// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::exec;
use super::exec::Word;
use crate::ir::*;
use std::collections::{HashMap, HashSet};

/// Specifies how to initialize states that do not have
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum InitKind {
    Zero,
    Random,
}

pub trait Simulator {
    /// Load the initial state values.
    fn init(&mut self, kind: InitKind);

    /// Recalculate signals.
    fn update(&mut self);

    /// Advance the state.
    fn step(&mut self);

    /// Change the value or an expression in the simulator. Be careful!
    fn set(&mut self, expr: ExprRef, value: u64);

    fn get(&mut self, expr: ExprRef) -> Option<ValueRef<'_>>;

    fn step_count(&self) -> u64;
}

/// Interpreter based simulator for a transition system.
pub struct Interpreter<'a> {
    ctx: &'a Context,
    update: Program,
    init: Program,
    states: Vec<State>,
    inputs: Vec<ExprRef>,
    data: Vec<Word>,
    step_count: u64,
}

impl<'a> Interpreter<'a> {
    pub fn new(ctx: &'a Context, sys: &TransitionSystem) -> Self {
        let init = compile(ctx, sys, true);
        let update = compile(ctx, sys, false);
        let states = sys.states().cloned().collect::<Vec<_>>();
        let inputs = sys
            .get_signals(|s| s.kind == SignalKind::Input)
            .iter()
            .map(|(e, _)| *e)
            .collect::<Vec<_>>();
        let data = vec![0; update.mem_words as usize];
        Self {
            ctx,
            update,
            init,
            states,
            inputs,
            data,
            step_count: 0,
        }
    }
}

impl<'a> Simulator for Interpreter<'a> {
    fn init(&mut self, kind: InitKind) {
        // allocate memory to execute the init program
        let mut init_data = vec![0; self.init.mem_words as usize];

        // assign default value to all inputs
        for sym in self.inputs.iter() {
            let dst = self.init.get_range(sym).unwrap();
            exec::clear(&mut init_data[dst]);
        }

        // assign default value to all states
        for state in self.states.iter() {
            println!("{:?}", state.symbol.get_symbol_name(self.ctx));
            let dst = self.init.get_range(&state.symbol).unwrap();
            exec::clear(&mut init_data[dst]);
        }

        // execute the init program
        self.init.execute(&mut init_data);

        // copy init values from init to update program
        for state in self.states.iter() {
            // println!("{}", state.symbol.get_symbol_name(self.ctx).unwrap());
            let src = self.init.get_range(&state.symbol).unwrap();
            let dst = self.update.get_range(&state.symbol).unwrap();
            exec::assign(&mut self.data[dst], &init_data[src]);
        }
    }

    fn update(&mut self) {
        self.update.execute(&mut self.data);
    }

    fn step(&mut self) {
        // assign next expressions to state
        for state in self.states.iter() {
            if let Some(next) = state.next {
                let dst_range = self.update.get_range(&state.symbol).unwrap();
                let src_range = self.update.get_range(&next).unwrap();
                let (dst, src) = exec::split_borrow_1(&mut self.data, dst_range, src_range);
                exec::assign(dst, src);
            }
        }
        self.step_count += 1;
    }

    fn set(&mut self, expr: ExprRef, value: u64) {
        if let Some(m) = &self.update.symbols.get(&expr) {
            assert_eq!(m.elements, 1, "cannot set array values with this function");
            let dst = &mut self.data[m.loc.range()];
            exec::assign_word(dst, value);
            // println!("Set [{}] = {}", expr.index(), data[0]);
        }
    }

    fn get(&mut self, expr: ExprRef) -> Option<ValueRef<'_>> {
        // println!("{:?}", expr.get_symbol_name(self.ctx));
        if let Some(m) = &self.update.symbols.get(&expr) {
            assert_eq!(m.elements, 1, "cannot get array values with this function");
            let words = &self.data[m.loc.range()];
            let bits = m.width;
            Some(ValueRef { words, bits })
        } else {
            None
        }
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }
}

/// the result of a compilation
struct Program {
    instructions: Vec<Instr>,
    symbols: HashMap<ExprRef, SymbolInfo>,
    mem_words: u32,
}

struct SymbolInfo {
    loc: Loc,
    width: WidthInt,
    elements: u64,
}

impl Program {
    fn execute(&self, data: &mut [Word]) {
        for instr in self.instructions.iter() {
            exec_instr(instr, data);
        }
    }

    fn get_range(&self, e: &ExprRef) -> Option<std::ops::Range<usize>> {
        if let Some(info) = self.symbols.get(e) {
            let start = info.loc.offset as usize;
            let len = info.elements as usize * info.loc.words as usize;
            Some(start..(start + len))
        } else {
            None
        }
    }
}

/// Converts a transitions system into instructions and the number of Words that need to be allocated
/// * `init_mode` - Indicates whether we want to generate a program for the system init or the system update.
fn compile(ctx: &Context, sys: &TransitionSystem, init_mode: bool) -> Program {
    // we need to be able to indentiy expressions that represent states
    let expr_to_state: HashMap<ExprRef, &State> =
        HashMap::from_iter(sys.states().map(|s| (s.symbol, s)));

    // used to track instruction result allocations
    let mut locs: ExprMetaData<Option<(Loc, WidthInt)>> = ExprMetaData::default();
    let mut symbols = HashMap::new();
    // generated instructions
    let mut instructions = Vec::new();
    // bump allocator
    let mut mem_words = 0u32;

    // keep track of which instructions need to be compiled next
    let mut todo = Vec::new();

    // we want to be able to identify these expression to add them to the `symbol` lookup
    let init_and_next_exprs = get_next_and_init_refs(sys);

    // define roots depending on mode
    if init_mode {
        // calculate the value for each state (which in init mode is the value of the init expression)
        for state in sys.states() {
            todo.push(state.symbol);
        }
        // allocate space for inputs
        for (signal_expr, _) in sys.get_signals(|s| matches!(s.kind, SignalKind::Input)) {
            todo.push(signal_expr);
        }
    } else {
        // calculate the next expression for each state
        for state in sys.states() {
            if let Some(next) = state.next {
                if next != state.symbol {
                    todo.push(next);
                }
            }
        }
        // calculate all other signals that might be observable
        for (signal_expr, _) in sys.get_signals(is_usage_root_signal) {
            todo.push(signal_expr);
        }
    }

    // compile until we are done
    while let Some(expr_ref) = todo.pop() {
        // check to see if this expression has already been compiled and can be skipped
        if locs.get(expr_ref).is_some() {
            continue;
        }

        // states get special handling in init mode
        let mut compile_expr_ref = expr_ref;
        if let Some(state) = expr_to_state.get(&expr_ref) {
            if init_mode {
                if let Some(init) = state.init {
                    // compute the init expression instead of the state
                    compile_expr_ref = init; // overwrite!
                }
            }
        }

        let is_bv_or_symbol =
            compile_expr_ref.is_symbol(ctx) || compile_expr_ref.get_type(ctx).is_bit_vector();
        if is_bv_or_symbol {
            let instr = compile_bv_or_symbol_expr(
                ctx,
                sys,
                expr_ref,
                compile_expr_ref,
                &mut todo,
                &mut locs,
                &init_and_next_exprs,
                &mut symbols,
                &mut mem_words,
            );
            if let Some(ii) = instr {
                instructions.push(ii);
            }
        } else {
            let instrs = compile_array_expr(
                ctx,
                expr_ref,
                compile_expr_ref,
                &mut todo,
                &mut locs,
                &mut mem_words,
            );
            if let Some(mut ii) = instrs {
                instructions.append(&mut ii);
            }
        }
    }

    Program {
        instructions,
        symbols,
        mem_words,
    }
}

fn compile_bv_or_symbol_expr(
    ctx: &Context,
    sys: &TransitionSystem,
    expr_ref: ExprRef,
    compile_expr_ref: ExprRef,
    todo: &mut Vec<ExprRef>,
    locs: &mut ExprMetaData<Option<(Loc, WidthInt)>>,
    init_and_next_exprs: &HashSet<ExprRef>,
    symbols: &mut HashMap<ExprRef, SymbolInfo>,
    mem_words: &mut u32,
) -> Option<Instr> {
    // check to see if all children are already compiled
    let expr = ctx.get(compile_expr_ref);
    let mut all_compiled = true;
    expr.for_each_child(|c| {
        if locs.get(*c).is_none() {
            if all_compiled {
                todo.push(expr_ref); // return expression to the todo list
            }
            all_compiled = false;
            // we need to compile the child first
            todo.push(*c);
        }
    });
    if !all_compiled {
        // something was missing, try again later
        return None;
    }

    // allocate space to store the expression result
    let (loc, width, index_width) = allocate_result_space(expr.get_type(ctx), mem_words);
    *locs.get_mut(expr_ref) = Some((loc, index_width));
    // if the expression is a symbol or a state expression or a usage root, we create a lookup
    let is_root = sys
        .get_signal(compile_expr_ref)
        .map(is_usage_root_signal)
        .unwrap_or(false);
    if expr.is_symbol() || init_and_next_exprs.contains(&compile_expr_ref) || is_root {
        // it is important to use `expr_ref` here!
        symbols.insert(
            expr_ref,
            SymbolInfo {
                loc,
                width,
                elements: 1u64 << index_width,
            },
        );
    }
    // compile expression
    let instr = compile_expr(ctx, sys, compile_expr_ref, loc, &locs, width);
    Some(instr)
}

fn compile_array_expr(
    ctx: &Context,
    expr_ref: ExprRef,
    compile_expr_ref: ExprRef,
    todo: &mut Vec<ExprRef>,
    locs: &mut ExprMetaData<Option<(Loc, WidthInt)>>,
    mem_words: &mut u32,
) -> Option<Vec<Instr>> {
    // check to see if all children are already compiled
    let mut all_compiled = true;
    for c in get_array_expr_children(ctx, compile_expr_ref) {
        if locs.get(c).is_none() {
            if all_compiled {
                todo.push(expr_ref); // return expression to the todo list
            }
            all_compiled = false;
            // we need to compile the child first
            todo.push(c);
        }
    }
    if !all_compiled {
        // something was missing, try again later
        return None;
    }

    // allocate space for the result array
    let (loc, width, index_width) = allocate_result_space(expr_ref.get_type(ctx), mem_words);
    *locs.get_mut(expr_ref) = Some((loc, index_width));

    // compile the complete array instruction _block_
    let mut instrs = Vec::new();
    compile_array_res_expr_type(
        ctx,
        compile_expr_ref,
        &loc,
        index_width,
        None,
        locs,
        &mut instrs,
    );
    Some(instrs)
}

fn compile_array_res_expr_type(
    ctx: &Context,
    expr_ref: ExprRef,
    dst: &Loc,
    index_width: WidthInt,
    store_cond: Option<&Loc>,
    locs: &ExprMetaData<Option<(Loc, WidthInt)>>,
    instructions: &mut Vec<Instr>,
) {
    let expr = ctx.get(expr_ref);
    match expr {
        Expr::ArrayConstant { e, data_width, index_width } => {
            todo!("compile array constant")
        }
        Expr::ArrayIte { cond, tru, fals } => {
            todo!("compile array ite")
        }
        Expr::ArrayStore { array, data, index } => {
            // first we need to compile all previous stores or copies
            compile_array_res_expr_type(ctx, *array, dst, index_width, store_cond, locs, instructions);
            // now we can execute our store
            let tpe = InstrType::ArrayStore(index_width, locs[index].unwrap().0, locs[data].unwrap().0);
            instructions.push(Instr::new(*dst, tpe, SignalKind::Node, 0));
        }
        Expr::ArraySymbol { index_width, .. } => {
            match locs.get(expr_ref) {
                None => panic!("Symbol `{}` should have been pre-allocated!", expr.get_symbol_name(ctx).unwrap()),
                Some((src, _)) => {
                    // we implement array copy as a bit vector copy by extending the locations
                    let tpe = InstrType::Unary(UnaryOp::Copy, src.array_loc(*index_width));
                    instructions.push(Instr::new(dst.array_loc(*index_width), tpe, SignalKind::Node, 0));
                },
            }
        }
        _ => panic!("Unexpected expression which probably should have been handled by the bv-result compilation! {:?}", expr),
    }
}

fn get_array_expr_children(ctx: &Context, expr: ExprRef) -> Vec<ExprRef> {
    let mut todo = vec![expr];
    let mut out = Vec::new();
    while let Some(expr_ref) = todo.pop() {
        let expr = ctx.get(expr_ref);
        match expr {
            Expr::ArrayConstant { e, .. } => {
                out.push(*e);
            }
            Expr::ArrayIte { cond, tru, fals } => {
                out.push(*cond);
                todo.push(*tru);
                todo.push(*fals);
            }
            Expr::ArrayStore { array, data, index } => {
                out.push(*data);
                out.push(*index);
                todo.push(*array);
            }
            Expr::ArraySymbol { .. } => {
                // while symbols are array expressions
                // they actually get treated like bv expressions.
                out.push(expr_ref);
            } // terminal
            _ => panic!("{expr:?} is not an array expression"),
        }
    }
    out
}

fn get_next_and_init_refs(sys: &TransitionSystem) -> HashSet<ExprRef> {
    let mut out: HashSet<ExprRef> = HashSet::new();
    for state in sys.states() {
        if let Some(init) = state.init {
            out.insert(init);
        }
        if let Some(next) = state.next {
            out.insert(next);
        }
    }
    out
}

fn allocate_result_space(tpe: Type, word_count: &mut u32) -> (Loc, WidthInt, WidthInt) {
    match tpe {
        Type::BV(width) => {
            let words = width.div_ceil(Word::BITS as WidthInt) as u16;
            let offset = *word_count;
            *word_count += words as u32;
            let loc = Loc { offset, words };
            (loc, width, 0)
        }
        Type::Array(ArrayType {
            index_width,
            data_width,
        }) => {
            let words = data_width.div_ceil(Word::BITS as WidthInt) as u16;
            let offset = *word_count;
            let entries = 1u32 << index_width;
            *word_count += words as u32 * entries;
            let loc = Loc { offset, words };
            (loc, data_width, index_width)
        }
    }
}

fn compile_expr(
    ctx: &Context,
    sys: &TransitionSystem,
    expr_ref: ExprRef,
    dst: Loc,
    locs: &ExprMetaData<Option<(Loc, WidthInt)>>,
    result_width: WidthInt,
) -> Instr {
    let expr = ctx.get(expr_ref);
    let kind = sys
        .get_signal(expr_ref)
        .map(|s| s.kind.clone())
        .unwrap_or(SignalKind::Node);
    let tpe = compile_bv_res_expr_type(expr, locs, ctx);
    Instr::new(dst, tpe, kind, result_width)
}

fn compile_bv_res_expr_type(
    expr: &Expr,
    locs: &ExprMetaData<Option<(Loc, WidthInt)>>,
    ctx: &Context,
) -> InstrType {
    match expr {
        Expr::BVSymbol { .. } => InstrType::Nullary(NullaryOp::BVSymbol),
        Expr::BVLiteral { value, .. } => InstrType::Nullary(NullaryOp::BVLiteral(*value)),
        Expr::BVZeroExt { e, .. } => InstrType::Unary(UnaryOp::ZeroExt, locs[e].unwrap().0),
        Expr::BVSignExt { .. } => todo!("compile sext"),
        Expr::BVSlice { e, hi, lo } => {
            InstrType::Unary(UnaryOp::Slice(*hi, *lo), locs[e].unwrap().0)
        }
        Expr::BVNot(e, width) => InstrType::Unary(UnaryOp::Not(*width), locs[e].unwrap().0),
        Expr::BVNegate(_, _) => todo!(),
        Expr::BVEqual(a, b) => {
            InstrType::Binary(BinaryOp::BVEqual, locs[a].unwrap().0, locs[b].unwrap().0)
        }
        Expr::BVImplies(_, _) => todo!(),
        Expr::BVGreater(a, b) => {
            InstrType::Binary(BinaryOp::Greater, locs[a].unwrap().0, locs[b].unwrap().0)
        }
        Expr::BVGreaterSigned(_, _) => todo!(),
        Expr::BVGreaterEqual(a, b) => InstrType::Binary(
            BinaryOp::GreaterEqual,
            locs[a].unwrap().0,
            locs[b].unwrap().0,
        ),
        Expr::BVGreaterEqualSigned(_, _) => todo!(),
        Expr::BVConcat(a, b, _) => InstrType::Binary(
            BinaryOp::Concat(b.get_bv_type(ctx).unwrap()), // LSB width
            locs[a].unwrap().0,
            locs[b].unwrap().0,
        ),
        Expr::BVAnd(a, b, _) => {
            InstrType::Binary(BinaryOp::And, locs[a].unwrap().0, locs[b].unwrap().0)
        }
        Expr::BVOr(a, b, _) => {
            InstrType::Binary(BinaryOp::Or, locs[a].unwrap().0, locs[b].unwrap().0)
        }
        Expr::BVXor(a, b, _) => {
            InstrType::Binary(BinaryOp::Xor, locs[a].unwrap().0, locs[b].unwrap().0)
        }
        Expr::BVShiftLeft(_, _, _) => todo!(),
        Expr::BVArithmeticShiftRight(_, _, _) => todo!(),
        Expr::BVShiftRight(_, _, _) => todo!(),
        Expr::BVAdd(a, b, width) => InstrType::Binary(
            BinaryOp::Add(*width),
            locs[a].unwrap().0,
            locs[b].unwrap().0,
        ),
        Expr::BVMul(_, _, _) => todo!(),
        Expr::BVSignedDiv(_, _, _) => todo!(),
        Expr::BVUnsignedDiv(_, _, _) => todo!(),
        Expr::BVSignedMod(_, _, _) => todo!(),
        Expr::BVSignedRem(_, _, _) => todo!(),
        Expr::BVUnsignedRem(_, _, _) => todo!(),
        Expr::BVSub(a, b, width) => InstrType::Binary(
            BinaryOp::Sub(*width),
            locs[a].unwrap().0,
            locs[b].unwrap().0,
        ),
        Expr::BVArrayRead { array, index, .. } => {
            let (array_loc, index_width) = locs[array].unwrap();
            assert!(index_width <= Word::BITS, "array too large!");
            InstrType::ArrayRead(array_loc, index_width, locs[index].unwrap().0)
        }
        Expr::BVIte { cond, tru, fals } => InstrType::Tertiary(
            TertiaryOp::BVIte,
            locs[cond].unwrap().0,
            locs[tru].unwrap().0,
            locs[fals].unwrap().0,
        ),
        Expr::ArraySymbol { index_width, .. } => {
            InstrType::Nullary(NullaryOp::ArraySymbol(*index_width))
        }
        Expr::ArrayConstant { .. } => {
            panic!("Array constants should have been handled by a different compilation routine!")
        }
        Expr::ArrayEqual(_, _) => todo!("implement array equality comparison"),
        Expr::ArrayStore { .. } => {
            panic!("Array stores should have been handled by a different compilation routine!")
        }
        Expr::ArrayIte { .. } => {
            panic!("Array ites should have been handled by a different compilation routine!")
        }
    }
}

/// Contains a pointer to a value.
pub struct ValueRef<'a> {
    bits: WidthInt,
    words: &'a [Word],
}

impl<'a> ValueRef<'a> {
    pub fn to_u64(&self) -> Option<u64> {
        match self.words.len() {
            0 => Some(0),
            1 => Some(self.words[0] & exec::mask(self.bits)),
            _ => {
                // check to see if all msbs are zero
                for word in self.words.iter().skip(1) {
                    if *word != 0 {
                        return None;
                    }
                }
                Some(self.words[0])
            }
        }
    }

    pub fn to_bit_string(&self) -> String {
        exec::to_bit_str(self.words, self.bits)
    }

    pub fn to_big_uint(&self) -> num_bigint::BigUint {
        exec::to_big_uint(self.words)
    }
}

#[derive(Debug, Clone)]
struct Instr {
    dst: Loc,
    tpe: InstrType,
    kind: SignalKind,       // TODO: move to symbol meta-data or similar structure
    result_width: WidthInt, // TODO: move to symbol meta-data
    do_trace: bool,         // for debugging
}

impl Instr {
    fn new(dst: Loc, tpe: InstrType, kind: SignalKind, result_width: WidthInt) -> Self {
        Self {
            dst,
            tpe,
            kind,
            result_width,
            do_trace: false,
        }
    }

    /// Computes the data range while taking the number of array elements into account
    fn range(&self) -> std::ops::Range<usize> {
        match self.tpe {
            InstrType::Nullary(NullaryOp::ArraySymbol(index_width)) => {
                self.dst.array_range(index_width)
            }
            _ => self.dst.range(),
        }
    }
}

#[derive(Debug, Clone)]
enum InstrType {
    Nullary(NullaryOp),
    Unary(UnaryOp, Loc),
    Binary(BinaryOp, Loc, Loc),
    Tertiary(TertiaryOp, Loc, Loc, Loc),
    ArrayRead(Loc, WidthInt, Loc), // array loc + array index width + index loc
    ArrayStore(WidthInt, Loc, Loc), // array index width + index loc + data loc
}

#[derive(Debug, Clone)]
enum NullaryOp {
    BVSymbol,
    ArraySymbol(WidthInt), // index width
    BVLiteral(BVLiteralInt),
}

#[derive(Debug, Clone)]
enum UnaryOp {
    Slice(WidthInt, WidthInt),
    ZeroExt,
    Not(WidthInt),
    Copy,
}

#[derive(Debug, Clone)]
enum BinaryOp {
    BVEqual,
    Greater,
    GreaterEqual,
    Concat(WidthInt), // width of the lsb
    Or,
    And,
    Xor,
    Add(WidthInt),
    Sub(WidthInt),
}

#[derive(Debug, Clone)]
enum TertiaryOp {
    BVIte,
}

#[derive(Debug, Clone, Copy)]
struct Loc {
    /// Start of the value in the data array.
    offset: u32,
    /// Number of words.
    words: u16,
}

impl Loc {
    fn range(&self) -> std::ops::Range<usize> {
        let start = self.offset as usize;
        let end = start + self.words as usize;
        start..end
    }

    fn array_range(&self, index_width: WidthInt) -> std::ops::Range<usize> {
        let num_elements = 1usize << index_width;
        let start = self.offset as usize;
        let len = num_elements * self.words as usize;
        start..(start + len)
    }

    fn array_loc(&self, index_width: WidthInt) -> Self {
        let num_elements = 1u16 << index_width;
        Self {
            offset: self.offset,
            words: self.words * num_elements,
        }
    }
}

fn exec_instr(instr: &Instr, data: &mut [Word]) {
    match &instr.tpe {
        InstrType::Nullary(tpe) => {
            match tpe {
                NullaryOp::BVSymbol => {}
                NullaryOp::ArraySymbol(_) => {}
                NullaryOp::BVLiteral(value) => {
                    // TODO: optimize by only calculating once!
                    let dst = &mut data[instr.dst.range()];
                    exec::assign_word(dst, *value);
                    if instr.do_trace {
                        println!(
                            "{} <= {tpe:?} = ",
                            exec::to_bit_str(dst, instr.result_width)
                        );
                    }
                }
            }
        }
        InstrType::Unary(tpe, a_loc) => {
            let (dst, a) = exec::split_borrow_1(data, instr.dst.range(), a_loc.range());
            match tpe {
                UnaryOp::Slice(hi, lo) => exec::slice(dst, a, *hi, *lo),
                UnaryOp::Not(width) => exec::not(dst, a, *width),
                UnaryOp::ZeroExt => exec::zero_extend(dst, a),
                UnaryOp::Copy => exec::assign(dst, a),
            }
            if instr.do_trace {
                println!(
                    "{} <= {tpe:?} = {}",
                    exec::to_bit_str(dst, instr.result_width),
                    exec::to_bit_str(a, a.len() as WidthInt * Word::BITS)
                );
            }
        }
        InstrType::Binary(tpe, a_loc, b_loc) => {
            let (dst, a, b) =
                exec::split_borrow_2(data, instr.dst.range(), a_loc.range(), b_loc.range());
            if instr.do_trace {
                println!("Old dst: {}", exec::to_bit_str(dst, instr.result_width));
            }
            match tpe {
                BinaryOp::BVEqual => dst[0] = exec::bool_to_word(exec::cmp_equal(a, b)),
                BinaryOp::Greater => dst[0] = exec::bool_to_word(exec::cmp_greater(a, b)),
                BinaryOp::GreaterEqual => {
                    dst[0] = exec::bool_to_word(exec::cmp_greater_equal(a, b))
                }
                BinaryOp::Concat(lsb_width) => exec::concat(dst, a, b, *lsb_width),
                BinaryOp::Or => exec::or(dst, a, b),
                BinaryOp::And => exec::and(dst, a, b),
                BinaryOp::Xor => exec::xor(dst, a, b),
                BinaryOp::Add(width) => exec::add(dst, a, b, *width),
                BinaryOp::Sub(width) => exec::sub(dst, a, b, *width),
            }
            if instr.do_trace {
                println!(
                    "{} <= {tpe:?} = {}, {}",
                    exec::to_bit_str(dst, instr.result_width),
                    exec::to_bit_str(a, a.len() as WidthInt * Word::BITS),
                    exec::to_bit_str(b, b.len() as WidthInt * Word::BITS)
                );
            }
        }
        InstrType::Tertiary(tpe, a_loc, b_loc, c_loc) => match tpe {
            TertiaryOp::BVIte => {
                let cond_value = exec::read_bool(&data[a_loc.range()]);
                if cond_value {
                    let (dst, src) = exec::split_borrow_1(data, instr.dst.range(), b_loc.range());
                    exec::assign(dst, src);
                } else {
                    let (dst, src) = exec::split_borrow_1(data, instr.dst.range(), c_loc.range());
                    exec::assign(dst, src);
                }
            }
        },
        InstrType::ArrayRead(array, index_width, index) => {
            let index_value = data[index.range()][0] & exec::mask(*index_width);
            let src_start = array.offset as usize + array.words as usize * index_value as usize;
            let src_range = src_start..(src_start + array.words as usize);
            let (dst, src) = exec::split_borrow_1(data, instr.dst.range(), src_range);
            exec::assign(dst, src);
        }
        InstrType::ArrayStore(index_width, index, data_loc) => {
            let index_value = data[index.range()][0] & exec::mask(*index_width);
            let dst_start =
                instr.dst.offset as usize + instr.dst.words as usize * index_value as usize;
            let dst_range = dst_start..(dst_start + instr.dst.words as usize);
            let (dst, src) = exec::split_borrow_1(data, dst_range, data_loc.range());
            exec::assign(dst, src);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        // 4 bytes for offset, 2 bytes for number of words
        assert_eq!(std::mem::size_of::<Loc>(), 8);

        // contains value and width for literals
        assert_eq!(std::mem::size_of::<NullaryOp>(), 16);

        // contains a width for concatenation
        assert_eq!(std::mem::size_of::<BinaryOp>(), 8);

        // currently there is only one option
        assert_eq!(std::mem::size_of::<TertiaryOp>(), 0);

        // instruction type is twice as large as the expr because it includes all storage details
        assert_eq!(std::mem::size_of::<InstrType>(), 32);

        // 16-bytes for the instruction type + 16 bytes for storage details and other meta info
        assert_eq!(
            std::mem::size_of::<Instr>(),
            std::mem::size_of::<InstrType>() + 16
        );
    }
}
