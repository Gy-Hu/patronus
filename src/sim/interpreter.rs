// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::exec;
use super::exec::Word;
use crate::ir::*;
use crate::sim::exec::split_borrow_1;

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

    fn get(&mut self, expr: ExprRef) -> Option<u64>;

    fn step_count(&self) -> u64;
}

/// Interpreter based simulator for a transition system.
pub struct Interpreter {
    instructions: Vec<Option<Instr>>,
    states: Vec<State>,
    data: Vec<Word>,
    step_count: u64,
}

impl Interpreter {
    pub fn new(ctx: &Context, sys: &TransitionSystem) -> Self {
        let (meta, data_len) = compile(ctx, sys);
        let data = vec![0; data_len];
        let states = sys.states().cloned().collect::<Vec<_>>();
        Self {
            instructions: meta,
            data,
            states,
            step_count: 0,
        }
    }
}

/// Converts a transitions system into instructions and the number of Words that need to be allocated
fn compile(ctx: &Context, sys: &TransitionSystem) -> (Vec<Option<Instr>>, usize) {
    let use_counts = count_expr_uses(ctx, sys);
    // used to track instruction result allocations
    let mut locs: Vec<Option<Loc>> = Vec::with_capacity(use_counts.len());
    let mut instructions = Vec::new();
    let mut word_count = 0u32;
    for (idx, count) in use_counts.iter().enumerate() {
        if *count == 0 {
            locs.push(None); // no space needed
            instructions.push(None); // TODO: we would like to store the instructions compacted
        } else {
            let expr = ExprRef::from_index(idx);
            let tpe = expr.get_type(ctx);
            let (loc, width) = allocate_result_space(tpe, &mut word_count);
            locs.push(Some(loc));
            let instr = compile_expr(ctx, sys, expr, loc, &locs, width);
            instructions.push(Some(instr));
        }
    }
    (instructions, word_count as usize)
}

fn allocate_result_space(tpe: Type, word_count: &mut u32) -> (Loc, WidthInt) {
    match tpe.get_bit_vector_width() {
        None => todo!("array support"),
        Some(width) => {
            let words = width.div_ceil(Word::BITS as WidthInt) as u16;
            let offset = *word_count;
            *word_count += words as u32;
            let loc = Loc { offset, words };
            (loc, width)
        }
    }
}

fn compile_expr(
    ctx: &Context,
    sys: &TransitionSystem,
    expr_ref: ExprRef,
    dst: Loc,
    locs: &[Option<Loc>],
    result_width: WidthInt,
) -> Instr {
    let expr = ctx.get(expr_ref);
    let kind = sys
        .get_signal(expr_ref)
        .map(|s| s.kind.clone())
        .unwrap_or(SignalKind::Node);
    let tpe = compile_expr_type(expr, locs, ctx);
    Instr {
        dst,
        tpe,
        kind,
        result_width,
    }
}

fn compile_expr_type(expr: &Expr, locs: &[Option<Loc>], ctx: &Context) -> InstrType {
    match expr {
        Expr::BVSymbol { .. } => InstrType::Nullary(NullaryOp::BVSymbol),
        Expr::BVLiteral { value, width } => {
            InstrType::Nullary(NullaryOp::BVLiteral(*value, *width))
        }
        Expr::BVZeroExt { .. } => todo!("compile zext"),
        Expr::BVSignExt { .. } => todo!("compile sext"),
        Expr::BVSlice { e, hi, lo } => {
            InstrType::Unary(UnaryOp::BVSlice(*hi, *lo), locs[e.index()].unwrap())
        }
        Expr::BVNot(e, _) => InstrType::Unary(UnaryOp::BVNot, locs[e.index()].unwrap()),
        Expr::BVNegate(_, _) => todo!(),
        Expr::BVEqual(a, b) => InstrType::Binary(
            BinaryOp::BVEqual,
            locs[a.index()].unwrap(),
            locs[b.index()].unwrap(),
        ),
        Expr::BVImplies(_, _) => todo!(),
        Expr::BVGreater(_, _) => todo!(),
        Expr::BVGreaterSigned(_, _) => todo!(),
        Expr::BVGreaterEqual(_, _) => todo!(),
        Expr::BVGreaterEqualSigned(_, _) => todo!(),
        Expr::BVConcat(a, b, _) => InstrType::Binary(
            BinaryOp::BVConcat(b.get_bv_type(ctx).unwrap()), // LSB width
            locs[a.index()].unwrap(),
            locs[b.index()].unwrap(),
        ),
        Expr::BVAnd(_, _, _) => todo!(),
        Expr::BVOr(_, _, _) => todo!(),
        Expr::BVXor(_, _, _) => todo!(),
        Expr::BVShiftLeft(_, _, _) => todo!(),
        Expr::BVArithmeticShiftRight(_, _, _) => todo!(),
        Expr::BVShiftRight(_, _, _) => todo!(),
        Expr::BVAdd(_, _, _) => todo!(),
        Expr::BVMul(_, _, _) => todo!(),
        Expr::BVSignedDiv(_, _, _) => todo!(),
        Expr::BVUnsignedDiv(_, _, _) => todo!(),
        Expr::BVSignedMod(_, _, _) => todo!(),
        Expr::BVSignedRem(_, _, _) => todo!(),
        Expr::BVUnsignedRem(_, _, _) => todo!(),
        Expr::BVSub(_, _, _) => todo!(),
        Expr::BVArrayRead { .. } => todo!(),
        Expr::BVIte { cond, tru, fals } => InstrType::Tertiary(
            TertiaryOp::BVIte,
            locs[cond.index()].unwrap(),
            locs[tru.index()].unwrap(),
            locs[fals.index()].unwrap(),
        ),
        Expr::ArraySymbol { .. } => todo!(),
        Expr::ArrayConstant { .. } => todo!(),
        Expr::ArrayEqual(_, _) => todo!(),
        Expr::ArrayStore { .. } => todo!(),
        Expr::ArrayIte { .. } => todo!(),
    }
}

impl Simulator for Interpreter {
    fn init(&mut self, kind: InitKind) {
        // assign default value to all inputs and states
        for inst in self.instructions.iter().flatten() {
            if matches!(inst.kind, SignalKind::Input | SignalKind::State) {
                exec::clear(&mut self.data[inst.dst.range()]);
            }
        }

        // update signals since signal init values might need to be computed
        // TODO: more efficient would be to only update expressions that are needed for init
        self.update_all_signals();

        // assign init expressions to signals
        for state in self.states.iter() {
            if let Some(init) = state.init {
                let dst_range = self.instructions[state.symbol.index()]
                    .as_ref()
                    .unwrap()
                    .dst
                    .range();
                let src_range = self.instructions[init.index()]
                    .as_ref()
                    .unwrap()
                    .dst
                    .range();
                let (dst, src) = split_borrow_1(&mut self.data, dst_range, src_range);
                exec::assign(dst, src);
            }
        }
    }

    fn update(&mut self) {
        self.update_all_signals();
    }

    fn step(&mut self) {
        // assign next expressions to state
        for state in self.states.iter() {
            if let Some(next) = state.next {
                let dst_range = self.instructions[state.symbol.index()]
                    .as_ref()
                    .unwrap()
                    .dst
                    .range();
                let src_range = self.instructions[next.index()]
                    .as_ref()
                    .unwrap()
                    .dst
                    .range();
                let (dst, src) = split_borrow_1(&mut self.data, dst_range, src_range);
                exec::assign(dst, src);
            }
        }
        self.step_count += 1;
    }

    fn set(&mut self, expr: ExprRef, value: u64) {
        if let Some(m) = &self.instructions[expr.index()] {
            let data = &mut self.data[m.dst.range()];
            data[0] = value;
            for other in data.iter_mut().skip(1) {
                *other = 0;
            }
            // println!("Set [{}] = {}", expr.index(), data[0]);
        }
    }

    fn get(&mut self, expr: ExprRef) -> Option<u64> {
        if let Some(m) = &self.instructions[expr.index()] {
            let data = &self.data[m.dst.range()];
            let mask = (1u64 << m.result_width) - 1;
            let res = data[0] & mask;
            for other in data.iter().skip(1) {
                assert_eq!(*other, 0, "missing MSB!");
            }
            Some(res)
        } else {
            None
        }
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }
}

impl Interpreter {
    /// Eagerly re-computes all signals in the system.
    fn update_all_signals(&mut self) {
        for instr in self.instructions.iter().flatten() {
            exec_instr(instr, &mut self.data);
        }
    }
}

#[derive(Debug, Clone)]
struct Instr {
    dst: Loc,
    tpe: InstrType,
    kind: SignalKind,       // TODO: move to symbol meta-data or similar structure
    result_width: WidthInt, // TODO: move to symbol meta-data
}

#[derive(Debug, Clone)]
enum InstrType {
    Nullary(NullaryOp),
    Unary(UnaryOp, Loc),
    Binary(BinaryOp, Loc, Loc),
    Tertiary(TertiaryOp, Loc, Loc, Loc),
}

#[derive(Debug, Clone)]
enum NullaryOp {
    BVSymbol,
    BVLiteral(BVLiteralInt, WidthInt),
}

#[derive(Debug, Clone)]
enum UnaryOp {
    BVSlice(WidthInt, WidthInt),
    BVNot,
}

#[derive(Debug, Clone)]
enum BinaryOp {
    BVEqual,
    BVConcat(WidthInt), // width of the lsb
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
}

fn exec_instr(instr: &Instr, data: &mut [Word]) {
    match &instr.tpe {
        InstrType::Nullary(tpe) => {
            match tpe {
                NullaryOp::BVSymbol => {}
                NullaryOp::BVLiteral(value, width) => {
                    // TODO: optimize by only calculating once!
                    assert!(*width <= BVLiteralInt::BITS);
                    data[instr.dst.range()][0] = *value;
                }
            }
        }
        InstrType::Unary(tpe, a_loc) => {
            let (dst, a) = exec::split_borrow_1(data, instr.dst.range(), a_loc.range());
            match tpe {
                UnaryOp::BVSlice(hi, lo) => {
                    if dst.len() == 1 {
                        dst[0] = exec::slice_to_word(a, *hi, *lo);
                    } else {
                        todo!("implement slice with a larger target")
                    }
                }
                UnaryOp::BVNot => exec::not(dst, a),
            }
        }
        InstrType::Binary(tpe, a_loc, b_loc) => {
            let (dst, a, b) =
                exec::split_borrow_2(data, instr.dst.range(), a_loc.range(), b_loc.range());
            match tpe {
                BinaryOp::BVEqual => {
                    dst[0] = exec::cmp_equal(a, b);
                }
                BinaryOp::BVConcat(lsb_width) => exec::concat(dst, a, b, *lsb_width),
            }
        }
        InstrType::Tertiary(tpe, a_loc, b_loc, c_loc) => {
            match tpe {
                TertiaryOp::BVIte => {
                    // we take advantage of the fact that the condition is always a bool
                    let cond_value = data[a_loc.range()][0] != 0;
                    if cond_value {
                        let (dst, src) =
                            exec::split_borrow_1(data, instr.dst.range(), b_loc.range());
                        exec::assign(dst, src);
                    } else {
                        let (dst, src) =
                            exec::split_borrow_1(data, instr.dst.range(), c_loc.range());
                        exec::assign(dst, src);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        // 16-bytes for the expression + 8 bytes for storage details
        assert_eq!(
            std::mem::size_of::<OldInstruction>(),
            std::mem::size_of::<Expr>() + 8 + 8 // debugging data
        );
    }
}
