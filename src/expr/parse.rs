// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{Context, ExprRef, TypeCheck, WidthInt};
use baa::BitVecValue;
use regex::{Captures, Match, Regex, RegexSet};
use std::collections::HashMap;

pub fn parse_expr(ctx: &mut Context, inp: &str) -> ExprRef {
    let mut parser = Parser::new(ctx, inp);
    let expr = parser.parse_expr_all();
    expr.type_check(ctx)
        .unwrap_or_else(|_| panic!("{inp} failed to type-check"));
    expr
}

struct Parser<'a> {
    ctx: &'a mut Context,
    inp: &'a str,
    symbols: HashMap<String, ExprRef>,
}

#[derive(Debug, Copy, Clone)]
enum Arg {
    E(ExprRef),
    C(WidthInt),
}

#[derive(Debug, Copy, Clone)]
enum ArgTpe {
    E,
    C,
}

impl<'a> Parser<'a> {
    fn new(ctx: &'a mut Context, inp: &'a str) -> Self {
        let inp = inp.trim();
        let symbols = HashMap::new();
        Self { ctx, inp, symbols }
    }

    fn parse_expr_all(&mut self) -> ExprRef {
        let e = self.parse_expr();
        assert!(self.inp.is_empty(), "could not pars: {}", self.inp);
        e
    }

    fn parse_expr(&mut self) -> ExprRef {
        let mut e = self
            .try_parse_fun()
            .or_else(|| self.try_pars_bv_lit())
            .or_else(|| self.try_parse_symbol())
            .unwrap_or_else(|| panic!("failed to parse: {}", self.inp));

        while let Some(c) = slice_regex.captures(self.inp) {
            if let Some(bit) = c.get(2) {
                let bit = Self::width_int(bit);
                self.consume_c(&c);
                e = self.ctx.slice(e, bit, bit);
            } else if let (Some(msb), Some(lsb)) = (c.get(4), c.get(5)) {
                let msb = Self::width_int(msb);
                let lsb = Self::width_int(lsb);
                self.consume_c(&c);
                e = self.ctx.slice(e, msb, lsb);
            } else {
                unreachable!("unexpected slice! @ {}", self.inp)
            }
        }
        e
    }

    fn width_int(m: Match) -> WidthInt {
        m.as_str().parse().unwrap()
    }

    fn try_parse_fun(&mut self) -> Option<ExprRef> {
        let fun = any_function_regex.matches(self.inp);
        if let Some(fun_id) = fun.into_iter().next() {
            self.consume_r(&function_regex[fun_id]);
            let args = self.parse_args(fun_id);
            Some(self.make_fun(fun_id, args))
        } else {
            None
        }
    }

    fn try_pars_bv_lit(&mut self) -> Option<ExprRef> {
        if let Some(m) = bin_lit_regex.captures(self.inp) {
            let width: WidthInt = m.get(1).unwrap().as_str().parse().unwrap();
            let value_str = m.get(2).unwrap().as_str();
            let value = BitVecValue::from_str_radix(value_str, 2, width).unwrap();
            self.consume_c(&m);
            Some(self.ctx.bv_lit(&value))
        } else if let Some(m) = dec_lit_regex.captures(self.inp) {
            let width: WidthInt = m.get(1).unwrap().as_str().parse().unwrap();
            let value_str = m.get(2).unwrap().as_str();
            let value = BitVecValue::from_str_radix(value_str, 10, width).unwrap();
            self.consume_c(&m);
            Some(self.ctx.bv_lit(&value))
        } else if let Some(m) = hex_lit_regex.captures(self.inp) {
            let width: WidthInt = m.get(1).unwrap().as_str().parse().unwrap();
            let value_str = m.get(2).unwrap().as_str();
            let value = BitVecValue::from_str_radix(value_str, 16, width).unwrap();
            self.consume_c(&m);
            Some(self.ctx.bv_lit(&value))
        } else if let Some(c) = true_false_regex.captures(self.inp) {
            self.consume_c(&c);
            if c.get(2).is_some() {
                Some(self.ctx.tru())
            } else {
                debug_assert!(c.get(3).is_some());
                Some(self.ctx.fals())
            }
        } else {
            None
        }
    }

    fn try_parse_symbol(&mut self) -> Option<ExprRef> {
        if let Some(c) = symbol_regex.captures(self.inp) {
            let escaped_name = c.get(3).map(|m| {
                let len = m.as_str().len();
                &m.as_str()[1..len - 2]
            });
            let name = escaped_name.unwrap_or_else(|| c.get(1).map(|m| m.as_str()).unwrap());

            // do we have an explicit bv type?
            if let Some(width) = c.get(5) {
                let width: WidthInt = width.as_str().parse().unwrap();
                let new_sym = self.ctx.bv_symbol(name, width);
                // compare width
                if let Some(other) = self.symbols.get(name) {
                    let other_width = self.ctx.get(*other).get_bv_type(self.ctx).unwrap();
                    assert_eq!(
                        width, other_width,
                        "Two symbols with same name {name} have different widths!"
                    );
                } else {
                    // remember width
                    self.symbols.insert(name.to_string(), new_sym);
                }
                self.consume_c(&c);
                Some(new_sym)
            } else {
                let other = *self
                    .symbols
                    .get(name)
                    .unwrap_or_else(|| panic!("symbol of unknown type: `{name}` @ {}", self.inp));
                let width = self.ctx.get(other).get_bv_type(self.ctx).unwrap();
                self.consume_c(&c);
                Some(self.ctx.bv_symbol(name, width))
            }
        } else {
            None
        }
    }

    fn make_fun(&mut self, fun_id: usize, args: Vec<Arg>) -> ExprRef {
        match (fun_id, args.as_slice()) {
            (0, [Arg::E(e), Arg::C(by)]) => self.ctx.zero_extend(*e, *by),
            (1, [Arg::E(e), Arg::C(by)]) => self.ctx.sign_extend(*e, *by),
            (2, [Arg::E(e)]) => self.ctx.not(*e),
            (3, [Arg::E(e)]) => self.ctx.negate(*e),
            (4, [Arg::E(a), Arg::E(b)]) => self.ctx.bv_equal(*a, *b),
            (5, [Arg::E(a), Arg::E(b)]) => self.ctx.implies(*a, *b),
            (6, [Arg::E(a), Arg::E(b)]) => self.ctx.greater(*a, *b),
            (7, [Arg::E(a), Arg::E(b)]) => self.ctx.greater_signed(*a, *b),
            (8, [Arg::E(a), Arg::E(b)]) => self.ctx.greater_or_equal(*a, *b),
            (9, [Arg::E(a), Arg::E(b)]) => self.ctx.greater_or_equal_signed(*a, *b),
            (10, [Arg::E(a), Arg::E(b)]) => self.ctx.concat(*a, *b),
            (11, [Arg::E(a), Arg::E(b)]) => self.ctx.and(*a, *b),
            (12, [Arg::E(a), Arg::E(b)]) => self.ctx.or(*a, *b),
            (13, [Arg::E(a), Arg::E(b)]) => self.ctx.xor(*a, *b),
            (14, [Arg::E(a), Arg::E(b)]) => self.ctx.shift_left(*a, *b),
            (15, [Arg::E(a), Arg::E(b)]) => self.ctx.arithmetic_shift_right(*a, *b),
            (16, [Arg::E(a), Arg::E(b)]) => self.ctx.shift_right(*a, *b),
            (17, [Arg::E(a), Arg::E(b)]) => self.ctx.add(*a, *b),
            (18, [Arg::E(a), Arg::E(b)]) => self.ctx.mul(*a, *b),
            (19, [Arg::E(a), Arg::E(b)]) => self.ctx.signed_div(*a, *b),
            (20, [Arg::E(a), Arg::E(b)]) => self.ctx.div(*a, *b),
            (21, [Arg::E(a), Arg::E(b)]) => self.ctx.signed_mod(*a, *b),
            (22, [Arg::E(a), Arg::E(b)]) => self.ctx.signed_remainder(*a, *b),
            (23, [Arg::E(a), Arg::E(b)]) => self.ctx.remainder(*a, *b),
            (24, [Arg::E(a), Arg::E(b)]) => self.ctx.sub(*a, *b),
            (25, [Arg::E(a), Arg::E(b), Arg::E(c)]) => self.ctx.bv_ite(*a, *b, *c),
            _ => todo!("implement: {}({:?})", functions[fun_id], args),
        }
    }

    fn parse_args(&mut self, fun_id: usize) -> Vec<Arg> {
        let mut args = vec![];
        let arg_types = function_args[fun_id];
        for (ii, at) in arg_types.iter().enumerate() {
            match at {
                ArgTpe::E => {
                    args.push(Arg::E(self.parse_expr()));
                }
                ArgTpe::C => {
                    args.push(Arg::C(self.try_parse_width_int().unwrap()));
                }
            }
            let is_last = ii + 1 == arg_types.len();
            if is_last {
                if let Some(m) = close_regex.find(self.inp) {
                    self.consume_m(&m);
                } else {
                    panic!(
                        "failed to find end of function {} @ {}",
                        functions[fun_id], self.inp
                    );
                }
            } else if let Some(m) = comma_regex.find(self.inp) {
                self.consume_m(&m);
            } else {
                panic!(
                    "failed to find end of argument in function {} @ {}",
                    functions[fun_id], self.inp
                );
            }
        }
        args
    }

    fn try_parse_width_int(&mut self) -> Option<WidthInt> {
        if let Some(m) = dec_num_regex.find(self.inp) {
            if let Ok(num) = m.as_str().parse() {
                self.consume_m(&m);
                return Some(num);
            }
        }
        None
    }

    fn consume_r(&mut self, reg: &Regex) {
        let m = reg.find(self.inp);
        if let Some(m) = m {
            self.consume_m(&m);
        }
    }

    fn consume_m(&mut self, m: &Match) {
        self.inp = &self.inp[m.end()..];
    }

    fn consume_c(&mut self, c: &Captures) {
        self.inp = &self.inp[c.get(0).unwrap().end()..];
    }
}

lazy_static! {
    static ref functions: [&'static str; 26] = [
        "zext",
        "sext",
        "not",
        "neg",
        "eq",
        "implies",
        "ugt",
        "sgt",
        "ugte",
        "sgte",
        "concat",
        "and",
        "or",
        "xor",
        "logical_shift_left",
        "arithmetic_shift_right",
        "logical_shift_right",
        "add",
        "mul",
        "sdiv",
        "udiv",
        "smod",
        "srem",
        "urem",
        "sub",
        "ite",
    ];
    static ref function_args: [&'static [ArgTpe]; 26] = [
        &[ArgTpe::E, ArgTpe::C],
        &[ArgTpe::E, ArgTpe::C],
        &[ArgTpe::E],
        &[ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E],
        &[ArgTpe::E, ArgTpe::E, ArgTpe::E],
    ];
    static ref function_regex: Vec<Regex> =
        functions.iter().map(|name| Regex::new(&format!("^{name}\\s*\\(\\s*")).unwrap()).collect();
    static ref any_function_regex: RegexSet =
        RegexSet::new(functions.iter().map(|name| format!("^{name}\\s*\\(\\s*"))).unwrap();
    static ref comma_regex: Regex = Regex::new(r"^,\s*").unwrap();
    static ref close_regex: Regex = Regex::new(r"^\)\s*").unwrap();
    static ref dec_num_regex: Regex = Regex::new(r"^[[:digit:]]+\s*").unwrap();
    static ref bin_lit_regex: Regex = Regex::new(r"^([[:digit:]]+)'b([01]+)\s*").unwrap();
    static ref dec_lit_regex: Regex = Regex::new(r"^([[:digit:]]+)'d([[:digit:]]+)\s*").unwrap();
    static ref hex_lit_regex: Regex = Regex::new(r"^([[:digit:]]+)'x([0-9a-fA-F]+)\s*").unwrap();
    static ref true_false_regex: Regex = Regex::new(r"^((true)|(false))\s*").unwrap();
    // escaped or not + optional type info
    static ref symbol_regex: Regex = Regex::new(r"^(([[:alpha:]][[:alnum:]]*)|(\|[^\|]*\|))\s*(:\s*bv<\s*([[:digit:]]+)\s*>\s*)?").unwrap();
    static ref slice_regex: Regex = Regex::new(r"^(\[\s*([[:digit:]]+)\s*\]\s*)|(\[\s*([[:digit:]]+)\s*:\s*([[:digit:]]+)\s*\]\s*)").unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_regexes() {
        assert!(true_false_regex.is_match("true"));
        assert!(true_false_regex.is_match("false"));
        assert!(true_false_regex.is_match("true  "));
        assert!(true_false_regex.is_match("false  "));
        assert!(!true_false_regex.is_match(" false"));
        assert!(true_false_regex.is_match("false  123"));

        assert!(symbol_regex.is_match("a"));
        assert!(symbol_regex.is_match("|a|"));
        assert!(symbol_regex.is_match("a : bv<10>"));
        assert!(symbol_regex.is_match("a : bv< 10>"));
        assert!(symbol_regex.is_match("a : bv<10 >"));
        assert!(symbol_regex.is_match("a: bv<10>"));
        assert!(symbol_regex.is_match("a :bv<10>"));
    }

    #[test]
    fn simple_parse() {
        let mut ctx = Context::default();
        assert_eq!(
            parse_expr(&mut ctx, "and(a : bv<1>, b : bv<1>)"),
            ctx.build(|c| c.and(c.bv_symbol("a", 1), c.bv_symbol("b", 1)))
        );

        assert_eq!(
            parse_expr(&mut ctx, "and(a : bv<2>, b : bv<2>)[1]"),
            ctx.build(|c| c.slice(c.and(c.bv_symbol("a", 2), c.bv_symbol("b", 2)), 1, 1))
        );

        assert_eq!(
            parse_expr(&mut ctx, "a : bv<10>[7:3]"),
            ctx.build(|c| c.slice(c.bv_symbol("a", 10), 7, 3))
        );

        assert_eq!(
            parse_expr(&mut ctx, "and(true, false)"),
            ctx.build(|c| c.and(c.tru(), c.fals()))
        );

        assert_eq!(
            parse_expr(&mut ctx, "ite(c : bv<1>, a: bv<10>, a)"),
            ctx.build(|c| c.bv_ite(
                c.bv_symbol("c", 1),
                c.bv_symbol("a", 10),
                c.bv_symbol("a", 10)
            )),
        );

        assert_eq!(
            parse_expr(&mut ctx, "and(a : bv<3>, 3'b111)"),
            ctx.build(|c| c.and(c.bv_symbol("a", 3), c.bit_vec_val(0b111, 3)))
        );
    }
}
