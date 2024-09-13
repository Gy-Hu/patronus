// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::expr::*;
use crate::ir::TypeCheck;
use std::fmt::{Debug, Formatter};
use std::num::NonZeroU32;

// TODO: go back to 16-bit if we can change the interner to give us monotonically increasing IDs
type StringSymbolType = string_interner::symbol::SymbolU32;

type PatronStringInterner =
    string_interner::StringInterner<string_interner::DefaultBackend<StringSymbolType>>;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct StringRef(StringSymbolType);
#[derive(PartialEq, Eq, Clone, Copy, Hash, Ord, PartialOrd)]
pub struct ExprRef(NonZeroU32);

impl Debug for ExprRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // we need a custom implementation in order to show the zero based index
        write!(f, "ExprRef({})", self.index())
    }
}

impl ExprRef {
    // TODO: reduce visibility to pub(crate)
    pub fn from_index(index: usize) -> Self {
        ExprRef(NonZeroU32::new((index + 1) as u32).unwrap())
    }

    pub(crate) fn index(&self) -> usize {
        (self.0.get() - 1) as usize
    }
}

/// Context which is used to create all SMT expressions. Expressions are interned such that
/// reference equivalence implies structural equivalence.
#[derive(Clone)]
pub struct Context {
    strings: PatronStringInterner,
    exprs: indexmap::IndexSet<Expr>,
}

impl Default for Context {
    fn default() -> Self {
        Context {
            strings: PatronStringInterner::new(),
            exprs: indexmap::IndexSet::default(),
        }
    }
}

impl Context {
    /// ensures that the value is unique (by appending a number if necessary) and then adds it to the store
    /// TODO: move this functionality to the parser, since it is only really good to use when we
    ///       have a fresh context. Otherwise, we might encounter "false" conflicts, leading to
    ///       unstable names.
    pub(crate) fn add_unique_str(&mut self, value: &str) -> StringRef {
        let mut name: String = value.to_string();
        let mut count: usize = 0;
        while self.is_interned(&name) {
            name = format!("{value}_{count}");
            count += 1;
        }
        self.string(name.into())
    }

    fn is_interned(&self, value: &str) -> bool {
        self.strings.get(value).is_some()
    }
}

/// Adding and removing nodes.
impl Context {
    pub fn get(&self, reference: ExprRef) -> &Expr {
        self.exprs
            .get_index((reference.0.get() as usize) - 1)
            .expect("Invalid ExprRef!")
    }

    pub(crate) fn add_expr(&mut self, value: Expr) -> ExprRef {
        let (index, _) = self.exprs.insert_full(value);
        ExprRef::from_index(index)
    }

    pub(crate) fn get_str(&self, reference: StringRef) -> &str {
        self.strings
            .resolve(reference.0)
            .expect("Invalid StringRef!")
    }

    pub(crate) fn string(&mut self, value: std::borrow::Cow<str>) -> StringRef {
        StringRef(self.strings.get_or_intern(value))
    }
}

/// Convenience methods to construct IR nodes.
impl Context {
    // helper functions to construct expressions
    pub fn bv_symbol(&mut self, name: &str, width: WidthInt) -> ExprRef {
        assert!(width > 0, "0-bit bitvectors are not allowed");
        let name_ref = self.string(name.into());
        self.add_expr(Expr::BVSymbol {
            name: name_ref,
            width,
        })
    }
    pub fn symbol(&mut self, name: StringRef, tpe: Type) -> ExprRef {
        assert_ne!(tpe, Type::BV(0), "0-bit bitvectors are not allowed");
        self.add_expr(Expr::symbol(name, tpe))
    }
    pub fn bv_lit(&mut self, value: BVLiteralInt, width: WidthInt) -> ExprRef {
        assert!(bv_value_fits_width(value, width));
        assert!(width > 0, "0-bit bitvectors are not allowed");
        self.add_expr(Expr::BVLiteral { value, width })
    }
    pub fn zero(&mut self, width: WidthInt) -> ExprRef {
        self.bv_lit(0, width)
    }

    pub fn zero_array(&mut self, tpe: ArrayType) -> ExprRef {
        let data = self.bv_lit(0, tpe.data_width);
        self.array_const(data, tpe.index_width)
    }

    pub fn mask(&mut self, width: WidthInt) -> ExprRef {
        let value = ((1 as BVLiteralInt) << width) - 1;
        self.bv_lit(value, width)
    }
    pub fn one(&mut self, width: WidthInt) -> ExprRef {
        self.bv_lit(1, width)
    }
    pub fn bv_equal(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVEqual(a, b))
    }
    pub fn bv_ite(&mut self, cond: ExprRef, tru: ExprRef, fals: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVIte { cond, tru, fals })
    }
    pub fn array_ite(&mut self, cond: ExprRef, tru: ExprRef, fals: ExprRef) -> ExprRef {
        self.add_expr(Expr::ArrayIte { cond, tru, fals })
    }
    pub fn implies(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVImplies(a, b))
    }
    pub fn greater_signed(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVGreaterSigned(a, b, b.get_bv_type(self).unwrap()))
    }

    pub fn greater(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVGreater(a, b))
    }
    pub fn greater_or_equal_signed(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVGreaterEqualSigned(
            a,
            b,
            b.get_bv_type(self).unwrap(),
        ))
    }

    pub fn greater_or_equal(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVGreaterEqual(a, b))
    }
    pub fn not(&mut self, e: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVNot(e, e.get_bv_type(self).unwrap()))
    }
    pub fn negate(&mut self, e: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVNegate(e, e.get_bv_type(self).unwrap()))
    }
    pub fn and(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVAnd(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn or(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVOr(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn xor(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVXor(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn shift_left(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVShiftLeft(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn arithmetic_shift_right(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVArithmeticShiftRight(
            a,
            b,
            b.get_bv_type(self).unwrap(),
        ))
    }
    pub fn shift_right(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVShiftRight(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn add(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVAdd(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn sub(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVSub(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn mul(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVMul(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn div(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVUnsignedDiv(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn signed_div(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVSignedDiv(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn signed_mod(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVSignedMod(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn signed_remainder(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVSignedRem(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn remainder(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVUnsignedRem(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn concat(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        let width = a.get_bv_type(self).unwrap() + b.get_bv_type(self).unwrap();
        self.add_expr(Expr::BVConcat(a, b, width))
    }
    pub fn slice(&mut self, e: ExprRef, hi: WidthInt, lo: WidthInt) -> ExprRef {
        if lo == 0 && hi + 1 == e.get_bv_type(self).unwrap() {
            e
        } else {
            assert!(hi >= lo, "{hi} < {lo} ... not allowed!");
            self.add_expr(Expr::BVSlice { e, hi, lo })
        }
    }
    pub fn zero_extend(&mut self, e: ExprRef, by: WidthInt) -> ExprRef {
        if by == 0 {
            e
        } else {
            let width = e.get_bv_type(self).unwrap() + by;
            self.add_expr(Expr::BVZeroExt { e, by, width })
        }
    }
    pub fn sign_extend(&mut self, e: ExprRef, by: WidthInt) -> ExprRef {
        if by == 0 {
            e
        } else {
            let width = e.get_bv_type(self).unwrap() + by;
            self.add_expr(Expr::BVSignExt { e, by, width })
        }
    }

    pub fn array_store(&mut self, array: ExprRef, index: ExprRef, data: ExprRef) -> ExprRef {
        self.add_expr(Expr::ArrayStore { array, index, data })
    }

    pub fn array_const(&mut self, e: ExprRef, index_width: WidthInt) -> ExprRef {
        let data_width = e.get_bv_type(self).unwrap();
        self.add_expr(Expr::ArrayConstant {
            e,
            index_width,
            data_width,
        })
    }

    pub fn array_read(&mut self, array: ExprRef, index: ExprRef) -> ExprRef {
        let width = array.get_type(self).get_array_data_width().unwrap();
        self.add_expr(Expr::BVArrayRead {
            array,
            index,
            width,
        })
    }
}

pub fn bv_value_fits_width(value: BVLiteralInt, width: WidthInt) -> bool {
    let bits_required = BVLiteralInt::BITS - value.leading_zeros();
    width >= bits_required
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ir_type_size() {
        assert_eq!(std::mem::size_of::<StringRef>(), 4);
        assert_eq!(std::mem::size_of::<ExprRef>(), 4);
    }

    #[test]
    fn reference_ids() {
        let mut ctx = Context::default();
        let str_id0 = ctx.string("a".into());
        let id0 = ctx.add_expr(Expr::BVSymbol {
            name: str_id0,
            width: 1,
        });
        assert_eq!(id0.0.get(), 1, "ids start at one (for now)");
        let id0_b = ctx.add_expr(Expr::BVSymbol {
            name: str_id0,
            width: 1,
        });
        assert_eq!(id0.0, id0_b.0, "ids should be interned!");
        let id1 = ctx.add_expr(Expr::BVSymbol {
            name: str_id0,
            width: 2,
        });
        assert_eq!(id0.0.get() + 1, id1.0.get(), "ids should increment!");
    }
}