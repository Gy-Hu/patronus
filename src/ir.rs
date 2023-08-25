// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

/// This type restricts the maximum width that a bit-vector type is allowed to have in our IR.
pub type WidthInt = u32;

/// This restricts the maximum value that a bit-vector literal can carry.
pub type BVLiteralInt = u64;

/// Add and get items in a context
pub trait ContextAccess<D, I>
where
    I: Clone + Copy,
{
    /// Add a new value to the context obtaining a reference
    fn add(&mut self, val: D) -> I;
    /// Lookup the value by the reference obtained from a call to add
    fn get(&self, reference: I) -> &D;
}

/// IR Nodes are only valid with their context
pub trait Context: ContextAccess<String, StringRef> + ContextAccess<BVExpr, BVExprRef> {
    // helper functions to construct expressions
    fn bv_literal(&mut self, value: BVLiteralInt, width: WidthInt) -> BVExprRef {
        self.add(BVExpr::Literal { value, width })
    }
    fn bv_symbol(&mut self, name: &str, width: WidthInt) -> BVExprRef {
        let name_ref = self.add(name.to_string());
        self.add(BVExpr::Symbol {
            name: name_ref,
            width,
        })
    }
}

#[derive(Default)]
/// simple implementation of a context
struct BasicContext {
    strings: Vec<String>,
    bv_exprs: Vec<BVExpr>,
}

impl ContextAccess<String, StringRef> for BasicContext {
    fn add(&mut self, value: String) -> StringRef {
        let index = self.strings.len();
        self.strings.push(value);
        StringRef(index as u16)
    }

    fn get(&self, reference: StringRef) -> &String {
        &self.strings[reference.0 as usize]
    }
}

impl ContextAccess<BVExpr, BVExprRef> for BasicContext {
    fn add(&mut self, value: BVExpr) -> BVExprRef {
        let index = self.bv_exprs.len();
        self.bv_exprs.push(value);
        BVExprRef(index as u32)
    }

    fn get(&self, reference: BVExprRef) -> &BVExpr {
        &self.bv_exprs[reference.0 as usize]
    }
}

impl Context for BasicContext {}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct StringRef(u16);
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct BVExprRef(u32);
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct ArrayExprRef(u32);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum STMExpr {
    BitVec(BVExpr),
}

#[derive(Debug, PartialEq, Eq, Clone)]
/// Represents a SMT bit-vector expression.
pub enum BVExpr {
    // nullary
    Symbol {
        name: StringRef,
        width: WidthInt,
    },
    // TODO: support literals that do not fit into 64-bit
    Literal {
        value: BVLiteralInt,
        width: WidthInt,
    },
    // unary operations
    ZeroExt {
        e: BVExprRef,
        by: WidthInt,
    },
    SignExt {
        e: BVExprRef,
        by: WidthInt,
    },
    Slice {
        e: BVExprRef,
        hi: WidthInt,
        lo: WidthInt,
    },
    Not(BVExprRef),
    Negate(BVExprRef),
    ReduceOr(BVExprRef),
    ReduceAnd(BVExprRef),
    ReduceXor(BVExprRef),
    // binary operations
    Equal(BVExprRef, BVExprRef),
    Implies(BVExprRef, BVExprRef),
    Greater(BVExprRef, BVExprRef),
    GreaterSigned(BVExprRef, BVExprRef),
    GreaterEqual(BVExprRef, BVExprRef),
    GreaterEqualSigned(BVExprRef, BVExprRef),
    Concat(BVExprRef, BVExprRef),
    // binary arithmetic
    And(BVExprRef, BVExprRef),
    Or(BVExprRef, BVExprRef),
    Xor(BVExprRef, BVExprRef),
    ShiftLeft(BVExprRef, BVExprRef),
    ArithmeticShiftRight(BVExprRef, BVExprRef),
    ShiftRight(BVExprRef, BVExprRef),
    Add(BVExprRef, BVExprRef),
    Mul(BVExprRef, BVExprRef),
    SignedDiv(BVExprRef, BVExprRef),
    UnsignedDiv(BVExprRef, BVExprRef),
    SignedMod(BVExprRef, BVExprRef),
    SignedRem(BVExprRef, BVExprRef),
    UnsignedRem(BVExprRef, BVExprRef),
    Sub(BVExprRef, BVExprRef),
    //
    ArrayRead {
        array: ArrayExprRef,
        index: BVExprRef,
    },
    // ternary op
    Ite {
        cond: BVExprRef,
        tru: BVExprRef,
        fals: BVExprRef,
    },
}

#[derive(Debug, PartialEq, Eq, Clone)]
/// Represents a SMT array expression.
pub enum ArrayExpr {
    // nullary
    Symbol {
        name: StringRef,
        index_width: WidthInt,
        data_width: WidthInt,
    },
    // unary
    Constant {
        e: BVExprRef,
        index_width: WidthInt,
    },
    // binary
    Equal(ArrayExprRef, ArrayExprRef),
    // ternary
    Store {
        array: ArrayExprRef,
        index: BVExprRef,
        data: BVExprRef,
    },
    Ite {
        cond: BVExprRef,
        tru: ArrayExprRef,
        fals: ArrayExprRef,
    },
}

trait SerializableIrNode {
    fn serialize<C: Context>(
        &self,
        ctx: &C,
        writer: &mut impl (std::io::Write),
    ) -> std::io::Result<()>;
    fn serialize_to_str<C: Context>(&self, ctx: &C) -> String {
        let mut buf = Vec::new();
        self.serialize(ctx, &mut buf)
            .expect("Failed to write to string!");
        String::from_utf8(buf).expect("Failed to read string we wrote!")
    }
}

impl SerializableIrNode for BVExpr {
    fn serialize<C: Context>(
        &self,
        ctx: &C,
        writer: &mut impl (std::io::Write),
    ) -> std::io::Result<()> {
        match *self {
            BVExpr::Symbol { name, .. } => write!(writer, "{}", ctx.get(name)),
            BVExpr::Literal { value, width } => {
                if width <= 8 {
                    write!(writer, "{width}'b{value:b}")
                } else {
                    write!(writer, "{width}'x{value:x}")
                }
            }
            BVExpr::ZeroExt { e, by } => {
                write!(writer, "zext(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ", {by})")
            }
            BVExpr::SignExt { e, by } => {
                write!(writer, "sext(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ", {by})")
            }
            BVExpr::Slice { e, hi, lo } => {
                e.serialize(ctx, writer)?;
                if hi == lo {
                    write!(writer, "[{hi}]")
                } else {
                    write!(writer, "[{hi}:{lo}]")
                }
            }
            BVExpr::Not(e) => {
                write!(writer, "not(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::Negate(e) => {
                write!(writer, "neg(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::ReduceOr(e) => {
                write!(writer, "redor(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::ReduceAnd(e) => {
                write!(writer, "redand(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::ReduceXor(e) => {
                write!(writer, "redxor(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::Equal(a, b) => {
                write!(writer, "eq(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::Implies(a, b) => {
                write!(writer, "implies(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::Greater(a, b) => {
                write!(writer, "ugt(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::GreaterSigned(a, b) => {
                write!(writer, "sgt(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::GreaterEqual(a, b) => {
                write!(writer, "ugte(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::GreaterEqualSigned(a, b) => {
                write!(writer, "sgte(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::Concat(a, b) => {
                write!(writer, "concat(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::And(a, b) => {
                write!(writer, "and(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::Or(a, b) => {
                write!(writer, "or(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::Xor(a, b) => {
                write!(writer, "xor(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::ShiftLeft(a, b) => {
                write!(writer, "logical_shift_left(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::ArithmeticShiftRight(a, b) => {
                write!(writer, "arithmetic_shift_right(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::ShiftRight(a, b) => {
                write!(writer, "logical_shift_right(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::Add(a, b) => {
                write!(writer, "add(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::Mul(a, b) => {
                write!(writer, "mul(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::SignedDiv(a, b) => {
                write!(writer, "sdiv(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::UnsignedDiv(a, b) => {
                write!(writer, "udiv(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::SignedMod(a, b) => {
                write!(writer, "smod(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::SignedRem(a, b) => {
                write!(writer, "srem(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::UnsignedRem(a, b) => {
                write!(writer, "urem(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::Sub(a, b) => {
                write!(writer, "sub(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            BVExpr::ArrayRead { .. } => write!(writer, "TODO: support array"),
            BVExpr::Ite { cond, tru, fals } => {
                write!(writer, "ite(")?;
                cond.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                tru.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                fals.serialize(ctx, writer)?;
                write!(writer, ")")
            }
        }
    }
}

impl SerializableIrNode for BVExprRef {
    fn serialize<C: Context>(
        &self,
        ctx: &C,
        writer: &mut impl (std::io::Write),
    ) -> std::io::Result<()> {
        ctx.get(*self).serialize(ctx, writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ir_type_size() {
        assert_eq!(std::mem::size_of::<StringRef>(), 2);
        assert_eq!(std::mem::size_of::<BVExprRef>(), 4);
        assert_eq!(std::mem::size_of::<WidthInt>(), 4);
        // 4 bytes for the tag, 4 * 3 bytes for the largest field
        assert_eq!(std::mem::size_of::<BVExpr>(), 16);
        // 4 bytes for the tag, 4 * 3 bytes for the largest field
        assert_eq!(std::mem::size_of::<ArrayExpr>(), 16);
    }

    #[test]
    fn simple_serialization() {
        let mut ctx = BasicContext::default();
        let test_expr = ctx.bv_symbol("test", 3);
        assert_eq!("test", test_expr.serialize_to_str(&ctx));
    }
}
