use clap::Parser;
use patronus::btor2;
use patronus::system::analysis::cone_of_influence;
use patronus::system::TransitionSystem;
use patronus::expr::{Context, Expr, ExprRef, Type, TypeCheck, ArrayType, SerializableIrNode};
use baa::BitVecOps;
use std::path::PathBuf;
use std::collections::HashSet;
use std::io::Write;

/// Cone of Influence analysis tool
#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Input BTOR2 file
    #[arg(short, long)]
    input: PathBuf,

    /// Output intermediate format file
    #[arg(short = 'o', long)]
    output: PathBuf,

    /// Specific bad property to analyze (by name)
    #[arg(short, long)]
    property: Option<String>,
}

fn format_type(ty: &Type) -> String {
    match ty {
        Type::BV(width) => format!("(_ BitVec {})", width),
        Type::Array(array_type) => {
            format!("(Array (_ BitVec {}) (_ BitVec {}))", 
                array_type.index_width,
                array_type.data_width)
        }
    }
}

fn format_operator(op: &str, args: &[String]) -> String {
    if args.is_empty() {
        op.to_string()
    } else {
        format!("({} {})", op, args.join(" "))
    }
}

fn format_expr(expr: &Expr, ctx: &Context) -> String {
    match expr {
        Expr::BVSymbol { name, width, .. } => {
            format!("{} : {}", ctx[*name], format_type(&Type::BV(*width)))
        }
        Expr::BVLiteral(value) => {
            if value.width() <= 8 {
                format!("(_ bv{} {})", value.get(ctx).to_bit_str(), value.width())
            } else {
                format!("(_ bv{} {})", value.get(ctx).to_hex_str(), value.width())
            }
        },
        Expr::BVEqual(a, b) => format_operator("=", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVImplies(a, b) => format_operator("=>", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVAnd(a, b, _) => format_operator("bvand", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVOr(a, b, _) => format_operator("bvor", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVXor(a, b, _) => format_operator("bvxor", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVNot(a, _) => format_operator("bvnot", &[
            format_expr_ref(a, ctx)
        ]),
        Expr::BVNegate(a, _) => format_operator("bvneg", &[
            format_expr_ref(a, ctx)
        ]),
        Expr::BVAdd(a, b, _) => format_operator("bvadd", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVSub(a, b, _) => format_operator("bvsub", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVMul(a, b, _) => format_operator("bvmul", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVSignedDiv(a, b, _) => format_operator("bvsdiv", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVUnsignedDiv(a, b, _) => format_operator("bvudiv", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVSignedRem(a, b, _) => format_operator("bvsrem", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVUnsignedRem(a, b, _) => format_operator("bvurem", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVShiftLeft(a, b, _) => format_operator("bvshl", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVShiftRight(a, b, _) => format_operator("bvlshr", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVArithmeticShiftRight(a, b, _) => format_operator("bvashr", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVIte { cond, tru, fals } => format_operator("ite", &[
            format_expr_ref(cond, ctx),
            format_expr_ref(tru, ctx),
            format_expr_ref(fals, ctx)
        ]),
        Expr::BVZeroExt { e, by, .. } => format_operator("(_ zero_extend {})", &[
            by.to_string(),
            format_expr_ref(e, ctx)
        ]),
        Expr::BVSignExt { e, by, .. } => format_operator("(_ sign_extend {})", &[
            by.to_string(),
            format_expr_ref(e, ctx)
        ]),
        Expr::BVSlice { e, hi, lo, .. } => format_operator("(_ extract {} {})", &[
            hi.to_string(),
            lo.to_string(),
            format_expr_ref(e, ctx)
        ]),
        Expr::BVConcat(a, b, _) => format_operator("concat", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::ArraySymbol { name, index_width, data_width } => {
            format!("{} : {}", 
                ctx[*name],
                format_type(&Type::Array(ArrayType { index_width: *index_width, data_width: *data_width })))
        }
        Expr::ArrayConstant { e, index_width, data_width } => {
            format!("(const {} : {})", 
                format_expr_ref(e, ctx),
                format_type(&Type::Array(ArrayType { index_width: *index_width, data_width: *data_width })))
        }
        Expr::ArrayEqual(a, b) => format_operator("=", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::ArrayStore { array, index, data } => format_operator("store", &[
            format_expr_ref(array, ctx),
            format_expr_ref(index, ctx),
            format_expr_ref(data, ctx)
        ]),
        Expr::BVArrayRead { array, index, .. } => format_operator("select", &[
            format_expr_ref(array, ctx),
            format_expr_ref(index, ctx)
        ]),
        Expr::BVGreater(a, b) => format_operator("bvugt", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVGreaterSigned(a, b, _) => format_operator("bvsgt", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVGreaterEqual(a, b) => format_operator("bvuge", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        Expr::BVGreaterEqualSigned(a, b, _) => format_operator("bvsge", &[
            format_expr_ref(a, ctx),
            format_expr_ref(b, ctx)
        ]),
        _ => expr.serialize_to_str(ctx)
    }
}

fn format_expr_ref(expr_ref: &ExprRef, ctx: &Context) -> String {
    format_expr(&ctx[*expr_ref], ctx)
}

fn write_coi_system(sys: &TransitionSystem, signals: &HashSet<ExprRef>, ctx: &Context, writer: &mut impl Write) -> std::io::Result<()> {
    writeln!(writer, "; Intermediate format for COI-reduced system")?;
    writeln!(writer, "; Original system name: {}", sys.name)?;
    writeln!(writer, "; Signals in COI: {}", signals.len())?;
    writeln!(writer)?;

    writeln!(writer, "(module {}", sys.name)?;
    writeln!(writer)?;

    // 输出状态变量
    writeln!(writer, "  ; State variables")?;
    for state in &sys.states {
        if signals.contains(&state.symbol) {
            let expr = &ctx[state.symbol];
            let name = expr.get_symbol_name(ctx).unwrap_or("anonymous");
            writeln!(writer, "  (state")?;
            writeln!(writer, "    (name {})", format_expr(expr, ctx))?;
            writeln!(writer, "    (type {})", format_type(&expr.get_type(ctx)))?;
            writeln!(writer, "    (comment \"{}\")", name)?;
            if let Some(init) = state.init {
                let init_expr = &ctx[init];
                writeln!(writer, "    (init {})", format_expr(init_expr, ctx))?;
            }
            if let Some(next) = state.next {
                let next_expr = &ctx[next];
                writeln!(writer, "    (next {})", format_expr(next_expr, ctx))?;
            }
            writeln!(writer, "  )")?;
        }
    }
    writeln!(writer)?;

    // 输出输入变量
    writeln!(writer, "  ; Input variables")?;
    for &input in &sys.inputs {
        if signals.contains(&input) {
            let expr = &ctx[input];
            let name = expr.get_symbol_name(ctx).unwrap_or("anonymous");
            writeln!(writer, "  (input")?;
            writeln!(writer, "    (name {})", format_expr(expr, ctx))?;
            writeln!(writer, "    (type {})", format_type(&expr.get_type(ctx)))?;
            writeln!(writer, "    (comment \"{}\")", name)?;
            writeln!(writer, "  )")?;
        }
    }
    writeln!(writer)?;

    // 输出坏状态
    writeln!(writer, "  ; Bad states")?;
    for &bad in &sys.bad_states {
        let expr = &ctx[bad];
        let name = expr.get_symbol_name(ctx).unwrap_or("anonymous");
        writeln!(writer, "  (bad")?;
        writeln!(writer, "    (expr {})", format_expr(expr, ctx))?;
        writeln!(writer, "    (type {})", format_type(&expr.get_type(ctx)))?;
        writeln!(writer, "    (comment \"{}\")", name)?;
        writeln!(writer, "  )")?;
    }
    writeln!(writer)?;

    // 输出约束
    writeln!(writer, "  ; Constraints")?;
    for &constraint in &sys.constraints {
        if signals.contains(&constraint) {
            let expr = &ctx[constraint];
            writeln!(writer, "  (constraint")?;
            writeln!(writer, "    (expr {})", format_expr(expr, ctx))?;
            writeln!(writer, "    (type {})", format_type(&expr.get_type(ctx)))?;
            writeln!(writer, "  )")?;
        }
    }

    writeln!(writer, ")")?;
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    // 解析 BTOR2 文件
    let (ctx, sys) = btor2::parse_file(&args.input)
        .ok_or_else(|| format!("Failed to parse BTOR2 file: {}", args.input.display()))?;

    // 找到所有的 bad 属性
    let bad_props: Vec<_> = sys.bad_states.iter().copied().collect();
    println!("Found {} bad properties", bad_props.len());

    // 收集所有需要保留的信号
    let mut all_signals = HashSet::new();

    // 如果指定了特定属性，只分析该属性
    if let Some(prop_name) = args.property {
        for (i, bad) in bad_props.iter().enumerate() {
            if let Some(name) = ctx.get_symbol_name(*bad) {
                if name == prop_name {
                    let cone = cone_of_influence(&ctx, &sys, *bad);
                    println!("Analyzing property '{}' (cone size: {})", name, cone.len());
                    
                    for symbol in &cone {
                        all_signals.insert(*symbol);
                        if let Some(sym_name) = ctx.get_symbol_name(*symbol) {
                            println!("  Symbol in cone: {}", sym_name);
                        }
                    }
                    break;
                }
            }
        }
    } else {
        // 分析所有属性
        for (i, bad) in bad_props.iter().enumerate() {
            let cone = cone_of_influence(&ctx, &sys, *bad);
            if let Some(name) = ctx.get_symbol_name(*bad) {
                println!("Bad property {} '{}' cone size: {}", i, name, cone.len());
            } else {
                println!("Bad property {} cone size: {}", i, cone.len());
            }
            
            for symbol in &cone {
                all_signals.insert(*symbol);
                if let Some(name) = ctx.get_symbol_name(*symbol) {
                    println!("  Symbol in cone: {}", name);
                }
            }
        }
    }

    // 输出中间格式
    let mut file = std::fs::File::create(&args.output)?;
    write_coi_system(&sys, &all_signals, &ctx, &mut file)?;
    println!("Written intermediate format to {}", args.output.display());

    Ok(())
} 