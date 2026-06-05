// Copyright 2023 The Regents of the University of California
// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use clap::{Parser, ValueEnum};
use patronus::expr::*;
use patronus::mc::bmc;
use patronus::smt::*;
use patronus::system::transform::simplify_expressions;
use patronus::*;
use std::fs::File;
use std::io::{BufWriter, Write};

#[derive(Parser, Debug)]
#[command(name = "bmc")]
#[command(author = "Kevin Laeufer <laeufer@berkeley.edu>")]
#[command(version)]
#[command(about = "Performs bounded model checking on a btor2 file.", long_about = None)]
struct Args {
    #[arg(
        long,
        value_enum,
        default_value = "bitwuzla",
        help = "the SMT solver to use"
    )]
    solver: SolverChoice,
    #[arg(short, long, default_value = "25")]
    kmax: u64,
    #[arg(short, long)]
    verbose: bool,
    #[arg(short, long)]
    skip_simplify: bool,
    #[arg(short, long)]
    dump_smt: bool,
    #[arg(long, help = "dump SMT-LIB to replay.smt without invoking the solver")]
    dump_only: bool,
    #[arg(value_name = "BTOR2", index = 1)]
    filename: String,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum SolverChoice {
    Bitwuzla,
    Yices2,
    Z3,
    CVC5,
}

fn main() {
    let args = Args::parse();
    let (mut ctx, mut sys) = btor2::parse_file(&args.filename).expect("Failed to load btor2 file!");
    if !args.skip_simplify {
        if args.verbose {
            println!("simplifying...")
        };
        // replace_anonymous_inputs_with_zero(&mut ctx, &mut sys);
        simplify_expressions(&mut ctx, &mut sys);
    }
    if args.verbose {
        println!("Loaded: {}", sys.name);
        println!("{}", sys.serialize_to_str(&ctx));
        println!();
        println!();
    }
    let k_max = args.kmax;
    let check_constraints = true;
    let check_bad_states_individually = false;
    let solver = match args.solver {
        SolverChoice::Bitwuzla => BITWUZLA,
        SolverChoice::Yices2 => YICES2,
        SolverChoice::Z3 => Z3,
        SolverChoice::CVC5 => CVC5,
    };
    if args.verbose {
        println!("Checking up to {k_max} using {}.", solver.name());
    }
    if args.dump_only {
        let dump_file = File::create("replay.smt").unwrap();
        let mut smt_ctx = DumpOnlySolverCtx::new(solver, dump_file).expect("failed to dump SMT");
        bmc(
            &mut ctx,
            &mut smt_ctx,
            &sys,
            check_constraints,
            check_bad_states_individually,
            k_max,
        )
        .unwrap();
        return;
    }
    let dump_file = if args.dump_smt {
        Some(File::create("replay.smt").unwrap())
    } else {
        None
    };
    let mut smt_ctx = solver.start(dump_file).expect("failed to start solver");
    let res = bmc(
        &mut ctx,
        &mut smt_ctx,
        &sys,
        check_constraints,
        check_bad_states_individually,
        k_max,
    )
    .unwrap();
    match res {
        mc::ModelCheckResult::Success => {
            println!("unsat");
        }
        mc::ModelCheckResult::Unknown => {
            println!("unknown");
        }
        mc::ModelCheckResult::Fail(wit) => {
            btor2::print_witness(&mut std::io::stdout(), &wit).unwrap();
        }
    }
}

struct DumpOnlySolverCtx {
    solver: SmtLibSolver,
    out: BufWriter<File>,
    stack_depth: usize,
}

impl DumpOnlySolverCtx {
    fn new(solver: SmtLibSolver, file: File) -> Result<Self> {
        let mut out = BufWriter::new(file);
        solver.write_options(&mut out)?;
        Ok(Self {
            solver,
            out,
            stack_depth: 0,
        })
    }

    fn write_cmd(&mut self, ctx: Option<&Context>, cmd: &SmtCommand) -> Result<()> {
        serialize_cmd(&mut self.out, ctx, cmd)?;
        self.out.flush()?;
        Ok(())
    }
}

impl Drop for DumpOnlySolverCtx {
    fn drop(&mut self) {
        let _ = self.write_cmd(None, &SmtCommand::Exit);
    }
}

impl SolverMetaData for DumpOnlySolverCtx {
    fn name(&self) -> &str {
        self.solver.name()
    }

    fn supports_check_assuming(&self) -> bool {
        self.solver.supports_check_assuming()
    }

    fn supports_uf(&self) -> bool {
        self.solver.supports_uf()
    }

    fn supports_const_array(&self) -> bool {
        self.solver.supports_const_array()
    }
}

impl SolverContext for DumpOnlySolverCtx {
    fn restart(&mut self) -> Result<()> {
        self.stack_depth = 0;
        Ok(())
    }

    fn set_logic(&mut self, option: Logic) -> Result<()> {
        self.write_cmd(None, &SmtCommand::SetLogic(option))
    }

    fn assert(&mut self, ctx: &Context, e: ExprRef) -> Result<()> {
        self.write_cmd(Some(ctx), &SmtCommand::Assert(e))
    }

    fn declare_const(&mut self, ctx: &Context, symbol: ExprRef) -> Result<()> {
        self.write_cmd(Some(ctx), &SmtCommand::DeclareConst(symbol))
    }

    fn define_const(&mut self, ctx: &Context, symbol: ExprRef, expr: ExprRef) -> Result<()> {
        self.write_cmd(Some(ctx), &SmtCommand::DefineConst(symbol, expr))
    }

    fn check_sat_assuming(
        &mut self,
        ctx: &Context,
        props: impl IntoIterator<Item = ExprRef>,
    ) -> Result<CheckSatResponse> {
        let props = props.into_iter().collect();
        self.write_cmd(Some(ctx), &SmtCommand::CheckSatAssuming(props))?;
        Ok(CheckSatResponse::Unsat)
    }

    fn check_sat(&mut self) -> Result<CheckSatResponse> {
        self.write_cmd(None, &SmtCommand::CheckSat)?;
        if self.stack_depth == 0 {
            Ok(CheckSatResponse::Sat)
        } else {
            Ok(CheckSatResponse::Unsat)
        }
    }

    fn push(&mut self) -> Result<()> {
        self.write_cmd(None, &SmtCommand::Push(1))?;
        self.stack_depth += 1;
        Ok(())
    }

    fn pop(&mut self) -> Result<()> {
        if self.stack_depth > 0 {
            self.write_cmd(None, &SmtCommand::Pop(1))?;
            self.stack_depth -= 1;
            Ok(())
        } else {
            Err(Error::StackUnderflow)
        }
    }

    fn get_value(&mut self, _ctx: &mut Context, _e: ExprRef) -> Result<ExprRef> {
        Err(Error::UnexpectedResponse(
            self.name().to_string(),
            "dump-only mode does not support get-value".to_string(),
        ))
    }
}
