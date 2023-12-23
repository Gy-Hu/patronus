// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use clap::{arg, Parser, ValueEnum};
use libpatron::ir::*;
use libpatron::mc::Simulator;
use libpatron::sim::interpreter::{InitKind, Interpreter};
use libpatron::*;
use num_bigint::BigUint;
use num_traits::Num;
use std::collections::HashMap;
use std::io::BufRead;

#[derive(Parser, Debug)]
#[command(name = "sim")]
#[command(author = "Kevin Laeufer <laeufer@berkeley.edu>")]
#[command(version)]
#[command(about = "Simulates a transitions system from a btor2 file.", long_about = None)]
struct Args {
    #[arg(short, long)]
    verbose: bool,
    #[arg(short, long, help = "print out signal values for each step")]
    trace: bool,
    #[arg(
        long,
        value_enum,
        default_value = "random",
        help = "initialization strategy"
    )]
    init: Init,
    #[arg(long, help = "Filename of a testbench.")]
    testbench: Option<String>,
    #[arg(value_name = "BTOR2", index = 1)]
    filename: String,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Init {
    Zero,
    Random,
}

fn main() {
    let args = Args::parse();
    let (ctx, sys) = btor2::parse_file(&args.filename).expect("Failed to load btor2 file!");
    if args.verbose {
        println!("Loaded: {}", sys.name);
        println!("{}", sys.serialize_to_str(&ctx));
        println!();
        println!();
    }

    // start execution
    let start_load = std::time::Instant::now();
    let mut sim = Interpreter::new(&ctx, &sys);
    match args.init {
        Init::Zero => {
            sim.init(InitKind::Zero);
        }
        Init::Random => {
            sim.init(InitKind::Random(0));
        }
    }
    let delta_load = std::time::Instant::now() - start_load;
    println!("Loaded the design into the interpreter in {:?}", delta_load);

    let testbench_file = match args.testbench {
        None => {
            println!("No testbench provided. Exiting...");
            return;
        }
        Some(tb) => tb,
    };

    let mut tb = std::io::BufReader::new(
        std::fs::File::open(testbench_file).expect("Failed to load testbench file"),
    );

    let name_to_ref = sys.generate_name_to_ref(&ctx);
    let (inputs, outputs) =
        read_header(&mut tb, &name_to_ref, &sys, &ctx).expect("Failed to read testbench header");
    if args.verbose {
        println!("Inputs: {inputs:?}");
        println!("Outputs: {outputs:?}");
    }

    let mut signals_to_print: Vec<(String, ExprRef)> = Vec::new();
    if args.trace {
        for (name, expr) in name_to_ref.iter() {
            // TODO: maybe filter
            if expr.get_type(&ctx).is_bit_vector() {
                // we do not print arrays
                signals_to_print.push((name.clone(), expr.clone()));
            }
        }
        signals_to_print.sort_by_key(|(name, _)| name.clone());
    }

    let start_exec = std::time::Instant::now();
    for (step_id, line) in tb.lines().flatten().enumerate() {
        do_step(
            step_id,
            &mut sim,
            &line,
            &inputs,
            &outputs,
            &signals_to_print,
        );
    }
    let delta_exec = std::time::Instant::now() - start_exec;
    println!("Executed {} steps in {:?}", sim.step_count(), delta_exec);
}

type IOInfo = Vec<(usize, ExprRef, String, WidthInt)>;

/// Correlates the header with the inputs and outputs of the system.
fn read_header(
    input: &mut impl BufRead,
    name_to_ref: &HashMap<String, ExprRef>,
    sys: &TransitionSystem,
    ctx: &Context,
) -> std::io::Result<(IOInfo, IOInfo)> {
    let mut line = String::new();
    input.read_line(&mut line)?;
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    for (cell_id, cell) in line.split(",").enumerate() {
        let name = cell.trim();
        if let Some(signal_ref) = name_to_ref.get(name) {
            let width = signal_ref.get_bv_type(ctx).unwrap();
            let signal = sys.get_signal(*signal_ref).unwrap();
            if signal.is_input() {
                inputs.push((cell_id, *signal_ref, name.to_string(), width));
            }
            if signal.is_output() {
                outputs.push((cell_id, *signal_ref, name.to_string(), width));
            }
        }
    }
    Ok((inputs, outputs))
}

/// Reads one line in the CSV, applies inputs, checks outputs and finally steps the system.
fn do_step(
    step_id: usize,
    sim: &mut impl Simulator,
    line: &str,
    inputs: &[(usize, ExprRef, String, WidthInt)],
    outputs: &[(usize, ExprRef, String, WidthInt)],
    signal_to_print: &[(String, ExprRef)],
) {
    // apply inputs
    let mut input_iter = inputs.iter();
    if let Some(mut input) = input_iter.next() {
        for (cell_id, cell) in line.split(",").enumerate() {
            if cell_id == input.0 {
                // apply input
                let trimmed = cell.trim();
                if trimmed.to_ascii_lowercase() != "x" {
                    let value = u64::from_str_radix(trimmed, 10).unwrap();
                    let width = input.3;
                    sim.set(input.1, (&Value::from_u64(value, width)).into());
                }

                // get next input
                if let Some(next_input) = input_iter.next() {
                    input = next_input;
                } else {
                    break;
                }
            }
        }
    }

    // calculate the output values
    sim.update();

    // print values if the option is enables
    if !signal_to_print.is_empty() {
        println!();
        for (name, expr) in signal_to_print.iter() {
            if let Some(value_ref) = sim.get(*expr) {
                let value = value_ref.to_bit_string();
                println!("{name}@{step_id} = {value}")
            }
        }
    }

    // check outputs
    let mut output_iter = outputs.iter();
    if let Some(mut output) = output_iter.next() {
        for (cell_id, cell) in line.split(",").enumerate() {
            if cell_id == output.0 {
                // apply input
                let trimmed = cell.trim();
                if trimmed.to_ascii_lowercase() != "x" {
                    let expected_big = BigUint::from_str_radix(trimmed, 10).unwrap();
                    let width = output.3;
                    let expected = Value::from_big_uint(&expected_big, width);
                    let actual = sim.get(output.1).unwrap();
                    assert_eq!(expected, actual, "{}@{step_id}", output.2);
                }

                // get next output
                if let Some(next_output) = output_iter.next() {
                    output = next_output;
                } else {
                    break;
                }
            }
        }
    }

    // advance simulation
    sim.step();
}
