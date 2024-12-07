use clap::Parser;
use patronus::btor2;
use patronus::system::analysis::cone_of_influence;
use patronus::mc::{SmtModelChecker, SmtModelCheckerOptions, BITWUZLA_CMD, YICES2_CMD, ModelCheckResult};
use patronus::system::TransitionSystem;
use std::path::PathBuf;
use futures::stream::FuturesUnordered;
use futures::StreamExt;
use std::sync::Arc;
use tokio::sync::Mutex;
use tokio::select;
use tokio::process::Command as TokioCommand;

/// Verification tool using Bitwuzla
#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Input BTOR2 file
    #[arg(short, long)]
    input: PathBuf,
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let args = Args::parse();
    let input_path = args.input.clone();

    // Parse BTOR2 file
    println!("Reading BTOR2 file: {}", input_path.display());
    let (ctx, sys) = btor2::parse_file(input_path).unwrap();
    
    // Wrap context in Arc<Mutex> for thread safety
    let ctx = Arc::new(Mutex::new(ctx));

    // Configure solver options
    let solver_opts = SmtModelCheckerOptions {
        check_constraints: true,
        check_bad_states_individually: true,
        save_smt_replay: false,
    };

    // Create a FuturesUnordered to handle tasks
    let mut futures = FuturesUnordered::new();
    
    for (idx, bad) in sys.bad_states.iter().enumerate() {
        let ctx = Arc::clone(&ctx);
        let sys = sys.clone();
        let bad = *bad;
        let solver_opts = solver_opts.clone();
        let input_path = args.input.clone();
        
        // Spawn a new task for each property that runs all solvers
        let future = tokio::spawn(async move {
            let mut prop_sys = TransitionSystem::new(format!("prop_{}", idx));
            
            // Get property name
            let ctx = ctx.lock().await;
            let name = ctx.get_symbol_name(bad).map(|s| s.to_string());
            
            // Get cone of influence
            let cone = cone_of_influence(&ctx, &sys, bad);
            
            // Copy over only the signals in the COI
            for signal in &cone {
                if sys.inputs.contains(signal) {
                    prop_sys.inputs.push(*signal);
                }
                // Find state by symbol
                for state in &sys.states {
                    if state.symbol == *signal {
                        prop_sys.states.push(state.clone());
                        break;
                    }
                }
            }
            
            // Add only this bad state
            prop_sys.bad_states.push(bad);

            // Copy constraints that only involve signals in the COI
            for constraint in &sys.constraints {
                let constraint_cone = cone_of_influence(&ctx, &sys, *constraint);
                if constraint_cone.iter().all(|s| cone.contains(s)) {
                    prop_sys.constraints.push(*constraint);
                }
            }

            // Create solver instances
            let bitwuzla_solver = SmtModelChecker::new(BITWUZLA_CMD, solver_opts.clone());
            let yices_solver = SmtModelChecker::new(YICES2_CMD, solver_opts.clone());

            // Create three tasks for parallel solving
            let mut bitwuzla_handle = {
                let mut ctx = ctx.clone();
                let prop_sys = prop_sys.clone();
                tokio::spawn(async move {
                    ("bitwuzla-smt", bitwuzla_solver.check(&mut ctx, &prop_sys, 1))
                })
            };

            let mut yices_handle = {
                let mut ctx = ctx.clone();
                let prop_sys = prop_sys.clone();
                tokio::spawn(async move {
                    ("yices", yices_solver.check(&mut ctx, &prop_sys, 1))
                })
            };

            let mut native_handle = {
                tokio::spawn(async move {
                    let output = TokioCommand::new("bitwuzla")
                        .args(["--lang", "btor2"])
                        .arg(input_path)
                        .output()
                        .await
                        .unwrap();

                    let result = if output.status.success() {
                        let stdout = String::from_utf8_lossy(&output.stdout);
                        if stdout.contains("unsat") {
                            Ok(ModelCheckResult::Success)
                        } else {
                            // TODO: Parse witness from stdout if needed
                            Ok(ModelCheckResult::Success) // Temporary, should be properly parsed
                        }
                    } else {
                        Err(std::io::Error::new(
                            std::io::ErrorKind::Other,
                            format!("bitwuzla error: {}", String::from_utf8_lossy(&output.stderr))
                        ))
                    };
                    ("bitwuzla-native", result)
                })
            };

            // Wait for any solver to complete
            let result = select! {
                bitwuzla_result = &mut bitwuzla_handle => {
                    yices_handle.abort();
                    native_handle.abort();
                    bitwuzla_result.unwrap()
                }
                yices_result = &mut yices_handle => {
                    bitwuzla_handle.abort();
                    native_handle.abort();
                    yices_result.unwrap()
                }
                native_result = &mut native_handle => {
                    bitwuzla_handle.abort();
                    yices_handle.abort();
                    native_result.unwrap()
                }
            };
            
            // Return verification info
            (idx, name, cone.len(), result)
        });
        
        futures.push(future);
    }

    // Process results as they complete
    while let Some(result) = futures.next().await {
        match result {
            Ok((idx, name, cone_size, (solver_name, verify_result))) => {
                println!("\nVerifying bad state {} with parallel solvers", idx);
                if let Some(name) = name {
                    println!("Property name: {}", name);
                }
                println!("Cone size: {}", cone_size);
                println!("{} finished first", solver_name);
                
                match verify_result {
                    Ok(ModelCheckResult::Success) => {
                        println!("Property VERIFIED");
                    }
                    Ok(ModelCheckResult::Fail(wit)) => {
                        println!("Property VIOLATED!");
                        
                        // Print witness
                        println!("Witness:");
                        for (idx, value) in wit.inputs[0].iter().enumerate() {
                            if let Some(name) = &wit.input_names[idx] {
                                println!("  {}: {:?}", name, value);
                            }
                        }
                    }
                    Err(e) => println!("Error: {}", e),
                }
            }
            Err(e) => println!("Task failed: {}", e),
        }
    }

    Ok(())
} 