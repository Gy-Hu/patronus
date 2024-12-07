use clap::Parser;
use patronus::btor2;
use patronus::system::analysis::cone_of_influence;
use patronus::mc::{SmtModelChecker, SmtModelCheckerOptions, BITWUZLA_CMD, BITWUZLA_KISSAT_CMD, BITWUZLA_ABSTRACTION_CMD, YICES2_CMD,YICES2_KISSAT_CMD, ModelCheckResult};
use patronus::system::TransitionSystem;
use std::path::PathBuf;
use futures::stream::FuturesUnordered;
use futures::StreamExt;
use std::sync::Arc;
use tokio::sync::Mutex;
use tokio::select;
use tokio::process::Command as TokioCommand;
use std::time::Duration;
use tokio::time::sleep;
use std::sync::atomic::{AtomicBool, Ordering};
use std::process::Command;
use ctrlc;

// Global flag to track if we're shutting down
static SHUTTING_DOWN: AtomicBool = AtomicBool::new(false);

/// Verification tool using Bitwuzla
#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Input BTOR2 file
    #[arg(short, long)]
    input: PathBuf,
}

fn setup_signal_handler() {
    ctrlc::set_handler(move || {
        println!("\nReceived Ctrl+C, cleaning up...");
        SHUTTING_DOWN.store(true, Ordering::SeqCst);
        
        // Kill all child processes in the process group
        if cfg!(unix) {
            unsafe {
                libc::kill(0, libc::SIGTERM);
            }
        }
        
        std::process::exit(0);
    }).expect("Error setting Ctrl-C handler");
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    // Set up signal handler for cleanup
    setup_signal_handler();
    
    // Create a new process group if on Unix
    #[cfg(unix)]
    unsafe {
        libc::setpgid(0, 0);
    }

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
            let bitwuzla_kissat_solver = SmtModelChecker::new(BITWUZLA_KISSAT_CMD, solver_opts.clone());
            let bitwuzla_abstraction_solver = SmtModelChecker::new(BITWUZLA_ABSTRACTION_CMD, solver_opts.clone());
            let yices_solver = SmtModelChecker::new(YICES2_CMD, solver_opts.clone());
            let yices_kissat_solver = SmtModelChecker::new(YICES2_KISSAT_CMD, solver_opts.clone());

            // Create five tasks for parallel solving
            let mut bitwuzla_handle = {
                let mut ctx = ctx.clone();
                let prop_sys = prop_sys.clone();
                tokio::spawn(async move {
                    ("bitwuzla-smt", bitwuzla_solver.check(&mut ctx, &prop_sys, 1))
                })
            };

            let mut bitwuzla_kissat_handle = {
                let mut ctx = ctx.clone();
                let prop_sys = prop_sys.clone();
                tokio::spawn(async move {
                    ("bitwuzla-kissat", bitwuzla_kissat_solver.check(&mut ctx, &prop_sys, 1))
                })
            };

            let mut bitwuzla_abstraction_handle = {
                let mut ctx = ctx.clone();
                let prop_sys = prop_sys.clone();
                tokio::spawn(async move {
                    ("bitwuzla-abstraction", bitwuzla_abstraction_solver.check(&mut ctx, &prop_sys, 1))
                })
            };

            let mut yices_handle = {
                let mut ctx = ctx.clone();
                let prop_sys = prop_sys.clone();
                tokio::spawn(async move {
                    ("yices", yices_solver.check(&mut ctx, &prop_sys, 1))
                })
            };

            let mut yices_kissat_handle = {
                let mut ctx = ctx.clone();
                let prop_sys = prop_sys.clone();
                tokio::spawn(async move {
                    ("yices-kissat", yices_kissat_solver.check(&mut ctx, &prop_sys, 1))
                })
            };

            let mut native_handle = {
                tokio::spawn(async move {
                    let mut child = TokioCommand::new("bitwuzla")
                        .args(["--lang", "btor2"])
                        .arg(input_path)
                        .kill_on_drop(true)  // Ensure process is killed when dropped
                        .spawn()
                        .unwrap();

                    let result = match child.wait_with_output().await {
                        Ok(output) => {
                            if output.status.success() {
                                let stdout = String::from_utf8_lossy(&output.stdout);
                                if stdout.contains("unsat") {
                                    Ok(ModelCheckResult::Success)
                                } else {
                                    Ok(ModelCheckResult::Success)
                                }
                            } else {
                                Err(std::io::Error::new(
                                    std::io::ErrorKind::Other,
                                    format!("bitwuzla error: {}", String::from_utf8_lossy(&output.stderr))
                                ))
                            }
                        },
                        Err(e) => Err(e),
                    };
                    ("bitwuzla-native", result)
                })
            };

            // Wait for any solver to complete or shutdown signal
            let result = select! {
                bitwuzla_result = &mut bitwuzla_handle => {
                    if !SHUTTING_DOWN.load(Ordering::SeqCst) {
                        yices_handle.abort();
                        yices_kissat_handle.abort();  
                        native_handle.abort();
                        bitwuzla_kissat_handle.abort();
                        bitwuzla_abstraction_handle.abort();
                        bitwuzla_result.unwrap()
                    } else {
                        return (idx, name, cone.len(), ("cancelled", Ok(ModelCheckResult::Success)));
                    }
                }
                
                yices_result = &mut yices_handle => {
                    if !SHUTTING_DOWN.load(Ordering::SeqCst) {
                        bitwuzla_handle.abort();
                        native_handle.abort();
                        bitwuzla_kissat_handle.abort();
                        bitwuzla_abstraction_handle.abort();
                        yices_kissat_handle.abort();  
                        yices_result.unwrap()
                    } else {
                        return (idx, name, cone.len(), ("cancelled", Ok(ModelCheckResult::Success)));
                    }
                }
                yices_kissat_result = &mut yices_kissat_handle => {
                    if !SHUTTING_DOWN.load(Ordering::SeqCst) {
                        bitwuzla_handle.abort();
                        yices_handle.abort();
                        native_handle.abort();
                        bitwuzla_kissat_handle.abort();
                        bitwuzla_abstraction_handle.abort();
                        yices_kissat_result.unwrap()
                    } else {
                        return (idx, name, cone.len(), ("cancelled", Ok(ModelCheckResult::Success)));
                    }
                }
                native_result = &mut native_handle => {
                    if !SHUTTING_DOWN.load(Ordering::SeqCst) {
                        bitwuzla_handle.abort();
                        yices_handle.abort();
                        yices_kissat_handle.abort();
                        bitwuzla_kissat_handle.abort();
                        bitwuzla_abstraction_handle.abort();
                        native_result.unwrap()
                    } else {
                        return (idx, name, cone.len(), ("cancelled", Ok(ModelCheckResult::Success)));
                    }
                }
                bitwuzla_kissat_result = &mut bitwuzla_kissat_handle => {
                    if !SHUTTING_DOWN.load(Ordering::SeqCst) {
                        bitwuzla_handle.abort();
                        yices_handle.abort();
                        yices_kissat_handle.abort();
                        native_handle.abort();
                        bitwuzla_abstraction_handle.abort();
                        bitwuzla_kissat_result.unwrap()
                    } else {
                        return (idx, name, cone.len(), ("cancelled", Ok(ModelCheckResult::Success)));
                    }
                }
                bitwuzla_abstraction_result = &mut bitwuzla_abstraction_handle => {
                    if !SHUTTING_DOWN.load(Ordering::SeqCst) {
                        bitwuzla_handle.abort();
                        yices_handle.abort();
                        yices_kissat_handle.abort();
                        native_handle.abort();
                        bitwuzla_kissat_handle.abort();
                        bitwuzla_abstraction_result.unwrap()
                    } else {
                        return (idx, name, cone.len(), ("cancelled", Ok(ModelCheckResult::Success)));
                    }
                }
            };
            
            // Return verification info
            (idx, name, cone.len(), result)
        });
        
        futures.push(future);
    }

    // Process results as they complete
    while let Some(result) = futures.next().await {
        if SHUTTING_DOWN.load(Ordering::SeqCst) {
            break;
        }
        
        match result {
            Ok((idx, name, cone_size, (solver_name, verify_result))) => {
                println!("\nVerifying bad {} with parallel solvers", idx);
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

    // Signal that we're shutting down
    SHUTTING_DOWN.store(true, Ordering::SeqCst);
    
    // Kill all child processes in the process group
    if cfg!(unix) {
        unsafe {
            libc::kill(0, libc::SIGTERM);
        }
    }
    
    // Small delay to allow processes to clean up
    sleep(Duration::from_millis(100)).await;
    
    std::process::exit(0);
} 