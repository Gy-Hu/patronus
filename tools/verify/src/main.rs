use clap::Parser;
use patronus::btor2;
use patronus::system::analysis::cone_of_influence;
use patronus::mc::{SmtModelChecker, SmtModelCheckerOptions, BITWUZLA_CMD, ModelCheckResult};
use patronus::system::{TransitionSystem, State};
use std::path::PathBuf;
use futures::future::join_all;
use std::sync::Arc;
use tokio::sync::Mutex;

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

    // Parse BTOR2 file
    println!("Reading BTOR2 file: {}", args.input.display());
    let (ctx, sys) = btor2::parse_file(args.input).unwrap();
    
    // Wrap context in Arc<Mutex> for thread safety
    let ctx = Arc::new(Mutex::new(ctx));

    // Configure solver options
    let solver_opts = SmtModelCheckerOptions {
        check_constraints: true,
        check_bad_states_individually: true,
        save_smt_replay: false,
    };

    // Create futures for each property verification
    let mut futures = Vec::new();
    
    for (idx, bad) in sys.bad_states.iter().enumerate() {
        let ctx = Arc::clone(&ctx);
        let sys = sys.clone();
        let bad = *bad;
        
        // Spawn a new task for each property
        let future = tokio::spawn(async move {
            let mut prop_sys = TransitionSystem::new(format!("prop_{}", idx));
            
            // Get property name
            let mut ctx = ctx.lock().await;
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

            // Create solver instance
            let solver = SmtModelChecker::new(BITWUZLA_CMD, solver_opts.clone());

            // Run verification
            let result = solver.check(&mut ctx, &prop_sys, 1);
            
            // Return verification info
            (idx, name, cone.len(), result)
        });
        
        futures.push(future);
    }

    // Wait for all verifications to complete and print results as they arrive
    for result in join_all(futures).await {
        match result {
            Ok((idx, name, cone_size, verify_result)) => {
                println!("\nVerifying bad state {}", idx);
                if let Some(name) = name {
                    println!("Property name: {}", name);
                }
                println!("Cone size: {}", cone_size);
                
                match verify_result {
                    Ok(ModelCheckResult::Success) => {
                        println!("Property VERIFIED");
                    }
                    Ok(ModelCheckResult::Fail(wit)) => {
                        println!("Property VIOLATED!");
                        println!("Failed properties: {:?}", wit.failed_safety);
                        
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