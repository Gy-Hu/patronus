// Demo: read a btor2, COI-reduce to keep only signals relevant to every bad state
// and every constraint, then serialize.
//
// Usage:  coi_demo <input.btor> <full_out.btor> <reduced_out.btor>
//
// Writes (1) the original system re-serialized, and (2) the COI-reduced system.

use patronus::btor2;
use patronus::expr::*;
use patronus::system::analysis::cone_of_influence;
use patronus::system::{State, TransitionSystem};
use rustc_hash::FxHashSet;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let input = &args[1];
    let full_out = &args[2];
    let reduced_out = &args[3];

    let (mut ctx, mut sys) = btor2::parse_file(input).unwrap();

    // btor2aiger converts `bad` and `constraint` into AIGER properties/constraints
    // but drops plain `output` lines. To use abc's `dsec`/`cec` for equivalence
    // checking between the full and COI-reduced systems, we need the outputs to
    // survive the AIGER conversion. Promote every `output` expression into a
    // sequence of 1-bit `bad` lines (one per bit), so btor2aiger keeps them in a
    // stable, aligned order between the two files. We do this *before* reduction,
    // so COI sees these bads as roots just like the original outputs.
    promote_outputs_to_bads(&mut ctx, &mut sys);

    let reduced = reduce_by_coi(&ctx, &sys);

    // Serialization may panic when running in COI_SINGLE_PROP mode, since we
    // leave all outputs/bads in place — some of them will reference symbols
    // not in the reduced state/input set. That's fine when we only want to
    // print the COI set and compare against pono.
    if std::env::var("COI_NO_WRITE").is_err() {
        std::fs::write(full_out, btor2::serialize_to_str(&ctx, &sys)).unwrap();
        std::fs::write(reduced_out, btor2::serialize_to_str(&ctx, &reduced)).unwrap();
    }

    if std::env::var("COI_DUMP_NAMES").is_ok() {
        eprintln!("COI statevars (kept):");
        let mut names: Vec<&str> = reduced
            .states
            .iter()
            .map(|s| ctx[s.symbol].get_symbol_name(&ctx).unwrap_or("?"))
            .collect();
        names.sort();
        for n in names {
            eprintln!("  {n}");
        }
        // For a fair comparison against pono, also list every original input
        // whose symbol appears in the cone. We iterate the original `sys`
        // because the reduced system intentionally keeps *all* inputs to
        // preserve the primary-input interface for abc `dsec`.
        eprintln!("COI inputvars (in cone):");
        let keep: rustc_hash::FxHashSet<ExprRef> = {
            let roots = sys
                .bad_states
                .iter()
                .copied()
                .chain(sys.constraints.iter().copied())
                .chain(sys.outputs.iter().map(|o| o.expr));
            let mut out = rustc_hash::FxHashSet::default();
            for r in roots {
                for sym in cone_of_influence(&ctx, &sys, r) {
                    out.insert(sym);
                }
            }
            out
        };
        let mut input_names: Vec<&str> = sys
            .inputs
            .iter()
            .filter(|i| keep.contains(i))
            .map(|i| ctx[*i].get_symbol_name(&ctx).unwrap_or("?"))
            .collect();
        input_names.sort();
        for n in input_names {
            eprintln!("  {n}");
        }
    }

    eprintln!(
        "full   : {} inputs, {} states, {} bads, {} constraints, {} outputs",
        sys.inputs.len(),
        sys.states.len(),
        sys.bad_states.len(),
        sys.constraints.len(),
        sys.outputs.len(),
    );
    eprintln!(
        "reduced: {} inputs, {} states, {} bads, {} constraints, {} outputs",
        reduced.inputs.len(),
        reduced.states.len(),
        reduced.bad_states.len(),
        reduced.constraints.len(),
        reduced.outputs.len(),
    );
}

fn promote_outputs_to_bads(ctx: &mut Context, sys: &mut TransitionSystem) {
    use patronus::expr::TypeCheck;
    let outputs: Vec<_> = sys.outputs.iter().map(|o| o.expr).collect();
    for expr in outputs {
        match expr.get_type(ctx) {
            Type::BV(1) => sys.bad_states.push(expr),
            Type::BV(w) => {
                for bit in 0..w {
                    let sliced = ctx.slice(expr, bit, bit);
                    sys.bad_states.push(sliced);
                }
            }
            // Skip array-typed outputs: not expressible as a single-bit bad, and
            // btor2aiger would reject them anyway.
            Type::Array(_) => {}
        }
    }
}

fn reduce_by_coi(ctx: &Context, sys: &TransitionSystem) -> TransitionSystem {
    // Roots: every bad state, every constraint, and every output. Dropping an
    // input/state that none of these depend on is sound w.r.t. all observable
    // behaviour under the given constraints. For apples-to-apples comparison
    // with tools that only support a single property at a time (e.g. pono's
    // `--prop N`), set `COI_SINGLE_PROP=N` to root on only that bad.
    let mut keep: FxHashSet<ExprRef> = FxHashSet::default();
    let roots: Vec<ExprRef> = match std::env::var("COI_SINGLE_PROP") {
        Ok(s) => {
            let idx: usize = s.parse().expect("COI_SINGLE_PROP must be an integer");
            // pono's COI visits bad + constraints; mirror that.
            std::iter::once(sys.bad_states[idx])
                .chain(sys.constraints.iter().copied())
                .collect()
        }
        Err(_) => sys
            .bad_states
            .iter()
            .copied()
            .chain(sys.constraints.iter().copied())
            .chain(sys.outputs.iter().map(|o| o.expr))
            .collect(),
    };
    for r in roots {
        for sym in cone_of_influence(ctx, sys, r) {
            keep.insert(sym);
        }
    }

    let mut out = TransitionSystem::new(format!("{}_coi", sys.name));
    // Keep ALL inputs, even those not in the cone. This preserves the primary
    // input interface so abc's `dsec` can line up the two circuits. Unused
    // inputs remain dangling in the reduced system; that's still sound because
    // observable behaviour only depends on inputs in the cone.
    for &input in sys.inputs.iter() {
        out.add_input(ctx, input);
    }
    for state in sys.states.iter() {
        if keep.contains(&state.symbol) {
            out.add_state(
                ctx,
                State {
                    symbol: state.symbol,
                    init: state.init,
                    next: state.next,
                },
            );
        }
    }
    for &b in sys.bad_states.iter() {
        out.bad_states.push(b);
    }
    for &c in sys.constraints.iter() {
        out.constraints.push(c);
    }
    for o in sys.outputs.iter() {
        out.outputs.push(*o);
    }
    // copy any names carried on individual expressions
    for (expr, name) in sys.names.iter() {
        out.names[expr] = *name;
    }
    out
}
