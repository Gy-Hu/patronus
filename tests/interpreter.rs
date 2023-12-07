// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use libpatron::btor2;
use libpatron::ir::Context;
use libpatron::mc::Simulator;
use libpatron::sim::interpreter::{InitKind, Interpreter};

const COUNT_2: &str = r#"
1 sort bitvec 3
2 zero 1
3 state 1
4 init 1 3 2
5 one 1
6 add 1 3 5
7 next 1 3 6
8 ones 1
9 sort bitvec 1
10 eq 9 3 8
11 bad 10
"#;

#[test]
fn interpret_count_2() {
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, COUNT_2, Some("count2")).unwrap();
    let counter_state = sys.states().next().unwrap().symbol;
    let bad = sys.bad_states().first().unwrap().0;
    let mut sim = Interpreter::new(&ctx, &sys);

    // init
    sim.init(InitKind::Zero);
    sim.update();
    assert_eq!(sim.get(counter_state).unwrap().to_u64().unwrap(), 0);

    // increment counter by one
    sim.step();
    sim.update();
    assert_eq!(sim.get(counter_state).unwrap().to_u64().unwrap(), 1);

    // save state
    let at_one = sim.take_snapshot();

    // increment counter to three
    sim.step();
    sim.update();
    sim.step();
    sim.update();
    assert_eq!(sim.get(counter_state).unwrap().to_u64().unwrap(), 3);

    // save state again
    let at_three = sim.take_snapshot();

    // restore state
    sim.restore_snapshot(at_one);
    sim.update();
    assert_eq!(sim.get(counter_state).unwrap().to_u64().unwrap(), 1);
    sim.step();
    sim.update();
    assert_eq!(sim.get(counter_state).unwrap().to_u64().unwrap(), 2);

    // restore again
    sim.restore_snapshot(at_three);
    sim.update();
    assert_eq!(sim.get(counter_state).unwrap().to_u64().unwrap(), 3);

    // make bad condition fail
    while sim.get(bad).unwrap().to_u64().unwrap() == 0 {
        sim.step();
        sim.update();
    }

    // the failure is reached when the state is 7
    assert_eq!(sim.get(counter_state).unwrap().to_u64().unwrap(), 7);
}
