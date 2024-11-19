// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use patronus::expr::*;

/// test a simplification
fn ts(inp: &str, expect: &str) {
    let mut ctx = Context::default();
    let input = parse_expr(&mut ctx, inp);
    let expected = parse_expr(&mut ctx, expect);
    let simplified = simplify_single_expression(&mut ctx, input);
    assert_eq!(
        simplified,
        expected,
        "simplify({}) = {}\nExpected: {}",
        input.serialize_to_str(&ctx),
        simplified.serialize_to_str(&ctx),
        expected.serialize_to_str(&ctx)
    );
}

#[test]
fn test_simplify_and_or() {
    ts("true", "true");
    ts("false", "false");
    ts("and(true, false)", "false");
    ts("and(true, true)", "true");
    ts("or(false, true)", "true");
    ts("or(false, false)", "false");
    ts("and(a : bv<1>, true)", "a : bv<1>");
    ts("and(a : bv<1>, false)", "false");
    ts("or(a : bv<1>, true)", "true");
    ts("or(a : bv<1>, false)", "a : bv<1>");
}

#[test]
fn test_simplify_ite() {
    // outcome is always the same
    ts("ite(c : bv<1>, a: bv<10>, a)", "a : bv<10>");

    // constant condition
    ts("ite(true, a: bv<10>, b: bv<10>)", "a : bv<10>");
    ts("ite(false, a: bv<10>, b: bv<10>)", "b : bv<10>");

    // both true and false value are boolean constants
    ts("ite(c : bv<1>, true, false)", "c : bv<1>");
    ts("ite(c : bv<1>, true, true)", "true");
    ts("ite(c : bv<1>, false, true)", "not(c : bv<1>)");
    ts("ite(c : bv<1>, false, false)", "false");
}
