//! **VAR-OP-VAR gates lower to a real cross-key executor tooth.**
//!
//! A scene condition that compares two VARIABLES (`{ gold >= "$price" }`,
//! `{ hp <= "$cap" }`) — not a variable to a literal — lowers to a cross-slot
//! [`StateConstraint::FieldLteOther`] the verified executor re-checks on the turn's
//! post-state. So a cross-variable gate is a REAL tooth, not a handler courtesy: a
//! broke buyer whose `gold` is below the (dynamic) `price` is a `WorldError::Refused`
//! that commits nothing (anti-ghost), and a solvent buyer's SAME line commits.
//!
//! The current git-pinned `emberian/spween` grammar parses a comparison's RHS only as
//! a literal, so the var-reference rides the closest expressible form — a quoted string
//! with a `$` sigil (`"$price"`). A native `var op var` is a noted parser follow-up;
//! the lowering here already handles the relation, so it would be a pure parser widening.

use dregg_app_framework::{CellProgram, StateConstraint, TransitionGuard, symbol};
use spween_dregg::{
    CompiledStory, Value, WorldCell, WorldError, choice_method, compile_scene, parse,
};

/// A bazaar: buying the amulet is gated on `gold >= price` where BOTH are variables
/// (`price` is set by the world, hagglable), and the crossing-priced purchase cannot be
/// expressed as a fixed literal. The buy choice does not touch `gold`/`price`, so its
/// gate lifts exactly (clamp-safe: both deltas zero).
const BAZAAR: &str = r#"---
id: bazaar
title: The Bazaar
weight: 1
---

=== stall

~ price = 20

A merchant eyes your purse and names a price.

* [Buy the amulet] { gold >= "$price" }
  ~ bought = 1
  -> END

* [Haggle the price down]
  ~ price -= 5
  -> stall
"#;

/// A ward: you may pass only while your `hp` is at or below the ward's `cap` (an upper
/// cross-variable bound — the `<=` direction). Exercises the other operand order.
const WARD: &str = r#"---
id: ward
title: The Ward
weight: 1
---

=== gate

~ cap = 8

A ward hums; it suffers only the weakened to pass.

* [Slip through] { hp <= "$cap" }
  ~ passed = 1
  -> END
"#;

fn scene(src: &str, name: &str) -> spween::Scene {
    parse(src, name).expect("scene parses")
}

/// The `idx`-th choice in `passage` (the same order `apply_choice`'s index selects).
fn nth_choice(scene: &spween::Scene, passage: &str, idx: usize) -> spween::Choice {
    let p = scene
        .passages
        .iter()
        .find(|p| p.name.as_str() == passage)
        .expect("passage exists");
    p.content
        .iter()
        .filter_map(|c| match c {
            spween::PassageContent::Choice(ch) => Some(ch),
            _ => None,
        })
        .nth(idx)
        .cloned()
        .expect("choice exists")
}

/// Look up the constraints installed on the case for `(passage, choice)`.
fn case_constraints(story: &CompiledStory, passage: &str, choice: usize) -> Vec<StateConstraint> {
    let m = symbol(&choice_method(passage, choice));
    let CellProgram::Cases(cases) = &story.program else {
        panic!("program is Cases");
    };
    cases
        .iter()
        .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == m))
        .map(|c| c.constraints.clone())
        .unwrap_or_default()
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. The lowering: a var-op-var gate becomes a FieldLteOther cross-slot tooth.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn ge_var_op_var_lowers_to_field_lte_other() {
    let s = scene(BAZAAR, "bazaar.scene");
    let story = compile_scene(&s).expect("bazaar compiles");

    // Both operands got real slots (the RHS var `price` was registered by the gate).
    let gold = *story.var_slots.get("gold").expect("gold has a slot") as u8;
    let price = *story.var_slots.get("price").expect("price has a slot") as u8;

    // `gold >= price` (buy choice, neither var touched) ⟺ `new[price] <= new[gold] + 0`.
    let buy = case_constraints(&story, "stall", 0);
    assert!(
        buy.iter().any(|c| matches!(c,
            StateConstraint::FieldLteOther { index, other, delta }
                if *index == price && *other == gold && *delta == 0)),
        "buy gate lowers to FieldLteOther(price <= gold + 0); got {buy:?}"
    );

    // The gate lowered FULLY — no residual handler lean.
    assert_eq!(
        story.fully_gated.get(&choice_method("stall", 0)),
        Some(&true),
        "the var-op-var gate is fully executor-lowered"
    );
}

#[test]
fn le_var_op_var_lowers_with_swapped_operands() {
    let s = scene(WARD, "ward.scene");
    let story = compile_scene(&s).expect("ward compiles");
    let hp = *story.var_slots.get("hp").expect("hp slot") as u8;
    let cap = *story.var_slots.get("cap").expect("cap slot") as u8;

    // `hp <= cap` ⟺ `new[hp] <= new[cap] + 0` — index/other swapped from the Ge case.
    let pass = case_constraints(&story, "gate", 0);
    assert!(
        pass.iter().any(|c| matches!(c,
            StateConstraint::FieldLteOther { index, other, delta }
                if *index == hp && *other == cap && *delta == 0)),
        "pass gate lowers to FieldLteOther(hp <= cap + 0); got {pass:?}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. The gate BITES on the real executor (non-vacuous: refused then admitted).
// ─────────────────────────────────────────────────────────────────────────────

/// THE HARD GATE: a broke buyer (`gold < price`) is REFUSED by the executor — a real
/// `WorldError::Refused` that commits nothing (anti-ghost: `bought` stays 0). A solvent
/// buyer's SAME line commits. Non-vacuous: identical line, refused then admitted, only
/// the cross-variable relation differs.
#[test]
fn cross_var_gate_bites_broke_buyer_refused_solvent_commits() {
    let s = scene(BAZAAR, "bazaar.scene");
    let buy = nth_choice(&s, "stall", 0);

    // Broke: gold 10 < price 20 → the executor REFUSES the buy.
    let mut broke = WorldCell::deploy(&s, 40).expect("deploy");
    broke.seed_var("price", Value::Int(20));
    broke.seed_var("gold", Value::Int(10));
    let refused = broke.apply_choice("stall", 0, &buy);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "a broke buyer (gold 10 < price 20) is refused by the executor, got {refused:?}"
    );
    assert_eq!(broke.read_var("bought"), 0, "anti-ghost: nothing bought");

    // Solvent: gold 50 >= price 20 → the SAME line commits.
    let mut solvent = WorldCell::deploy(&s, 41).expect("deploy");
    solvent.seed_var("price", Value::Int(20));
    solvent.seed_var("gold", Value::Int(50));
    solvent
        .apply_choice("stall", 0, &buy)
        .expect("a solvent buyer's purchase commits");
    assert_eq!(solvent.read_var("bought"), 1, "the amulet is bought");

    // The boundary (gold == price) satisfies `>=`.
    let mut exact = WorldCell::deploy(&s, 42).expect("deploy");
    exact.seed_var("price", Value::Int(20));
    exact.seed_var("gold", Value::Int(20));
    exact
        .apply_choice("stall", 0, &buy)
        .expect("gold == price satisfies the >= gate");
    assert_eq!(exact.read_var("bought"), 1);
}

/// The gate tracks a DYNAMIC threshold: after haggling `price` down, a buyer the ward
/// once refused now passes — the tooth reads the CURRENT `price` slot, not a frozen
/// literal. This is the whole point of var-op-var: neither operand is a compile-time
/// constant.
#[test]
fn haggling_lowers_the_dynamic_threshold_and_the_gate_follows() {
    let s = scene(BAZAAR, "bazaar.scene");
    let buy = nth_choice(&s, "stall", 0);
    let haggle = nth_choice(&s, "stall", 1);

    let mut w = WorldCell::deploy(&s, 43).expect("deploy");
    w.seed_var("price", Value::Int(20));
    w.seed_var("gold", Value::Int(18));

    // gold 18 < price 20 → refused.
    assert!(matches!(
        w.apply_choice("stall", 0, &buy),
        Err(WorldError::Refused(_))
    ));

    // Haggle twice: price 20 -> 15 -> 10. Now gold 18 >= price 10.
    w.apply_choice("stall", 1, &haggle).expect("haggle once");
    w.apply_choice("stall", 1, &haggle).expect("haggle twice");
    assert_eq!(w.read_var("price"), 10, "the price came down");

    w.apply_choice("stall", 0, &buy)
        .expect("the haggled-down price is now affordable");
    assert_eq!(w.read_var("bought"), 1);
}

/// The `<=` direction bites too: a heavy traveller (`hp > cap`) is barred by the ward,
/// a weakened one (`hp <= cap`) slips through. Same line, refused then admitted.
#[test]
fn upper_bound_cross_var_gate_bites() {
    let s = scene(WARD, "ward.scene");
    let slip = nth_choice(&s, "gate", 0);

    // hp 12 > cap 8 → refused.
    let mut hale = WorldCell::deploy(&s, 44).expect("deploy");
    hale.seed_var("cap", Value::Int(8));
    hale.seed_var("hp", Value::Int(12));
    assert!(matches!(
        hale.apply_choice("gate", 0, &slip),
        Err(WorldError::Refused(_))
    ));
    assert_eq!(hale.read_var("passed"), 0, "anti-ghost: the ward held");

    // hp 5 <= cap 8 → passes.
    let mut weak = WorldCell::deploy(&s, 45).expect("deploy");
    weak.seed_var("cap", Value::Int(8));
    weak.seed_var("hp", Value::Int(5));
    weak.apply_choice("gate", 0, &slip)
        .expect("a weakened traveller slips through the ward");
    assert_eq!(weak.read_var("passed"), 1);
}
