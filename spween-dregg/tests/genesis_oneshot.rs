//! ROOT CLOSURE — `genesis` is ONE-SHOT, not a universal post-deploy write-hatch.
//!
//! `compile_scene` must emit a `MethodIs { genesis }` case (the executor's dispatch is
//! method-default-deny, so the genesis turn needs a case to land on), and
//! `WorldCell::apply_raw` re-dispatches ANY method with no one-shot guard. Before this
//! fix the genesis case carried EMPTY constraints, so a POST-DEPLOY
//! `apply_raw("genesis", [SetField(slot, V)])` re-hit it and committed ARBITRARY writes
//! to ANY slot — a universal write-hatch on every compiled scene (dungeon/story/quest/
//! dialogue), previously sealed per-slot ~14 times.
//!
//! The root fix makes the genesis case a `0 → 1` transition on `GENESIS_DONE_EXT_KEY`
//! (`Equals{1} ∧ DeltaEquals{1}`): admissible exactly once (at deploy, sentinel still
//! field-zero), REFUSED for every later genesis turn — regardless of which slot a
//! stapled `SetField` targets, with NO per-slot `SlotChanged` dependence. Every
//! non-genesis case freezes the sentinel (`Immutable`), so no other method can reset it
//! to re-open genesis.
//!
//! These teeth DRIVE the fix through the real `EmbeddedExecutor`: the legit one-time
//! deploy/seed still works; a post-deploy genesis staple is refused REGARDLESS of slot;
//! a normal choice turn is unaffected; and the CANARY empties the genesis case's teeth
//! and shows the SAME staple COMMITS again (the hole reopens) — proving the teeth are
//! load-bearing, not decorative.

use std::sync::Arc;

use dregg_app_framework::{CellId, CellProgram, Effect, TransitionGuard, field_from_u64, symbol};
use spween_dregg::{
    CompiledStory, Driver, GENESIS_DONE_EXT_KEY, GENESIS_METHOD, HEAP_HATCH_METHOD, Value,
    WorldCell, WorldError, choice_method, compile_scene, parse,
};

/// A branching quest: `gate` (a gated choice + an UNGATED choice), `gold` a plain var
/// with NO per-slot guard — the clean staple target (the analogue of the documented
/// `apply_raw('genesis', [SetField(hp, 1000)])` vault attack).
const QUEST: &str = r#"---
id: genesis-oneshot
title: Genesis Oneshot
weight: 1
---

=== gate

You face a heavy locked door.

* [Force it open] { strength >= 5 }
  ~ strength -= 1
  -> hall

* [Look for a key]
  -> hall

=== hall

You are through, into the great hall.

* [Rest by the fire]
  ~ gold += 10
  -> END
"#;

fn scene() -> spween::Scene {
    parse(QUEST, "genesis-oneshot.scene").expect("scene parses")
}

fn deploy_strong(seed: u8) -> WorldCell {
    let mut w = WorldCell::deploy(&scene(), seed).expect("deploy");
    w.seed_var("strength", Value::Int(6));
    w
}

fn set_field(cell: CellId, index: u64, value: u64) -> Effect {
    Effect::SetField {
        cell,
        index,
        value: field_from_u64(value),
    }
}

/// The `gold` var's compiled field key (a plain var, no per-slot guard) — the staple
/// target that proves it is the GENESIS guard biting, not a leftover per-slot tooth.
fn gold_key(world: &WorldCell) -> u64 {
    world.story().var_key("gold").expect("gold has a slot")
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. Legit deploy seeds ONCE; genesis is then refused forever; a normal turn works.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn legit_deploy_seeds_then_genesis_is_a_refused_write_hatch() {
    let s = scene();
    // The LEGIT one-time deploy/seed: genesis runs, the world lands at the intro passage.
    let mut driver = Driver::start(deploy_strong(7), &s).expect("genesis (deploy) commits once");
    assert_eq!(
        driver.current_passage().as_deref(),
        Some("gate"),
        "the legit genesis seeded the intro passage"
    );
    assert_eq!(driver.world().read_var("gold"), 0, "gold born at zero");

    let world = driver.world();
    let cell = world.cell_id();
    let gold = gold_key(world);

    // THE ROOT HOLE, CLOSED: a POST-DEPLOY genesis turn stapling an arbitrary SetField
    // is REFUSED — the sentinel is already 1, so `Equals{1} ∧ DeltaEquals{1}` is jointly
    // unsatisfiable. `gold` has NO per-slot guard, so the refusal is the GENESIS guard.
    let refused = world.apply_raw(GENESIS_METHOD, vec![set_field(cell, gold, 1000)]);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "a post-deploy genesis staple is refused (one-shot genesis); got {refused:?}"
    );
    assert_eq!(
        world.read_var("gold"),
        0,
        "anti-ghost: the refused genesis staple committed nothing"
    );

    // Even a staple that ALSO tries to satisfy the sentinel (write it to 1) is refused:
    // old == 1 ⇒ Δ == 0 ≠ 1 (DeltaEquals) — the two teeth cannot both hold post-deploy.
    let refused2 = world.apply_raw(
        GENESIS_METHOD,
        vec![
            set_field(cell, gold, 1000),
            set_field(cell, GENESIS_DONE_EXT_KEY, 1),
        ],
    );
    assert!(
        matches!(refused2, Err(WorldError::Refused(_))),
        "a genesis staple that re-writes the sentinel is still refused; got {refused2:?}"
    );
    assert_eq!(world.read_var("gold"), 0, "anti-ghost");

    // A NORMAL method turn is unaffected: force the door (strength 6 >= 5) commits.
    driver
        .advance(0)
        .expect("a normal choice turn still commits");
    assert_eq!(driver.current_passage().as_deref(), Some("hall"));
    assert_eq!(driver.world().read_var("strength"), 5, "the choice ran");
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. CANARY — disable the genesis guard (empty its teeth) and the hole REOPENS.
// ─────────────────────────────────────────────────────────────────────────────

/// Return a copy of `story` with the genesis case's one-shot teeth REMOVED (the
/// pre-fix permissive shape) — the canary "disable the guard" toggle.
fn disable_genesis_guard(story: &CompiledStory) -> CompiledStory {
    let mut s = story.clone();
    if let CellProgram::Cases(cases) = &mut s.program {
        let genesis = symbol(GENESIS_METHOD);
        for case in cases.iter_mut() {
            if matches!(case.guard, TransitionGuard::MethodIs { method } if method == genesis) {
                case.constraints.clear();
            }
        }
    }
    s
}

#[test]
fn canary_disabling_the_genesis_guard_reopens_the_write_hatch() {
    let s = scene();
    let story = compile_scene(&s).expect("compile");

    // GUARD ENABLED (the shipped compiler output): the post-deploy staple is REFUSED.
    let fixed = Driver::start(
        WorldCell::deploy_compiled(Arc::new(story.clone()), 11).expect("deploy"),
        &s,
    )
    .expect("genesis")
    .finish()
    .0;
    let cell = fixed.cell_id();
    let gold = gold_key(&fixed);
    let refused = fixed.apply_raw(GENESIS_METHOD, vec![set_field(cell, gold, 1000)]);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "guard ENABLED: the staple is refused; got {refused:?}"
    );
    assert_eq!(
        fixed.read_var("gold"),
        0,
        "guard ENABLED: nothing committed"
    );

    // GUARD DISABLED (teeth emptied): the SAME staple COMMITS — the hole reopens.
    let disabled = disable_genesis_guard(&story);
    let holed = Driver::start(
        WorldCell::deploy_compiled(Arc::new(disabled), 11).expect("deploy"),
        &s,
    )
    .expect("genesis")
    .finish()
    .0;
    let cell = holed.cell_id();
    let gold = gold_key(&holed);
    holed
        .apply_raw(GENESIS_METHOD, vec![set_field(cell, gold, 1000)])
        .expect("guard DISABLED: the post-deploy genesis staple commits (hole reopened)");
    assert_eq!(
        holed.read_var("gold"),
        1000,
        "guard DISABLED: the universal write-hatch wrote gold = 1000 post-deploy"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. No OTHER method can reset the sentinel to re-open genesis (the freeze bites).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn no_other_method_can_reset_the_genesis_sentinel() {
    let s = scene();
    let world = Driver::start(deploy_strong(13), &s)
        .expect("genesis")
        .finish()
        .0;
    let cell = world.cell_id();
    assert_eq!(
        world.read_heap(GENESIS_DONE_EXT_KEY),
        Some(1),
        "the sentinel is set after the legit genesis"
    );

    // An UNGATED choice (`gate` index 1, no condition ⇒ empty gate teeth) cannot reset
    // the sentinel: the per-case `Immutable{sentinel}` freeze refuses the write. This is
    // exactly the "no per-slot dependence" property — an empty-gate choice is not a back
    // door to re-open genesis.
    let via_choice = world.apply_raw(
        &choice_method("gate", 1),
        vec![set_field(cell, GENESIS_DONE_EXT_KEY, 0)],
    );
    assert!(
        matches!(via_choice, Err(WorldError::Refused(_))),
        "an ungated choice cannot reset the sentinel (Immutable freeze); got {via_choice:?}"
    );

    // Nor can the heap hatch reset it.
    let via_hatch = world.apply_raw(
        HEAP_HATCH_METHOD,
        vec![set_field(cell, GENESIS_DONE_EXT_KEY, 0)],
    );
    assert!(
        matches!(via_hatch, Err(WorldError::Refused(_))),
        "the heap hatch cannot reset the sentinel; got {via_hatch:?}"
    );

    assert_eq!(
        world.read_heap(GENESIS_DONE_EXT_KEY),
        Some(1),
        "anti-ghost: the sentinel stayed set — genesis cannot be re-opened"
    );
}
