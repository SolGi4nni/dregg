//! REPAIR #4 — the heap escape hatch ([`WorldCell::apply_raw`]) is DISPATCHABLE.
//!
//! `compile_scene` builds a `CellProgram::Cases` with a `MethodIs` case per choice
//! plus the genesis case. The executor's dispatch is **method-default-deny**: once a
//! program has any `MethodIs` case, an action whose method matches none is refused as
//! `NoTransitionCaseMatched` — so a raw HEAP-keyed turn (a NOVEL method that no choice
//! case names) was dead on arrival, and `apply_raw`/`read_heap` had zero coverage.
//!
//! These teeth DRIVE the fix through the real [`dregg_app_framework::EmbeddedExecutor`]:
//! the reserved `HEAP_HATCH_METHOD` case revives the hatch (heap write admitted iff the
//! confinement teeth pass), while an unknown/forged method is STILL refused (the
//! dispatch default-deny is not weakened) — and the FIRST test empirically DISPROVES
//! the "just add an `Always` catch-all" fix: an `Always` case does not dispatch a
//! novel-method turn.

use std::sync::Arc;

use dregg_app_framework::{
    CellId, CellProgram, Effect, TransitionCase, TransitionGuard, field_from_u64, symbol,
};
use spween_dregg::{
    CompiledStory, Driver, GENESIS_METHOD, HEAP_HATCH_METHOD, PASSAGE_SLOT, STATE_SLOTS, WorldCell,
    WorldError, choice_method, parse,
};

/// A raw `Effect::SetField` into a HEAP key (`index >= STATE_SLOTS`, routed into the
/// cell's committed `fields_map`).
fn heap_effect(cell: CellId, key: u64, value: u64) -> Effect {
    Effect::SetField {
        cell,
        index: key,
        value: field_from_u64(value),
    }
}

/// A raw `Effect::SetField` into a REGISTER slot (`index < STATE_SLOTS`).
fn slot_effect(cell: CellId, index: u64, value: u64) -> Effect {
    Effect::SetField {
        cell,
        index,
        value: field_from_u64(value),
    }
}

/// A one-passage scene: genesis enters `start` (`PASSAGE_SLOT = 0`), one choice.
const MINI: &str = r#"---
id: mini-hatch
title: Mini Hatch
weight: 1
---

=== start

A quiet room with a chest.

* [Wait]
  -> END
"#;

fn scene() -> spween::Scene {
    parse(MINI, "mini-hatch.scene").expect("mini scene parses")
}

// ─────────────────────────────────────────────────────────────────────────────
// STEP 1 — REPRO / DISPROOF: an `Always` catch-all does NOT revive the hatch.
//
// This is the fix the roadmap text proposed. It fails: `TransitionGuard::Always`
// is NOT method-dispatching, so `any_dispatch_case && !any_dispatch_matched` in the
// executor still refuses a novel-method turn. We build that exact program by hand and
// drive it — proving the refusal is the DISPATCH default-deny (the `genesis` MethodIs
// case admits the SAME heap effect under its own method).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn always_catchall_does_not_dispatch_a_novel_heap_method() {
    // program = [ MethodIs(genesis), Always([]) ] — the naive "add a catch-all" shape.
    let story = CompiledStory {
        scene_id: "always-disproof".into(),
        var_slots: Default::default(),
        has_slots: Default::default(),
        passage_index: Default::default(),
        program: CellProgram::Cases(vec![
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol(GENESIS_METHOD),
                },
                constraints: vec![],
            },
            TransitionCase {
                guard: TransitionGuard::Always,
                constraints: vec![],
            },
        ]),
        fully_gated: Default::default(),
    };
    let world = WorldCell::deploy_compiled(Arc::new(story), 99).expect("deploy");
    let cell = world.cell_id();
    let key = STATE_SLOTS as u64 + 4;

    // A novel method whose heap write the Always case "matches" — but the dispatch
    // default-deny refuses it: the Always case never satisfies "a dispatch case matched".
    let refused = world.apply_raw("inv/add", vec![heap_effect(cell, key, 1)]);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "an Always catch-all does NOT dispatch a novel-method heap turn (dispatch \
         default-deny still bites): {refused:?}"
    );
    assert_eq!(
        world.read_heap(key),
        None,
        "anti-ghost: the refused heap turn committed nothing"
    );

    // Non-vacuity: the SAME heap effect under the `genesis` dispatch method DOES commit,
    // so the only thing refusing `inv/add` is the method default-deny.
    world
        .apply_raw(GENESIS_METHOD, vec![heap_effect(cell, key, 1)])
        .expect("the genesis MethodIs case dispatches the identical heap effect");
    assert_eq!(world.read_heap(key), Some(1));
}

// ─────────────────────────────────────────────────────────────────────────────
// STEP 2 — FIX: `compile_scene` installs the reserved `HEAP_HATCH_METHOD` case so a
// raw heap turn DISPATCHES, confined to the heap; unknown/forged methods stay refused.
// ─────────────────────────────────────────────────────────────────────────────

/// The heap hatch is ALIVE: a `>16`-slot inventory rides `apply_raw` and `read_heap`
/// reads it back, driven as a real cap-bounded turn after genesis.
#[test]
fn heap_hatch_dispatches_and_scales_past_the_register_slots() {
    let s = scene();
    let world = WorldCell::deploy(&s, 7).expect("deploy");
    let driver = Driver::start(world, &s).expect("genesis runs");
    let world = driver.world();
    let cell = world.cell_id();

    // Stash 24 items into heap keys 16..40 — beyond the 16 register slots. Each is a
    // real committed turn through the reserved hatch case; the heap holds the whole
    // collection. (Before the fix, every one of these was NoTransitionCaseMatched.)
    for k in (STATE_SLOTS as u64)..(STATE_SLOTS as u64 + 24) {
        world
            .apply_raw(HEAP_HATCH_METHOD, vec![heap_effect(cell, k, k)])
            .unwrap_or_else(|e| panic!("heap stash at key {k} dispatches and commits: {e:?}"));
        assert_eq!(world.read_heap(k), Some(k), "heap holds item {k}");
    }
    // A key never written reads back absent (heap: absent ≠ present-zero).
    assert_eq!(world.read_heap(9999), None);
}

/// The hatch is CONFINED to the heap: a forged hatch turn that overwrites a REGISTER
/// slot (e.g. `PASSAGE_SLOT` to teleport) is refused by the `Immutable` confinement
/// teeth — the catch-all does not become a write-anywhere hole.
#[test]
fn heap_hatch_cannot_overwrite_a_register_slot() {
    let s = scene();
    let world = WorldCell::deploy(&s, 8).expect("deploy");
    let driver = Driver::start(world, &s).expect("genesis runs");
    let world = driver.world();
    let cell = world.cell_id();

    let before = world.snapshot()[PASSAGE_SLOT];
    let refused = world.apply_raw(
        HEAP_HATCH_METHOD,
        vec![slot_effect(cell, PASSAGE_SLOT as u64, 7)],
    );
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "a hatch turn that writes a register slot is refused (Immutable confinement): \
         {refused:?}"
    );
    assert_eq!(
        world.snapshot()[PASSAGE_SLOT],
        before,
        "anti-ghost: the passage slot was not teleported"
    );
}

/// The dispatch default-deny is NOT weakened: an UNKNOWN method and a FORGED CHOICE
/// method (a choice index that names no case) are STILL refused — refused by their own
/// case's absence, not admitted by the hatch.
#[test]
fn unknown_and_forged_choice_methods_still_refused() {
    let s = scene();
    let world = WorldCell::deploy(&s, 9).expect("deploy");
    let driver = Driver::start(world, &s).expect("genesis runs");
    let world = driver.world();
    let cell = world.cell_id();
    let key = STATE_SLOTS as u64 + 1;

    // An arbitrary novel method that is neither a choice, genesis, nor the hatch.
    let unknown = world.apply_raw("inv/add", vec![heap_effect(cell, key, 1)]);
    assert!(
        matches!(unknown, Err(WorldError::Refused(_))),
        "an unknown method is still refused (default-deny intact): {unknown:?}"
    );

    // A FORGED choice method: `start` has one choice (index 0); index 9 names no case.
    let forged = world.apply_raw(
        &choice_method("start", 9),
        vec![slot_effect(cell, PASSAGE_SLOT as u64, 3)],
    );
    assert!(
        matches!(forged, Err(WorldError::Refused(_))),
        "a forged choice method is refused by its own case's absence: {forged:?}"
    );

    assert_eq!(world.read_heap(key), None, "anti-ghost: nothing committed");
}
