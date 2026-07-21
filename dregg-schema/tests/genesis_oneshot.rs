//! ROOT CLOSURE — a schema's `genesis` (seed) method is ONE-SHOT, not a universal
//! post-deploy write-hatch. (Ported from `spween-dregg`'s `genesis_oneshot.rs`.)
//!
//! [`emit_program`] must emit a `MethodIs { genesis }` case (the executor's dispatch is
//! method-default-deny, so a seed turn needs a case to land on), and
//! `WorldCell::apply_raw` re-dispatches ANY method with no one-shot guard. Before this
//! fix the genesis case carried EMPTY constraints, so a POST-DEPLOY
//! `seed()` / `apply_raw("genesis", [SetField(slot, V)])` re-hit it and committed
//! ARBITRARY writes to ANY slot — e.g. `hp = 1000`, past the `Stat` cap the `move` teeth
//! enforce — routing around every component invariant. A universal write-hatch on every
//! deployed schema.
//!
//! The fix makes the genesis case a `0 → 1` transition on `GENESIS_DONE_EXT_KEY`
//! (`Equals{1} ∧ DeltaEquals{1}`): admissible exactly once (at the first seed, sentinel
//! still field-zero), REFUSED for every later genesis turn — regardless of which slot a
//! stapled `SetField` targets, with NO per-slot dependence. The `move` case freezes the
//! sentinel (`Immutable`), so no move can reset it to re-open genesis.
//!
//! Because a schema game IS a `spween_dregg::WorldCell`, this reuses spween's world
//! machinery verbatim: `program_requires_genesis_sentinel` keys off the INSTALLED
//! PROGRAM (a genesis case carrying a `HeapField` over `GENESIS_DONE_EXT_KEY`), so
//! `deploy_compiled` births the sentinel at field-zero and `commit` injects the `0 → 1`
//! write on the `"genesis"` method — no change on the world side.
//!
//! These teeth DRIVE the fix through the real executor: the legit one-time seed works; a
//! post-deploy genesis staple is refused REGARDLESS of slot (`hp` has no per-slot tooth
//! under genesis, so the refusal is the GENESIS guard); a normal move is unaffected; no
//! move can reset the sentinel; and the CANARY empties the genesis case's teeth and shows
//! the SAME staple COMMITS again (the hole reopens) — proving the teeth are load-bearing.

use std::sync::Arc;

use dregg_app_framework::{CellId, CellProgram, Effect, TransitionGuard, field_from_u64, symbol};
use dregg_schema::{
    GENESIS_METHOD, GameError, MOVE_METHOD, SchemaGame, Slot, check_layout, compiled_story,
    descent_schema,
};
use spween_dregg::{CompiledStory, GENESIS_DONE_EXT_KEY, WorldCell, WorldError};

// The seeded baseline (mirrors tests/refinement.rs::fresh).
const HP: u64 = 20;
const FLOOR: u64 = 5;
const GOLD: u64 = 10;
const OWNER: u64 = 1000;
const SHIELD: u64 = 5;
const ITEMS: u64 = 3;

fn set_field(cell: CellId, index: u64, value: u64) -> Effect {
    Effect::SetField {
        cell,
        index,
        value: field_from_u64(value),
    }
}

/// `hp`'s register index (a `Stat` capped at 20). It carries NO per-slot tooth under the
/// genesis case, so a refused genesis staple on it is the GENESIS guard biting — and a
/// value of 1000 (past the `move` cap) makes the hatch's power vivid.
fn hp_index() -> u64 {
    let layout = check_layout(&descent_schema()).expect("layout");
    match layout.resolve("hp").expect("hp resolves") {
        Slot::Register(r) => u64::from(r),
        Slot::Heap(_) => panic!("hp is a register stat"),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. Legit seed seeds ONCE; genesis is then a refused write-hatch; a move still works.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn legit_seed_then_genesis_is_a_refused_write_hatch() {
    let game = SchemaGame::deploy(descent_schema(), 7).expect("deploy");

    // The LEGIT one-time seed under the permissive genesis method.
    game.seed()
        .set("hp", HP)
        .set("floor", FLOOR)
        .set("gold", GOLD)
        .set("owner", OWNER)
        .set("shield", SHIELD)
        .set("items", ITEMS)
        .commit()
        .expect("genesis seed commits once");
    assert_eq!(game.get("hp"), Some(HP), "seed landed");

    // THE ROOT HOLE, CLOSED: a POST-DEPLOY genesis staple writing `hp = 1000` (past the
    // `Stat` cap of 20 the `move` teeth enforce) is REFUSED — the sentinel is already 1,
    // so `Equals{1} ∧ DeltaEquals{1}` is jointly unsatisfiable. `hp` has NO per-slot
    // tooth under genesis, so the refusal is the GENESIS guard, not a leftover cap.
    let refused = game.seed().set("hp", 1000).commit();
    assert!(
        matches!(refused, Err(GameError::World(WorldError::Refused(_)))),
        "a post-deploy genesis staple is refused (one-shot genesis); got {refused:?}"
    );
    assert_eq!(
        game.get("hp"),
        Some(HP),
        "anti-ghost: the refused genesis staple committed nothing"
    );

    // A NORMAL move is unaffected: hp within [0, 20] commits.
    game.move_()
        .set("hp", 15)
        .commit()
        .expect("a normal move still commits");
    assert_eq!(game.get("hp"), Some(15), "the move ran");
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. CANARY — disable the genesis guard (empty its teeth) and the hole REOPENS.
// ─────────────────────────────────────────────────────────────────────────────

/// Return a copy of `story` with the genesis case's one-shot teeth REMOVED (the pre-fix
/// permissive shape). With no `HeapField` over `GENESIS_DONE_EXT_KEY` in the genesis
/// case, spween's `program_requires_genesis_sentinel` returns false, so the world births
/// no sentinel and injects no `0 → 1` write — the exact pre-fix behaviour.
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

/// Deploy a story on a raw world, seed `hp` once (the legit genesis), and return the
/// world ready for a post-deploy staple.
fn deploy_and_seed(story: CompiledStory, seed: u8) -> WorldCell {
    let cell_seed = story.clone();
    let world = WorldCell::deploy_compiled(Arc::new(cell_seed), seed).expect("deploy");
    let cell = world.cell_id();
    world
        .apply_raw(GENESIS_METHOD, vec![set_field(cell, hp_index(), HP)])
        .expect("the legit one-time seed commits");
    world
}

#[test]
fn canary_disabling_the_genesis_guard_reopens_the_write_hatch() {
    let schema = descent_schema();
    let layout = check_layout(&schema).expect("layout");
    let story = compiled_story(&schema, &layout).expect("story");
    let hp = hp_index();

    // GUARD ENABLED (the shipped emitter output): the post-deploy staple is REFUSED.
    let fixed = deploy_and_seed(story.clone(), 11);
    let cell = fixed.cell_id();
    let refused = fixed.apply_raw(GENESIS_METHOD, vec![set_field(cell, hp, 1000)]);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "guard ENABLED: the staple is refused; got {refused:?}"
    );
    assert_eq!(fixed.read_var("hp"), HP, "guard ENABLED: nothing committed");

    // GUARD DISABLED (teeth emptied): the SAME staple COMMITS — the hole reopens.
    let disabled = disable_genesis_guard(&story);
    let holed = deploy_and_seed(disabled, 11);
    let cell = holed.cell_id();
    holed
        .apply_raw(GENESIS_METHOD, vec![set_field(cell, hp, 1000)])
        .expect("guard DISABLED: the post-deploy genesis staple commits (hole reopened)");
    assert_eq!(
        holed.read_var("hp"),
        1000,
        "guard DISABLED: the universal write-hatch wrote hp = 1000 past the cap, post-deploy"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. No move can reset the genesis sentinel to re-open genesis (the freeze bites).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn no_move_can_reset_the_genesis_sentinel() {
    let schema = descent_schema();
    let layout = check_layout(&schema).expect("layout");
    let story = compiled_story(&schema, &layout).expect("story");
    let world = deploy_and_seed(story, 13);
    let cell = world.cell_id();

    assert_eq!(
        world.read_heap(GENESIS_DONE_EXT_KEY),
        Some(1),
        "the sentinel is set after the legit seed"
    );

    // A move that tries to reset the sentinel to 0 is REFUSED by the `Immutable` freeze
    // on the move case — a move is not a back door to re-open genesis.
    let via_move = world.apply_raw(MOVE_METHOD, vec![set_field(cell, GENESIS_DONE_EXT_KEY, 0)]);
    assert!(
        matches!(via_move, Err(WorldError::Refused(_))),
        "a move cannot reset the sentinel (Immutable freeze); got {via_move:?}"
    );
    assert_eq!(
        world.read_heap(GENESIS_DONE_EXT_KEY),
        Some(1),
        "anti-ghost: the sentinel stayed set — genesis cannot be re-opened"
    );
}
