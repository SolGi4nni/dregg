//! # `dungeon-on-dregg` — a dungeon crawl on the REAL dregg executor
//!
//! The Phase-A de-risk vertical slice of the collective-fiction rebuild. It hosts a
//! minimal dungeon (3 rooms, 1 item, 1 gated exit) on `spween-dregg`'s **real**
//! [`WorldCell`](spween_dregg::WorldCell) — the same `EmbeddedExecutor`, cell,
//! [`CellProgram`](dregg_app_framework::CellProgram) and [`TurnReceipt`] the flagship
//! substrate uses — NOT `attested-dm`'s toy `WorldCell`/blake3 ledger.
//!
//! ## The mapping (dungeon → real cell / turn / CellProgram)
//!
//! The whole dungeon is **one dregg cell**. Its owned state (`fields[16]`) carries:
//!
//! | cell slot | meaning | dungeon role |
//! |-----------|---------|--------------|
//! | [`PASSAGE_SLOT`](spween_dregg::PASSAGE_SLOT) (0) | current passage index | **the player's room** (the program counter) |
//! | `has_lantern` slot | 0/1 | **the item** — 1 once grabbed |
//! | `depth` slot | int | descent counter (a real state write on the gated turn) |
//! | `gold` slot | int | the hoard |
//!
//! A **move** is one signed action the executor admits: its `spween::Effect`s become
//! `Effect::SetField` writes on the cell and its navigation advances [`PASSAGE_SLOT`].
//! Taking the lantern is `SetField(has_lantern, 1)`; descending is `SetField(depth, +1)`
//! then the room advance. The move is a real cap-bounded turn (the driver holds a
//! `Signature` cap to the world-cell) that lands a real [`TurnReceipt`].
//!
//! ## The gate is an executor-enforced `StateConstraint` tooth (not app code)
//!
//! The compiler lowers the gated exit's condition `{ has_lantern >= 1 }` into a real
//! [`StateConstraint::FieldGte`](dregg_app_framework::StateConstraint) installed on
//! the cell as a [`CellProgram`] case, guarded by the descend move's dispatch method.
//! The verified executor re-checks that constraint on the move's **post-state**: a
//! descent with `has_lantern == 0` fails the `FieldGte` and is REFUSED in-band —
//! nothing commits, no receipt. The rule is a kernel predicate, not a client courtesy.
//!
//! This is the salvaged `attested-dm` design (`exit down -> dark_stair requires item
//! lantern`) rebuilt on the real substrate: the *content* is reused, the *substrate*
//! is spween-dregg's real cell/turn — never attested-dm's toy.
//!
//! [`TurnReceipt`]: dregg_app_framework::TurnReceipt

use dregg_app_framework::{CellProgram, StateConstraint, TransitionGuard, symbol};
use spween::{Choice, PassageContent, Scene};
use spween_dregg::{CompiledStory, Value, WorldCell, choice_method, compile_scene, parse};

/// The dungeon, expressed in the spween narrative DSL. Three rooms
/// (`shore` → `antechamber` → `dark_stair`), one item (the brass lantern), one gated
/// exit (`antechamber` → `dark_stair`, requiring the lantern).
///
/// Salvaged from `attested-dm`'s `.dungeon` content shape — `exit down -> dark_stair
/// requires item lantern` — but every mechanic here lowers to a REAL executor tooth.
pub const DUNGEON: &str = r#"---
id: salt-shore-descent
title: The Salt Shore Descent
weight: 1
---

=== shore

Cold surf hisses over black sand. A brass lantern lies half-buried at the tide line.
A low arch opens north into an antechamber; beyond it a stair spirals into the dark.

* [Take the brass lantern and step north]
  ~ has_lantern = 1
  -> antechamber

* [Leave it and step north empty-handed]
  -> antechamber

=== antechamber

A round stone room. The stair drops away into pitch black — no light means no descent.

* [Descend the dark stair] { has_lantern >= 1 }
  ~ depth += 1
  -> dark_stair

* [Retreat to the shore]
  -> shore

=== dark_stair

Your lantern throws long shapes across wet, salt-crusted steps. Gold glints below.

* [Claim the sunken hoard]
  ~ gold += 500
  -> END
"#;

// ── Room / choice coordinates (the driver + verifier speak in these) ────────────

/// The opening room: the lantern lies here.
pub const ROOM_SHORE: &str = "shore";
/// The gate room: its down-stair is gated on the lantern.
pub const ROOM_ANTECHAMBER: &str = "antechamber";
/// The treasure room (terminal).
pub const ROOM_DARK_STAIR: &str = "dark_stair";

/// `shore`: take the lantern (sets `has_lantern = 1`), then north.
pub const CH_TAKE_LANTERN: usize = 0;
/// `shore`: step north empty-handed (no item).
pub const CH_LEAVE_LANTERN: usize = 1;
/// `antechamber`: the GATED descent — refused unless `has_lantern >= 1`.
pub const CH_DESCEND: usize = 0;
/// `antechamber`: retreat back to the shore (ungated).
pub const CH_RETREAT: usize = 1;
/// `dark_stair`: claim the hoard (ends the dungeon).
pub const CH_CLAIM: usize = 0;

/// Parse the dungeon scene.
pub fn scene() -> Scene {
    parse(DUNGEON, "salt-shore-descent.scene").expect("the dungeon scene parses")
}

/// Deploy the dungeon as a real world-cell (compile → birth cell → install the
/// `CellProgram` gate teeth). Deterministic in `seed`, so a re-deploy reproduces the
/// same cell identity + state hashes (what the replay verifier leans on).
pub fn deploy(seed: u8) -> WorldCell {
    WorldCell::deploy(&scene(), seed).expect("the dungeon deploys onto a real world-cell")
}

/// Compile the scene to its world-cell descriptor (slot layout + installed program).
pub fn compiled() -> CompiledStory {
    compile_scene(&scene()).expect("the dungeon compiles")
}

/// Pull a specific `Choice` out of the parsed scene — the exact value
/// [`WorldCell::apply_choice`](spween_dregg::WorldCell::apply_choice) drives directly
/// at the executor (bypassing the client-side runtime so the executor gate is the
/// SOLE referee).
pub fn choice_at(scene: &Scene, room: &str, index: usize) -> Choice {
    let passage = scene
        .passages
        .iter()
        .find(|p| p.name.as_str() == room)
        .unwrap_or_else(|| panic!("room `{room}` exists"));
    passage
        .content
        .iter()
        .filter_map(|c| match c {
            PassageContent::Choice(ch) => Some(ch),
            _ => None,
        })
        .nth(index)
        .cloned()
        .unwrap_or_else(|| panic!("room `{room}` has a choice {index}"))
}

/// Introspect the installed program and return the executor-enforced `StateConstraint`s
/// guarding the descend move — proof the gate is a real kernel predicate. Returns the
/// constraints attached to the case guarded by the descend move's dispatch method.
pub fn descend_gate_constraints(story: &CompiledStory) -> Vec<StateConstraint> {
    let method = symbol(&choice_method(ROOM_ANTECHAMBER, CH_DESCEND));
    let CellProgram::Cases(cases) = &story.program else {
        return Vec::new();
    };
    cases
        .iter()
        .find(|case| matches!(&case.guard, TransitionGuard::MethodIs { method: m } if *m == method))
        .map(|case| case.constraints.clone())
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use spween_dregg::{Driver, StepPos, VerifyBreak, WorldError, verify, verify_chain_linkage};

    /// The compiler lowers the gated exit into a REAL executor tooth — a `FieldGte`
    /// on the lantern slot, guarded by the descend move's method. The gate is a kernel
    /// predicate, not app bookkeeping.
    #[test]
    fn gate_lowers_to_a_real_fieldgte_tooth() {
        let story = compiled();

        // The lantern and passage got distinct cell slots.
        let lantern_slot = *story.var_slots.get("has_lantern").expect("lantern slot");
        assert!(lantern_slot >= 1, "lantern is not the passage slot");

        // The descend gate fully lowered to executor constraints (no handler-only clause).
        let m = choice_method(ROOM_ANTECHAMBER, CH_DESCEND);
        assert_eq!(
            story.fully_gated.get(&m),
            Some(&true),
            "the descend gate is fully executor-enforced"
        );

        // And it is exactly a FieldGte on the lantern slot with threshold 1.
        let constraints = descend_gate_constraints(&story);
        assert!(
            constraints.iter().any(|c| matches!(
                c,
                StateConstraint::FieldGte { index, value }
                    if *index as usize == lantern_slot
                        && *value == dregg_app_framework::field_from_u64(1)
            )),
            "descend gate is FieldGte(has_lantern, 1); got {constraints:?}"
        );
    }

    /// THE HARD GATE (illegal move): walk to the gate empty-handed, then drive the
    /// descend move DIRECTLY at the executor. The real executor REFUSES it (its
    /// `FieldGte` gate fails on the post-state) — and nothing commits (anti-ghost:
    /// still in the antechamber, no depth, no lantern).
    #[test]
    fn illegal_descent_is_a_real_executor_refusal_that_commits_nothing() {
        let s = scene();
        let world = deploy(3);

        // Walk to the gate room WITHOUT the lantern (the ungated "leave it" move).
        let leave = choice_at(&s, ROOM_SHORE, CH_LEAVE_LANTERN);
        world
            .apply_choice(ROOM_SHORE, CH_LEAVE_LANTERN, &leave)
            .expect("stepping north empty-handed is ungated and commits");
        assert_eq!(world.read_passage(), Some(1), "now in the antechamber");
        assert_eq!(world.read_var("has_lantern"), 0, "no lantern held");

        // Drive the gated descend at the executor — with has_lantern == 0 it is REFUSED.
        let descend = choice_at(&s, ROOM_ANTECHAMBER, CH_DESCEND);
        let refused = world.apply_choice(ROOM_ANTECHAMBER, CH_DESCEND, &descend);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "an unlit descent is refused by the real executor, got {refused:?}"
        );

        // Anti-ghost — the refused turn committed NOTHING.
        assert_eq!(world.read_passage(), Some(1), "still in the antechamber");
        assert_eq!(world.read_var("depth"), 0, "depth did not advance");
        assert_eq!(world.read_var("has_lantern"), 0, "lantern still not held");
    }

    /// The SAME descend move, WITH the lantern, commits — and its receipt chains onto
    /// the take-lantern move's receipt (`pre_state_hash == prev.post_state_hash`).
    #[test]
    fn legal_descent_commits_and_the_receipt_chain_links() {
        let s = scene();
        let world = deploy(4);

        let take = choice_at(&s, ROOM_SHORE, CH_TAKE_LANTERN);
        let r1 = world
            .apply_choice(ROOM_SHORE, CH_TAKE_LANTERN, &take)
            .expect("taking the lantern commits");
        assert_eq!(world.read_var("has_lantern"), 1);

        let descend = choice_at(&s, ROOM_ANTECHAMBER, CH_DESCEND);
        let r2 = world
            .apply_choice(ROOM_ANTECHAMBER, CH_DESCEND, &descend)
            .expect("with the lantern, the descent commits");
        assert_eq!(world.read_passage(), Some(2), "descended to the dark stair");
        assert_eq!(world.read_var("depth"), 1);

        // The real receipt chain: the descend receipt's pre-state IS the take-lantern
        // receipt's post-state (an un-retconnable hash link).
        assert_ne!(r1.turn_hash, [0u8; 32], "take is a genuine committed turn");
        assert_ne!(
            r2.turn_hash, [0u8; 32],
            "descend is a genuine committed turn"
        );
        assert_eq!(
            r2.pre_state_hash, r1.post_state_hash,
            "descend.pre == take.post — the receipts chain"
        );
    }

    /// A full playthrough over the STOCK runtime is a real receipt chain, and it
    /// re-verifies (chain linkage + replay). A retconned choice fails replay.
    #[test]
    fn full_playthrough_reverifies_and_a_retcon_fails() {
        let s = scene();
        let mut driver = Driver::start(deploy(5), &s).expect("start");

        driver.advance(CH_TAKE_LANTERN).expect("take lantern");
        assert_eq!(driver.current_passage().as_deref(), Some(ROOM_ANTECHAMBER));
        driver.advance(CH_DESCEND).expect("descend (gate open)");
        assert_eq!(driver.current_passage().as_deref(), Some(ROOM_DARK_STAIR));
        driver.advance(CH_CLAIM).expect("claim the hoard");
        assert!(driver.is_ended(), "the dungeon ended");
        assert_eq!(driver.world().read_var("gold"), 500);

        let play = driver.playthrough();
        assert_eq!(play.receipts().len(), 4, "genesis + 3 moves");
        verify_chain_linkage(&play).expect("the receipt chain links cleanly");
        verify(deploy(5), &s, &play).expect("the honest playthrough re-verifies by replay");

        // Retcon the first move to "leave the lantern" — replay reproduces a DIFFERENT
        // committed state (or the executor refuses the later gated descend). Either way
        // the forged record fails.
        let mut forged = play.clone();
        forged.steps[0].choice_index = CH_LEAVE_LANTERN;
        let out = spween_dregg::verify_by_replay(deploy(5), &s, &forged);
        assert!(
            matches!(
                out,
                Err(VerifyBreak::StateMismatch {
                    step: StepPos::Step(0)
                }) | Err(VerifyBreak::RefusedOnReplay { .. })
                    | Err(VerifyBreak::PassageOutOfOrder { .. })
            ),
            "a retconned lantern-grab fails replay, got {out:?}"
        );
    }
}
