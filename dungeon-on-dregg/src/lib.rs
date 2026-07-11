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

use std::sync::Arc;

use dregg_app_framework::{
    CellProgram, Effect, StateConstraint, TransitionCase, TransitionGuard, field_from_u64, symbol,
};

/// Phase B — the un-jailbreakable AI narrator, landed on the real turn substrate. A
/// brain proposes a typed [`narrator::Command`] + a narration; the world resolves the
/// Command on the real executor (prose is not power) and the narration binds into the
/// real [`TurnReceipt`] via an `EmitEvent` (not a parallel ledger).
pub mod narrator;

/// Phase C — the COLLECTIVE landed on the real substrate. A crowd quorum-certifies a
/// winning [`narrator::Command`] through the REAL [`collective_choice`] engine (WriteOnce
/// ballots + Monotonic tally + the polis `AffineLe` quorum gate), and that certified
/// winner fires a REAL [`spween_dregg::WorldCell`] turn on the game executor — the crowd
/// decides, the world resolves. Prose/vote is not power: a quorum-certified but ILLEGAL
/// Command is a real executor refusal (the crowd cannot vote past the `CellProgram` gate).
pub mod collective;
use dregg_cell::program::HeapAtom;
use spween::{Choice, PassageContent, Scene};
use spween_dregg::{CompiledStory, WorldCell, choice_method, compile_scene, parse};

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

// ═══════════════════════════════════════════════════════════════════════════════
// SCALING UP — richer game mechanics, each a REAL executor-enforced `StateConstraint`
// ═══════════════════════════════════════════════════════════════════════════════
//
// The salt-shore slice proved ONE tooth (a gated exit = a real `FieldGte`). This
// section scales the collective-fiction rebuild to a richer dungeon — "The Warden's
// Keep" — whose real game rules each lower to an executor-enforced `StateConstraint`
// the verified `EmbeddedExecutor` re-checks on every touching turn. Each mechanic is
// DRIVEN (see the `keep_tests` module): a LEGAL move commits a real `TurnReceipt`; an
// ILLEGAL move is a REAL `WorldError::Refused` that commits NOTHING (anti-ghost).
//
// The mechanics + their salvaged `attested-dm` content (the RULES, not its toy blake3
// substrate) and their real tooth:
//
// | # | mechanic (attested-dm salvage)        | real executor tooth                       | cell field           |
// |---|----------------------------------------|-------------------------------------------|----------------------|
// | 1 | combat HP floor (`CombatEnemy` HP)     | `StateConstraint::FieldGte { .., 1 }`     | `hp` slot            |
// | 2 | loot / first-grabber (`LootRule`)      | `StateConstraint::WriteOnce`              | `relic_owner` slot   |
// | 3 | spell mana budget (`SpellRule` cost)   | `StateConstraint::FieldLteField`          | `mana_spent`↔`budget`|
// | 4 | one-way descent (`LightRule` ratchet)  | `StateConstraint::Monotonic`              | `depth` slot         |
// | 5 | multi-item inventory (`GameWorld`)     | `StateConstraint::HeapField { WriteOnce }`| heap key (>16 slots) |
//
// Tooth #1 is emitted by the v0 compiler itself: the attack move `~ hp -= 20` gated
// `{ hp >= 21 }` lifts (pre `hp>=21`, net delta −20) to the post-state `FieldGte(hp,1)`
// — "a blow you would not survive is refused." Teeth #2–#5 are shapes the v0 compiler
// does not emit (transition / cross-slot / heap constraints), so [`keep_compiled`]
// AUGMENTS the compiled program with them. An augmented case is enforced identically
// to a compiled one: the executor never distinguishes who authored a `TransitionCase`.

/// The richer dungeon — "The Warden's Keep" — in the spween DSL. Three rooms, each the
/// stage for one richer mechanic. Salvages `attested-dm`'s HP-combat / loot / spell-cost
/// / one-way-descent RULES onto the real substrate; every rule below is a real executor
/// tooth (see [`keep_compiled`]), never app bookkeeping.
///
/// The intro passage's entry effects seed the fight/budget (`hp = 50`, `mana_budget =
/// 50`) — real genesis writes when driven by the stock [`spween_dregg::Driver`]; the
/// direct-executor tests seed the same slots via [`WorldCell::seed_var`] (they bypass
/// genesis to drive the executor as the sole referee).
pub const KEEP: &str = r#"---
id: wardens-keep
title: The Warden's Keep
weight: 1
---

=== gatehall

~ hp = 50
~ mana_budget = 50

The gate-warden bars the way with a notched greatsword. Steel or nothing.

* [Trade blows with the gate-warden] { hp >= 21 }
  ~ hp -= 20
  -> gatehall

* [Press on into the plundered hall]
  -> hall

=== hall

A plundered hall. One reliquary crown remains on its plinth; two war-banners covet it,
and only the first hand to close on it holds it.

* [Claim the crown for the Red Hand]
  ~ relic_owner = 1
  -> hall

* [Claim the crown for the Blue Hand]
  ~ relic_owner = 2
  -> hall

* [Descend the collapsing stair]
  ~ depth += 1
  -> sanctum

=== sanctum

The sanctum hums with old wards; the stair groans and sheds stone behind you. Casting
draws on a finite reserve of will.

* [Cast the sealing ward]
  ~ mana_spent += 30
  -> sanctum

* [Climb back up the stair]
  ~ depth -= 1
  -> hall

* [Seize the hoard]
  ~ gold += 500
  -> END
"#;

// ── Keep room / choice coordinates (the driver + verifier speak in these) ────────

/// The keep's opening room: the gate-warden fight (HP-floor mechanic).
pub const ROOM_GATEHALL: &str = "gatehall";
/// The plundered hall: the contested crown (loot / first-grabber mechanic).
pub const ROOM_HALL: &str = "hall";
/// The warded sanctum: the sealing ward (mana-budget) + the collapsed stair (ratchet).
pub const ROOM_SANCTUM: &str = "sanctum";

/// `gatehall`: trade blows — costs 20 HP, gated so a killing blow is refused.
pub const KP_TRADE_BLOWS: usize = 0;
/// `gatehall`: press on into the hall (ungated).
pub const KP_PRESS_ON: usize = 1;
/// `hall`: claim the crown for the Red Hand (`relic_owner = 1`).
pub const KP_CLAIM_RED: usize = 0;
/// `hall`: claim the crown for the Blue Hand (`relic_owner = 2`) — refused if Red won.
pub const KP_CLAIM_BLUE: usize = 1;
/// `hall`: descend the collapsing stair (`depth += 1`).
pub const KP_DESCEND: usize = 2;
/// `sanctum`: cast the sealing ward (`mana_spent += 30`) — refused past the budget.
pub const KP_CAST_WARD: usize = 0;
/// `sanctum`: climb back up (`depth -= 1`) — refused (the stair collapsed: one-way).
pub const KP_CLIMB_BACK: usize = 1;
/// `sanctum`: seize the hoard (ends the dungeon).
pub const KP_SEIZE: usize = 2;

/// The dispatch method for a raw heap-write turn ([`WorldCell::apply_raw`]) that stashes
/// an item into the heap-keyed inventory (mechanic #5).
pub const STASH_METHOD: &str = "stash";
/// The heap key of the reliquary crown's owner marker — a WRITE-ONCE heap field: the
/// first stash claims it, a second stash to a different owner is refused. Keys `>= 16`
/// live in the cell's committed `fields_map` (the heap), beyond the 16 register slots.
pub const CROWN_HEAP_KEY: u64 = 100;

/// Parse the keep scene.
pub fn keep_scene() -> Scene {
    parse(KEEP, "wardens-keep.scene").expect("the keep scene parses")
}

/// Look up a variable's cell slot in the compiled keep (panics if the var is unnamed —
/// every var below is named by an effect/condition in [`KEEP`], so it always resolves).
fn keep_slot(story: &CompiledStory, name: &str) -> u8 {
    (*story
        .var_slots
        .get(name)
        .unwrap_or_else(|| panic!("keep var `{name}` has a compiled slot"))) as u8
}

/// Append `extra` constraints onto the existing method-guarded case for `method` (a
/// mechanic whose tooth the v0 compiler does not emit — a transition / cross-slot
/// constraint). Panics if no such case exists (a coordinate typo).
fn augment_case(program: &mut CellProgram, method: &str, extra: Vec<StateConstraint>) {
    let m = symbol(method);
    let CellProgram::Cases(cases) = program else {
        panic!("keep program is Cases");
    };
    let case = cases
        .iter_mut()
        .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method: mm } if *mm == m))
        .unwrap_or_else(|| panic!("no compiled case for method `{method}`"));
    case.constraints.extend(extra);
}

/// Add a fresh method-guarded case (for a method the scene has no choice for — the raw
/// [`STASH_METHOD`] heap-write turn).
fn add_case(program: &mut CellProgram, method: &str, constraints: Vec<StateConstraint>) {
    let CellProgram::Cases(cases) = program else {
        panic!("keep program is Cases");
    };
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(method),
        },
        constraints,
    });
}

/// **Compile the keep AND augment its program with the richer teeth** (#2–#5). Mechanic
/// #1 (the HP floor) is already a compiler-emitted `FieldGte` on the trade-blows case;
/// this adds the transition / cross-slot / heap constraints the v0 compiler cannot
/// express. The result is a `CellProgram` the real executor enforces move-for-move.
pub fn keep_compiled() -> CompiledStory {
    let mut story = compile_scene(&keep_scene()).expect("the keep compiles");

    let owner = keep_slot(&story, "relic_owner");
    let depth = keep_slot(&story, "depth");
    let spent = keep_slot(&story, "mana_spent");
    let budget = keep_slot(&story, "mana_budget");

    // #2 Loot / first-grabber-wins: the crown's owner slot is WRITE-ONCE — the first
    // claim (0 → banner) commits; a rival second claim (banner → other) is refused.
    let write_once_owner = || vec![StateConstraint::WriteOnce { index: owner }];
    augment_case(
        &mut story.program,
        &choice_method(ROOM_HALL, KP_CLAIM_RED),
        write_once_owner(),
    );
    augment_case(
        &mut story.program,
        &choice_method(ROOM_HALL, KP_CLAIM_BLUE),
        write_once_owner(),
    );

    // #4 One-way descent ratchet: `depth` is MONOTONIC — descending (depth += 1) passes;
    // climbing back (depth -= 1) decreases it and is refused ("the stair collapsed").
    augment_case(
        &mut story.program,
        &choice_method(ROOM_HALL, KP_DESCEND),
        vec![StateConstraint::Monotonic { index: depth }],
    );
    augment_case(
        &mut story.program,
        &choice_method(ROOM_SANCTUM, KP_CLIMB_BACK),
        vec![StateConstraint::Monotonic { index: depth }],
    );

    // #3 Spell mana budget: `mana_spent` must never exceed `mana_budget` (a CROSS-SLOT
    // post-state bound). The first ward (spent 0→30 ≤ 50) commits; a second (30→60 > 50)
    // overspends and is refused.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_SANCTUM, KP_CAST_WARD),
        vec![StateConstraint::FieldLteField {
            left_index: spent,
            right_index: budget,
        }],
    );

    // #5 Heap-keyed inventory: the crown's HEAP owner key is WRITE-ONCE. The heap
    // (`fields_map`, keys ≥ 16) holds a collection larger than the 16 register slots.
    add_case(
        &mut story.program,
        STASH_METHOD,
        vec![StateConstraint::HeapField {
            key: CROWN_HEAP_KEY,
            atom: HeapAtom::WriteOnce,
        }],
    );

    story
}

/// Deploy the augmented keep as a real world-cell (mechanics #2–#5 installed as executor
/// teeth). Deterministic in `seed` (re-deploy reproduces the same identity + hashes).
pub fn deploy_keep(seed: u8) -> WorldCell {
    WorldCell::deploy_compiled(Arc::new(keep_compiled()), seed).expect("the keep deploys")
}

/// A raw `Effect::SetField` writing `value` into HEAP key `key` on `cell` (`key >= 16`
/// routes into the committed `fields_map`). The move-shape mechanic #5's stash turn
/// carries, driven through [`WorldCell::apply_raw`].
pub fn stash_effect(cell: dregg_app_framework::CellId, key: u64, value: u64) -> Effect {
    Effect::SetField {
        cell,
        index: key as usize,
        value: field_from_u64(value),
    }
}

/// The executor-enforced constraints installed on the case guarded by `method` — proof
/// each mechanic's tooth is a real kernel predicate (for the example to print verbatim).
pub fn case_constraints(story: &CompiledStory, method: &str) -> Vec<StateConstraint> {
    let m = symbol(method);
    let CellProgram::Cases(cases) = &story.program else {
        return Vec::new();
    };
    cases
        .iter()
        .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method: mm } if *mm == m))
        .map(|c| c.constraints.clone())
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

// ═══════════════════════════════════════════════════════════════════════════════
// THE CEILINGS — where a single cell stops, named precisely (no faking)
// ═══════════════════════════════════════════════════════════════════════════════
//
// How far the single-cell world honestly scales, and the two substrate boundaries a
// full collective-fiction game hits next.
//
// ── (a) The 16-register budget, and how far the HEAP carries past it ──────────────
//
// A dregg cell has 16 fixed register slots (`dregg_cell::state::STATE_SLOTS`); slot 0
// is the passage/program-counter, leaving 15 for named scalar vars. The keep uses 6
// (`depth`, `gold`, `hp`, `mana_budget`, `mana_spent`, `relic_owner`) — comfortable.
// The compiler FAILS CLOSED past the budget: a scene naming >15 vars+atoms is a
// `CompileError::TooManySlots` (compiler.rs), not a silent slot collision.
//
// Collections that would blow the 15-slot budget (a per-item inventory, a per-room
// visited-map, a per-NPC dialogue-state map) move into the HEAP: `SetField` with key
// `>= 16` routes into the cell's committed `fields_map` (`state.rs`), digested into
// `fields_root` and bound into the cell commitment. Mechanic #5 drives this: 20+ item
// keys live in one cell's heap, each executor-constrained by a `HeapField` atom
// (`WriteOnce`/`Monotonic`/`Gte`/…). A single cell therefore scales to an UNBOUNDED
// keyed collection — as far as one serial writer + one state-root honestly goes.
//
// ── (b) CEILING 1 — the MULTI-CELL boundary (concurrency & authority, not capacity) ─
//
// The heap removes the CAPACITY reason to split, so the real boundary is not "ran out
// of slots" — it is CONCURRENCY and AUTHORITY. One cell is ONE serial writer under ONE
// owner key: every turn touching it totally orders against every other. A two-player
// party that acts SIMULTANEOUSLY, a shared world edited by many authors at once, or
// per-player state each player must solely control, all force a cell PER agent/party/
// shard — because independent writers must not serialize on one cell (`BalanceDeltaLte`
// is even flagged NOT i-confluent for exactly this reason in the constraint docs). The
// keep is single-writer, so it stays one cell; the moment two parties act concurrently,
// the world is a GRAPH of cells (a player-cell, a room-cell, a party-cell), not one.
//
// ── (c) CEILING 2 — CROSS-CELL gating (a tooth reading ANOTHER cell's state) ───────
//
// Every tooth here (`FieldGte`, `WriteOnce`, `Monotonic`, `FieldLteField`, `HeapField`)
// is checked against the ACTION'S OWN TARGET CELL's (old,new) post-state. None can read
// a DIFFERENT cell. So a rule like "room B's door opens because item A — living on a
// SEPARATE cell — was taken" CANNOT be a `StateConstraint` on room B's cell: room B's
// program cannot see item A's cell. Once (b) splits the world into multiple cells, most
// interesting gates become cross-cell and fall off this vocabulary's edge.
//
// What the cross-cell primitive needs (it EXISTS in the substrate; this slice does not
// wire it): a witnessed observation of a peer cell's FINALIZED field. The vocabulary
// already names it — `StateConstraint::Witnessed` / the `BoundBranch::Witnessed`
// arm / `ObservedFieldEquals` (types.rs), gated by a host `FinalizedRootAuthority`
// (`WitnessBundle::finalized_roots`): the turn carries a Merkle-open proof that peer
// cell A's `source_field` opens to value `v` at a finalized `at_root`, and the local
// tooth admits iff `new[local] == v`. A missing authority FAILS CLOSED (no peer roots ⇒
// every cross-cell read refuses) — the anti-self-fabrication tooth. Wiring it needs
// three things this slice lacks: (1) a real finalized-root channel between the world's
// cells (the `FinalizedRootAuthority` host impl), (2) the compiler lowering a
// cross-room condition (`taken(item_A) in room_B`) to a `Witnessed`/`ObservedFieldEquals`
// against item A's cell + slot, and (3) the driver attaching the Merkle-open witness
// blob to the gated turn. That is the next Phase — the multi-cell collective fiction —
// and it is a WIRING task over an existing primitive, not a missing one.

#[cfg(test)]
mod keep_tests {
    //! The richer mechanics, each DRIVEN: a legal move commits a real `TurnReceipt`; an
    //! illegal move is a REAL executor refusal that commits NOTHING (anti-ghost).
    use super::*;
    use spween_dregg::{Driver, Value, WorldError, verify, verify_chain_linkage};

    /// #1 — the compiler already lowers the gated attack to a real `FieldGte` tooth:
    /// the trade-blows move `~ hp -= 20` gated `{ hp >= 21 }` lifts to the post-state
    /// `FieldGte(hp, 1)` — a blow that would drop HP to 0 fails the kernel predicate.
    #[test]
    fn hp_floor_lowers_to_a_real_fieldgte_tooth() {
        let story = keep_compiled();
        let hp = keep_slot(&story, "hp");
        let cs = case_constraints(&story, &choice_method(ROOM_GATEHALL, KP_TRADE_BLOWS));
        assert!(
            cs.iter().any(|c| matches!(
                c,
                StateConstraint::FieldGte { index, value }
                    if *index == hp && *value == field_from_u64(1)
            )),
            "trade-blows gate is FieldGte(hp, 1); got {cs:?}"
        );
    }

    /// #1 (combat HP floor) — DRIVEN. Two blows land as real receipts (hp 50→30→10);
    /// the third would drop hp to 0 and is a REAL executor refusal that commits nothing.
    #[test]
    fn combat_hp_floor_legal_commits_illegal_refused() {
        let s = keep_scene();
        let mut world = deploy_keep(11);
        world.seed_var("hp", Value::Int(50)); // the gate-warden fight begins at 50 HP.

        let blow = choice_at(&s, ROOM_GATEHALL, KP_TRADE_BLOWS);

        // Two legal blows: each a real committed turn.
        let r1 = world
            .apply_choice(ROOM_GATEHALL, KP_TRADE_BLOWS, &blow)
            .expect("a survivable blow commits");
        assert_eq!(world.read_var("hp"), 30);
        let r2 = world
            .apply_choice(ROOM_GATEHALL, KP_TRADE_BLOWS, &blow)
            .expect("a survivable blow commits");
        assert_eq!(world.read_var("hp"), 10);
        assert_ne!(r1.turn_hash, [0u8; 32]);
        assert_eq!(
            r2.pre_state_hash, r1.post_state_hash,
            "the blow receipts chain (pre == prev.post)"
        );

        // The killing blow (10 − 20 ≤ 0) fails FieldGte(hp, 1): a REAL executor refusal.
        let refused = world.apply_choice(ROOM_GATEHALL, KP_TRADE_BLOWS, &blow);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a killing blow is refused by the executor, got {refused:?}"
        );
        // Anti-ghost: the refused turn committed nothing.
        assert_eq!(world.read_var("hp"), 10, "hp unchanged after the refusal");
    }

    /// #2 (loot / first-grabber-wins) — DRIVEN. The Red Hand claims the crown (a real
    /// `WriteOnce` transition 0→1); the Blue Hand's rival claim (1→2) is a REAL executor
    /// refusal — the crown is held by whoever's write landed FIRST.
    #[test]
    fn loot_first_grabber_wins_writeonce() {
        let s = keep_scene();
        let world = deploy_keep(12);

        let claim_red = choice_at(&s, ROOM_HALL, KP_CLAIM_RED);
        let claim_blue = choice_at(&s, ROOM_HALL, KP_CLAIM_BLUE);

        let r = world
            .apply_choice(ROOM_HALL, KP_CLAIM_RED, &claim_red)
            .expect("the first claim (0 → Red) commits");
        assert_eq!(world.read_var("relic_owner"), 1, "Red holds the crown");
        assert_ne!(r.turn_hash, [0u8; 32]);

        let refused = world.apply_choice(ROOM_HALL, KP_CLAIM_BLUE, &claim_blue);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a rival second claim is refused (WriteOnce), got {refused:?}"
        );
        assert_eq!(
            world.read_var("relic_owner"),
            1,
            "anti-ghost: the crown still belongs to Red"
        );
    }

    /// #3 (spell mana budget) — DRIVEN. The first ward spends within budget (0→30 ≤ 50,
    /// a real committed turn); the second would overspend (30→60 > 50) and is a REAL
    /// executor refusal (`FieldLteField` — a cross-slot post-state bound).
    #[test]
    fn mana_budget_cross_slot_fieldltefield() {
        let s = keep_scene();
        let mut world = deploy_keep(13);
        world.seed_var("mana_budget", Value::Int(50));

        let ward = choice_at(&s, ROOM_SANCTUM, KP_CAST_WARD);

        let r = world
            .apply_choice(ROOM_SANCTUM, KP_CAST_WARD, &ward)
            .expect("a ward within budget commits");
        assert_eq!(world.read_var("mana_spent"), 30);
        assert_ne!(r.turn_hash, [0u8; 32]);

        let refused = world.apply_choice(ROOM_SANCTUM, KP_CAST_WARD, &ward);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "an over-budget ward is refused (FieldLteField), got {refused:?}"
        );
        assert_eq!(
            world.read_var("mana_spent"),
            30,
            "anti-ghost: no will was spent on the refused cast"
        );
    }

    /// #4 (one-way descent ratchet) — DRIVEN. Descending deepens `depth` (0→1, a real
    /// committed turn that PASSES the `Monotonic` tooth); climbing back would decrease it
    /// (1→0) and is a REAL executor refusal — the stair collapsed; the descent is one-way.
    #[test]
    fn depth_ratchet_monotonic() {
        let s = keep_scene();
        let world = deploy_keep(14);

        let descend = choice_at(&s, ROOM_HALL, KP_DESCEND);
        let climb = choice_at(&s, ROOM_SANCTUM, KP_CLIMB_BACK);

        let r = world
            .apply_choice(ROOM_HALL, KP_DESCEND, &descend)
            .expect("descending (depth 0→1) passes Monotonic and commits");
        assert_eq!(world.read_var("depth"), 1);
        assert_ne!(r.turn_hash, [0u8; 32]);

        let refused = world.apply_choice(ROOM_SANCTUM, KP_CLIMB_BACK, &climb);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "climbing back (depth 1→0) is refused (Monotonic), got {refused:?}"
        );
        assert_eq!(
            world.read_var("depth"),
            1,
            "anti-ghost: depth did not un-ratchet"
        );
    }

    /// #5 (heap-keyed inventory) — DRIVEN. The single cell scales a collection LARGER
    /// than its 16 register slots into the committed heap (`fields_map`, keys ≥ 16): 20
    /// stashed items live there. The crown's heap owner key is WRITE-ONCE: the first
    /// stash claims it, a re-claim to a different owner is a REAL executor refusal.
    #[test]
    fn heap_inventory_scales_and_writeonce_bites() {
        let world = deploy_keep(15);
        let cell = world.cell_id();

        // First stash of the crown (heap[100] absent → 1): a real committed turn.
        let r = world
            .apply_raw(STASH_METHOD, vec![stash_effect(cell, CROWN_HEAP_KEY, 1)])
            .expect("the first stash of the crown commits");
        assert_eq!(world.read_heap(CROWN_HEAP_KEY), Some(1));
        assert_ne!(r.turn_hash, [0u8; 32]);

        // Stash 20 more items into heap keys 16..36 — beyond the 15 usable register
        // slots. Each is a real committed turn; the heap holds the whole collection.
        for k in 16u64..36 {
            world
                .apply_raw(STASH_METHOD, vec![stash_effect(cell, k, 1)])
                .unwrap_or_else(|e| panic!("stashing item at heap key {k} commits: {e}"));
            assert_eq!(world.read_heap(k), Some(1), "heap holds item {k}");
        }

        // Re-claim the crown for a different owner (heap[100] 1→2): WriteOnce refuses.
        let refused = world.apply_raw(STASH_METHOD, vec![stash_effect(cell, CROWN_HEAP_KEY, 2)]);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a heap re-claim of the crown is refused (HeapField WriteOnce), got {refused:?}"
        );
        assert_eq!(
            world.read_heap(CROWN_HEAP_KEY),
            Some(1),
            "anti-ghost: the crown's heap owner is unchanged"
        );
    }

    /// A full LEGAL playthrough over the stock runtime commits a real receipt chain
    /// (through all four in-scene teeth) and re-verifies by replay against a fresh
    /// identically-seeded, identically-augmented keep.
    #[test]
    fn full_keep_playthrough_reverifies() {
        let s = keep_scene();
        let mut driver = Driver::start(deploy_keep(16), &s).expect("start the keep");

        driver.advance(KP_TRADE_BLOWS).expect("survivable blow"); // hp 50→30 (FieldGte)
        driver.advance(KP_PRESS_ON).expect("into the hall");
        driver.advance(KP_CLAIM_RED).expect("claim the crown"); // owner 0→1 (WriteOnce)
        driver.advance(KP_DESCEND).expect("descend the stair"); // depth 0→1 (Monotonic)
        driver.advance(KP_CAST_WARD).expect("cast the ward"); // spent 0→30 (FieldLteField)
        driver.advance(KP_SEIZE).expect("seize the hoard");
        assert!(driver.is_ended(), "the keep is cleared");
        assert_eq!(driver.world().read_var("gold"), 500);
        assert_eq!(driver.world().read_var("hp"), 30);
        assert_eq!(driver.world().read_var("relic_owner"), 1);
        assert_eq!(driver.world().read_var("depth"), 1);
        assert_eq!(driver.world().read_var("mana_spent"), 30);

        let play = driver.playthrough();
        assert_eq!(play.receipts().len(), 7, "genesis + 6 moves");
        verify_chain_linkage(&play).expect("the keep receipt chain links");
        verify(deploy_keep(16), &s, &play).expect("the honest keep playthrough re-verifies");
    }
}
