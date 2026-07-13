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

/// The MULTI-CELL frontier — a universe as a GRAPH of real cells (rooms/items as
/// SEPARATE cells) with a **real executor-enforced CROSS-CELL gate**. Where the
/// single-cell keep (this file) named its ceiling — a tooth cannot read ANOTHER
/// cell's state — [`multicell`] closes it with the real substrate primitive:
/// [`StateConstraint::ObservedFieldEquals`](dregg_app_framework::StateConstraint)
/// on room-B's cell, reading item-A's finalized owner slot on item-A's OWN cell,
/// admitted by the executor's [`FinalizedRootAuthority`](dregg_cell::predicate::FinalizedRootAuthority)
/// (built from the committed ledger) plus the driver attaching the Merkle-open
/// witness of item-A's finalized state. "Room B opens because item A was taken on
/// another cell" becomes a kernel predicate the [`EmbeddedExecutor`](dregg_app_framework::EmbeddedExecutor)
/// re-checks across cells — NOT a host `if`.
pub mod multicell;

/// THE MULTI-PLAYER SHARED WORLD — several PLAYER cells inhabit ONE living world, each
/// acting via real cap-bounded turns. Closes the concurrency-&-authority half of the
/// single-cell ceiling this crate named, on the real multi-actor substrate
/// ([`starbridge_v2::world::World`]). See the module docs for the full model.
pub mod mud;

/// VERIFIABLE RANDOMNESS landed on a real turn. The single-cell keep's combat uses a
/// FIXED damage rule (the compiler's `FieldGte(hp, 1)` tooth); [`dice_combat`] wires a
/// real [`dregg_dice::DrawStream`] roll into a combat blow — the damage is a real draw
/// over a [`dregg_dice::RandomnessRequest`] binding the turn context, bound into the
/// real [`TurnReceipt`] via an `EmitEvent` (mirroring [`narrator`]'s narration binding)
/// and REPRODUCED on replay ([`dice_combat::reverify_draw`] re-derives the same draw; a
/// forged roll is caught). Reproducible offline via the `Deterministic` source; the
/// non-grindable `ServerVrf`/`Hybrid` sources are a named `dregg-dice` follow-up.
pub mod dice_combat;

pub mod combat;
/// RPG CHARACTER PROGRESSION on the real substrate. XP, LEVEL and CLASS are real
/// character-cell state; a level-up is a real turn the executor GATES on earned XP
/// (`FieldGte(xp, threshold(L))`) so you cannot level without the XP, and a class
/// ability is admitted only in-class (`FieldEquals(class, .)`) — the referee is the
/// kernel, not the game code. See [`progression`] for the cell model + the driven
/// earned/premature/class-gate teeth.
pub mod progression;
pub mod skills;
pub mod spells;
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

// ═══════════════════════════════════════════════════════════════════════════════
// A SECOND UNIVERSE — "The Sunken Vault": an ITEM / INVENTORY system, executor-refereed
// ═══════════════════════════════════════════════════════════════════════════════
//
// The Keep proved four rules-as-teeth on ONE scene. The Vault is a SECOND committed
// world, deployed the SAME real way (compile → augment → birth cell → install the
// `CellProgram`), whose deepening is an **inventory**: items a player picks up and uses,
// each pickup/use a real cap-bounded turn the verified executor REFUSES when illegal.
// Nothing here is app bookkeeping — every rule is a `StateConstraint` the
// [`EmbeddedExecutor`](dregg_app_framework::EmbeddedExecutor) re-checks on the turn's
// post-state, identical enforcement to the Keep.
//
// | item             | pickup tooth (augmented)      | use tooth                                  |
// |------------------|-------------------------------|--------------------------------------------|
// | coral key        | `WriteOnce { key_owner }`     | `FieldGte(key_owner, 1)` on the grate move |
// | healing draught  | `WriteOnce { draughts_held }` | `FieldLteField(draughts_drunk ≤ held)`     |
//
// Plus the Keep's HP-floor combat (a compiler-emitted `FieldGte(hp, 1)` on the
// eel-warden blow), so the draught's heal is load-bearing. Each tooth is
// executor-enforced and NON-VACUOUS — it BITES on the illegal move:
//   * **grab-a-taken-item** — the coral key is a CONTESTED relic: the first crew to
//     claim it (`key_owner` 0→1) holds it, and a RIVAL claim (1→2) fails `WriteOnce`.
//     (A boolean `WriteOnce` admits an idempotent `1→1` no-op — "you already hold it" —
//     so a genuinely-biting pickup refusal is the rival-claim / first-grabber shape,
//     a nonzero→different-nonzero write, exactly what `WriteOnce` refuses.)
//   * **use-without-holding (a gate item)** — slipping the grate with `key_owner == 0`
//     fails the `FieldGte(key_owner, 1)` the compiler lifts from `{ key_owner >= 1 }`
//     (the grate move does not touch `key_owner`, so the threshold stays 1 — a real
//     bite, not the vacuous `>= 0` a same-var decrement would collapse to). The coral
//     key is therefore BOTH loot (WriteOnce) AND a key that gates a door (FieldGte) —
//     one inventory item carrying two distinct executor teeth.
//   * **use-without-holding (a consumable)** — drinking with `draughts_held == 0`, or
//     over-drinking past what you hold, fails the cross-slot `FieldLteField` budget
//     (drunk 0→1 with held 0 ⇒ 1 ≤ 0 is false ⇒ refused; drunk 1→2 with held 1 likewise).
//
// The Vault reuses the SAME augmentation machinery as the Keep ([`keep_slot`],
// [`augment_case`]) and the SAME real substrate — it is a fully additive world.

/// The second dungeon — "The Sunken Vault" — in the spween DSL. Three rooms: a drowned
/// `wreck` (the inventory: a coral key + a healing draught to pick up), a flooded
/// `gallery` (an eel-warden to fight, a draught to drink, a key-gated grate), and the
/// `vault` (the hoard). The inventory RULES lower to real executor teeth (see
/// [`vault_compiled`]).
pub const VAULT: &str = r#"---
id: sunken-vault
title: The Sunken Vault
weight: 1
---

=== wreck

~ hp = 40

A drowned wreck slumps in the current. A coral key glints in the silt — both the Gull
and Kraken wrecking-crews reach for it, and only the first hand to close on it holds it.
A healing draught bobs sealed in a bubble of air. A flooded gallery yawns north.

* [Claim the coral key for the Gull crew]
  ~ key_owner = 1
  -> wreck

* [Claim the coral key for the Kraken crew]
  ~ key_owner = 2
  -> wreck

* [Pocket the healing draught]
  ~ draughts_held = 1
  -> wreck

* [Swim north into the gallery]
  -> gallery

=== gallery

An eel-warden coils before a barnacled grate. Its bite is quick and cold, and the grate
beyond will not shift for a hand without the coral key.

* [Trade a blow with the eel-warden] { hp >= 16 }
  ~ hp -= 15
  -> gallery

* [Drink the healing draught]
  ~ draughts_drunk += 1
  ~ hp += 25
  -> gallery

* [Slip through the barnacled grate] { key_owner >= 1 }
  -> vault

* [Retreat to the wreck]
  -> wreck

=== vault

The vault floods with pale green light. A drowned hoard heaps the silt floor.

* [Seize the drowned hoard]
  ~ gold += 750
  -> END
"#;

// ── Vault room / choice coordinates (the driver + verifier speak in these) ───────

/// The drowned wreck: the inventory room (pick up the coral key + the draught).
pub const ROOM_WRECK: &str = "wreck";
/// The flooded gallery: the eel-warden fight, the draught, the key-gated grate.
pub const ROOM_GALLERY: &str = "gallery";
/// The flooded vault (terminal): the drowned hoard.
pub const ROOM_VAULT: &str = "vault";

/// `wreck`: claim the contested coral key for the Gull crew (`key_owner = 1`) — a
/// WRITE-ONCE, first-grabber-wins pickup.
pub const VLT_CLAIM_GULL: usize = 0;
/// `wreck`: claim the contested coral key for the Kraken crew (`key_owner = 2`) —
/// refused if the Gull crew already holds it (`WriteOnce`).
pub const VLT_CLAIM_KRAKEN: usize = 1;
/// `wreck`: pocket the healing draught (`draughts_held = 1`) — a WRITE-ONCE pickup.
pub const VLT_TAKE_DRAUGHT: usize = 2;
/// `wreck`: swim north into the gallery (ungated).
pub const VLT_SWIM: usize = 3;
/// `gallery`: trade a blow with the eel-warden — costs 15 HP, gated so a killing blow
/// is refused (`FieldGte(hp, 1)`).
pub const VLT_TRADE_BLOW: usize = 0;
/// `gallery`: drink the healing draught (`draughts_drunk += 1`, `hp += 25`) — refused
/// unless a draught is held (`FieldLteField(draughts_drunk ≤ draughts_held)`).
pub const VLT_DRINK: usize = 1;
/// `gallery`: slip through the grate into the vault — refused without the coral key
/// (`FieldGte(key_owner, 1)`).
pub const VLT_GRATE: usize = 2;
/// `gallery`: retreat back to the wreck (ungated).
pub const VLT_RETREAT: usize = 3;
/// `vault`: seize the hoard (ends the dungeon).
pub const VLT_SEIZE: usize = 0;

/// Parse the Sunken Vault scene.
pub fn vault_scene() -> Scene {
    parse(VAULT, "sunken-vault.scene").expect("the vault scene parses")
}

/// **Compile the Vault AND augment its program with the inventory teeth.** The combat
/// HP-floor (`FieldGte(hp, 1)`) and the key gate (`FieldGte(has_key, 1)`) are already
/// compiler-emitted from the scene conditions; this adds the two shapes the v0 compiler
/// does not emit — the `WriteOnce` on each pickup slot and the `FieldLteField` draught
/// budget — as real `CellProgram` cases the executor re-checks move-for-move.
pub fn vault_compiled() -> CompiledStory {
    let mut story = compile_scene(&vault_scene()).expect("the vault compiles");

    let key_owner = keep_slot(&story, "key_owner");
    let held = keep_slot(&story, "draughts_held");
    let drunk = keep_slot(&story, "draughts_drunk");

    // The coral key is a CONTESTED, first-grabber-wins relic: its owner slot is
    // WRITE-ONCE, so whichever crew claims it first (0→banner) holds it, and a RIVAL
    // claim (banner→other banner) is refused — the grab-a-taken-item tooth. (A boolean
    // WriteOnce admits an idempotent same-value re-write; the contested-owner shape is
    // the one that genuinely BITES a second claimant.)
    let write_once_key = || vec![StateConstraint::WriteOnce { index: key_owner }];
    augment_case(
        &mut story.program,
        &choice_method(ROOM_WRECK, VLT_CLAIM_GULL),
        write_once_key(),
    );
    augment_case(
        &mut story.program,
        &choice_method(ROOM_WRECK, VLT_CLAIM_KRAKEN),
        write_once_key(),
    );
    // The draught pickup is WRITE-ONCE too (defensive: the held-count cannot be
    // re-written to a different value). Its genuinely-biting tooth is the CONSUME
    // budget below, not this idempotent pickup.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_WRECK, VLT_TAKE_DRAUGHT),
        vec![StateConstraint::WriteOnce { index: held }],
    );

    // Consuming the draught is bounded by what you HOLD: `draughts_drunk` may never
    // exceed `draughts_held` (a CROSS-SLOT post-state bound). Drinking with none held
    // (0→1 > 0) or over-drinking (1→2 > 1) is refused — use-without-holding, on a
    // consumable. The same tooth-shape as the Keep's mana budget, on inventory.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_GALLERY, VLT_DRINK),
        vec![StateConstraint::FieldLteField {
            left_index: drunk,
            right_index: held,
        }],
    );

    story
}

/// Deploy the augmented Vault as a real world-cell (the inventory teeth installed as
/// executor predicates). Deterministic in `seed` (re-deploy reproduces identity + hashes).
pub fn deploy_vault(seed: u8) -> WorldCell {
    WorldCell::deploy_compiled(Arc::new(vault_compiled()), seed).expect("the vault deploys")
}

#[cfg(test)]
mod vault_tests {
    //! The Sunken Vault's inventory, each mechanic DRIVEN on the real `WorldCell`: a
    //! legal pickup/use commits a real `TurnReceipt`; an illegal one (grab-a-taken-item,
    //! use-without-holding) is a REAL executor refusal that commits NOTHING (anti-ghost).
    use super::*;
    use spween_dregg::{
        Driver, StepPos, Value, VerifyBreak, WorldError, verify, verify_by_replay,
        verify_chain_linkage,
    };

    /// The inventory rules are REAL kernel predicates: introspect the installed program
    /// and confirm the grate gate is `FieldGte(has_key, 1)`, each pickup carries a
    /// `WriteOnce`, and the drink carries the cross-slot `FieldLteField` budget.
    #[test]
    fn vault_teeth_are_real_kernel_predicates() {
        let story = vault_compiled();
        let key_owner = keep_slot(&story, "key_owner");
        let held = keep_slot(&story, "draughts_held");
        let drunk = keep_slot(&story, "draughts_drunk");
        let hp = keep_slot(&story, "hp");

        // The grate gate lowered fully to an executor FieldGte on the key-owner slot.
        let m_grate = choice_method(ROOM_GALLERY, VLT_GRATE);
        assert_eq!(
            story.fully_gated.get(&m_grate),
            Some(&true),
            "the grate gate is fully executor-enforced"
        );
        let grate = case_constraints(&story, &m_grate);
        assert!(
            grate.iter().any(|c| matches!(
                c,
                StateConstraint::FieldGte { index, value }
                    if *index == key_owner && *value == field_from_u64(1)
            )),
            "grate gate is FieldGte(key_owner, 1); got {grate:?}"
        );

        // The combat blow lifted to a real FieldGte(hp, 1) — a killing blow is refused.
        let blow = case_constraints(&story, &choice_method(ROOM_GALLERY, VLT_TRADE_BLOW));
        assert!(
            blow.iter().any(|c| matches!(
                c,
                StateConstraint::FieldGte { index, value }
                    if *index == hp && *value == field_from_u64(1)
            )),
            "blow gate is FieldGte(hp, 1); got {blow:?}"
        );

        // Both rival key-claim cases carry a WriteOnce on the contested owner slot.
        for m in [
            choice_method(ROOM_WRECK, VLT_CLAIM_GULL),
            choice_method(ROOM_WRECK, VLT_CLAIM_KRAKEN),
        ] {
            let claim = case_constraints(&story, &m);
            assert!(
                claim.iter().any(
                    |c| matches!(c, StateConstraint::WriteOnce { index } if *index == key_owner)
                ),
                "claim `{m}` is WriteOnce(key_owner); got {claim:?}"
            );
        }
        let take_draught = case_constraints(&story, &choice_method(ROOM_WRECK, VLT_TAKE_DRAUGHT));
        assert!(
            take_draught
                .iter()
                .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == held)),
            "take-draught is WriteOnce(draughts_held); got {take_draught:?}"
        );

        // The drink is bounded by the cross-slot draught budget.
        let drink = case_constraints(&story, &choice_method(ROOM_GALLERY, VLT_DRINK));
        assert!(
            drink.iter().any(|c| matches!(
                c,
                StateConstraint::FieldLteField { left_index, right_index }
                    if *left_index == drunk && *right_index == held
            )),
            "drink is FieldLteField(draughts_drunk ≤ draughts_held); got {drink:?}"
        );
    }

    /// ITEM PICKUP (grab-a-taken-item, first-grabber-wins) — DRIVEN. The Gull crew
    /// claims the contested coral key (a real `WriteOnce` transition 0→1); the Kraken
    /// crew's rival claim (1→2) is a REAL executor refusal — the item is already taken.
    #[test]
    fn coral_key_first_grabber_wins() {
        let s = vault_scene();
        let world = deploy_vault(21);

        let claim_gull = choice_at(&s, ROOM_WRECK, VLT_CLAIM_GULL);
        let claim_kraken = choice_at(&s, ROOM_WRECK, VLT_CLAIM_KRAKEN);

        let r = world
            .apply_choice(ROOM_WRECK, VLT_CLAIM_GULL, &claim_gull)
            .expect("the first claim of the coral key (0 → Gull) commits");
        assert_eq!(
            world.read_var("key_owner"),
            1,
            "the Gull crew holds the key"
        );
        assert_ne!(r.turn_hash, [0u8; 32]);

        // A rival claim (key_owner 1→2): WriteOnce refuses — the key is already taken.
        let refused = world.apply_choice(ROOM_WRECK, VLT_CLAIM_KRAKEN, &claim_kraken);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "grabbing a taken item is refused (WriteOnce), got {refused:?}"
        );
        assert_eq!(
            world.read_var("key_owner"),
            1,
            "anti-ghost: the key still belongs to the Gull crew"
        );
    }

    /// ITEM USE — a gate item (use-without-holding) — DRIVEN. Without the coral key the
    /// grate will not open (a REAL `FieldGte` refusal); after prising the key, the SAME
    /// move commits and carries the player through into the vault.
    #[test]
    fn grate_use_without_key_refused_then_with_key_commits() {
        let s = vault_scene();
        let world = deploy_vault(22);

        // Swim to the gallery WITHOUT claiming the key.
        let swim = choice_at(&s, ROOM_WRECK, VLT_SWIM);
        world
            .apply_choice(ROOM_WRECK, VLT_SWIM, &swim)
            .expect("swimming north is ungated and commits");
        assert_eq!(world.read_var("key_owner"), 0, "no key held");

        // Slip the grate with key_owner == 0: FieldGte(key_owner, 1) refuses.
        let grate = choice_at(&s, ROOM_GALLERY, VLT_GRATE);
        let refused = world.apply_choice(ROOM_GALLERY, VLT_GRATE, &grate);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "using the grate without the key is refused (FieldGte), got {refused:?}"
        );
        assert_eq!(
            world.read_passage(),
            Some(1),
            "anti-ghost: still in the gallery, the grate did not open"
        );

        // Retreat, claim the key, and try the grate again — now it opens.
        let retreat = choice_at(&s, ROOM_GALLERY, VLT_RETREAT);
        world
            .apply_choice(ROOM_GALLERY, VLT_RETREAT, &retreat)
            .expect("retreat to the wreck commits");
        let claim = choice_at(&s, ROOM_WRECK, VLT_CLAIM_GULL);
        world
            .apply_choice(ROOM_WRECK, VLT_CLAIM_GULL, &claim)
            .expect("claim the coral key");
        world
            .apply_choice(ROOM_WRECK, VLT_SWIM, &swim)
            .expect("swim back to the gallery");
        assert_eq!(world.read_var("key_owner"), 1, "the key is now held");

        let r = world
            .apply_choice(ROOM_GALLERY, VLT_GRATE, &grate)
            .expect("with the key, the grate opens and commits");
        assert_eq!(world.read_passage(), Some(2), "now in the vault");
        assert_ne!(r.turn_hash, [0u8; 32]);
    }

    /// ITEM USE — a consumable (use-without-holding / over-use) — DRIVEN. Drinking with
    /// no draught held is a REAL executor refusal; after pocketing one draught the first
    /// drink commits (heals 25 HP), and a SECOND drink over-spends the single held
    /// draught and is refused — the cross-slot `FieldLteField` budget bites.
    #[test]
    fn healing_draught_consume_requires_holding() {
        let s = vault_scene();
        let mut world = deploy_vault(23);
        world.seed_var("hp", Value::Int(40));

        let drink = choice_at(&s, ROOM_GALLERY, VLT_DRINK);

        // Drink with draughts_held == 0: drunk 0→1 > held 0 ⇒ FieldLteField refuses.
        let refused = world.apply_choice(ROOM_GALLERY, VLT_DRINK, &drink);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "drinking with no draught held is refused (FieldLteField), got {refused:?}"
        );
        assert_eq!(
            world.read_var("draughts_drunk"),
            0,
            "anti-ghost: nothing drunk"
        );
        assert_eq!(world.read_var("hp"), 40, "anti-ghost: no phantom heal");

        // Pocket a draught, then the first drink commits and heals.
        let take = choice_at(&s, ROOM_WRECK, VLT_TAKE_DRAUGHT);
        world
            .apply_choice(ROOM_WRECK, VLT_TAKE_DRAUGHT, &take)
            .expect("pocket the healing draught");
        assert_eq!(world.read_var("draughts_held"), 1);

        let r = world
            .apply_choice(ROOM_GALLERY, VLT_DRINK, &drink)
            .expect("a held draught drinks (0→1 ≤ 1) and commits");
        assert_eq!(world.read_var("draughts_drunk"), 1);
        assert_eq!(world.read_var("hp"), 65, "the draught healed 25 HP");
        assert_ne!(r.turn_hash, [0u8; 32]);

        // A second drink over-spends the single held draught (1→2 > 1): refused.
        let over = world.apply_choice(ROOM_GALLERY, VLT_DRINK, &drink);
        assert!(
            matches!(over, Err(WorldError::Refused(_))),
            "over-drinking past what you hold is refused (FieldLteField), got {over:?}"
        );
        assert_eq!(
            world.read_var("draughts_drunk"),
            1,
            "anti-ghost: no will spent on the refused over-drink"
        );
        assert_eq!(world.read_var("hp"), 65, "anti-ghost: no phantom heal");
    }

    /// A full LEGAL Vault playthrough over the stock runtime — pick up BOTH items, fight,
    /// drink, key through the grate, seize the hoard — commits a real receipt chain
    /// (through all inventory teeth) and re-verifies by replay against a fresh,
    /// identically-seeded, identically-augmented Vault.
    #[test]
    fn full_vault_playthrough_reverifies() {
        let s = vault_scene();
        let mut driver = Driver::start(deploy_vault(24), &s).expect("start the vault");

        driver.advance(VLT_CLAIM_GULL).expect("claim the coral key"); // key_owner 0→1 (WriteOnce)
        driver
            .advance(VLT_TAKE_DRAUGHT)
            .expect("pocket the draught"); // held 0→1 (WriteOnce)
        driver.advance(VLT_SWIM).expect("swim to the gallery");
        driver.advance(VLT_TRADE_BLOW).expect("trade a blow"); // hp 40→25 (FieldGte)
        driver.advance(VLT_DRINK).expect("drink the draught"); // drunk 0→1 ≤ 1 (FieldLteField), hp 25→50
        driver.advance(VLT_GRATE).expect("slip the grate"); // key_owner ≥ 1 (FieldGte)
        driver.advance(VLT_SEIZE).expect("seize the hoard");
        assert!(driver.is_ended(), "the vault is cleared");
        assert_eq!(driver.world().read_var("gold"), 750);
        assert_eq!(driver.world().read_var("hp"), 50);
        assert_eq!(driver.world().read_var("key_owner"), 1);
        assert_eq!(driver.world().read_var("draughts_held"), 1);
        assert_eq!(driver.world().read_var("draughts_drunk"), 1);

        let play = driver.playthrough();
        assert_eq!(play.receipts().len(), 8, "genesis + 7 moves");
        verify_chain_linkage(&play).expect("the vault receipt chain links");
        verify(deploy_vault(24), &s, &play).expect("the honest vault playthrough re-verifies");
    }

    /// A retconned Vault playthrough FAILS replay: forge the record to SKIP claiming the
    /// key (swim first), and the later key-gated grate is refused on replay — or the
    /// reproduced passage order diverges. Either way the forged record cannot pass.
    #[test]
    fn retconned_vault_playthrough_fails() {
        let s = vault_scene();
        let mut driver = Driver::start(deploy_vault(25), &s).expect("start the vault");
        driver.advance(VLT_CLAIM_GULL).expect("claim the coral key");
        driver.advance(VLT_SWIM).expect("swim to the gallery");
        driver
            .advance(VLT_GRATE)
            .expect("slip the grate with the key");
        driver.advance(VLT_SEIZE).expect("seize the hoard");

        let play = driver.playthrough();
        // Sanity: the honest record verifies.
        verify(deploy_vault(25), &s, &play).expect("the honest record re-verifies");

        // Forge step 0: don't take the key, swim instead. Replay diverges — the grate is
        // now unkeyed (RefusedOnReplay) or the passage order breaks first.
        let mut forged = play.clone();
        forged.steps[0].choice_index = VLT_SWIM;
        let out = verify_by_replay(deploy_vault(25), &s, &forged);
        assert!(
            matches!(
                out,
                Err(VerifyBreak::RefusedOnReplay { .. })
                    | Err(VerifyBreak::PassageOutOfOrder { .. })
                    | Err(VerifyBreak::StateMismatch {
                        step: StepPos::Step(_)
                    })
            ),
            "a retconned key-skip fails replay, got {out:?}"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// A THIRD UNIVERSE — "The Tidewrack Hold": a GENERAL N-SLOT HEAP-KEYED INVENTORY
// ═══════════════════════════════════════════════════════════════════════════════
//
// The Keep proved a heap-keyed `WriteOnce` on ONE key (mechanic #5); the Sunken Vault
// gave each item its OWN NAMED REGISTER SLOT (`key_owner`, `draughts_held`,
// `draughts_drunk`) — at most ~15 items before the 16-register budget runs out. The
// Tidewrack Hold is the fuller version the Vault named: items live in a HEAP-KEYED SLOT
// MAP (`CellState::fields_map`, keys `>= STATE_SLOTS`), NOT one register per item, so a
// player holds an UNBOUNDED set of distinct items. Every operation is a real cap-bounded
// turn the verified [`EmbeddedExecutor`](dregg_app_framework::EmbeddedExecutor) refers,
// each tooth a real [`StateConstraint`] the executor re-checks on the turn's post-state —
// never app bookkeeping, identical enforcement to the Keep/Vault.
//
// THE MODEL — `heap[held_key] = owner id` (0 / absent = unheld); one heap key per item:
//
//   * PICKUP (insert) — a SINGLE generic [`HOLD_PICKUP_METHOD`] turn whose case is a
//     CONJUNCTION of `HeapField { key, WriteOnce }` over EVERY registered item key.
//     Writing item K (absent/zero → owner) admits; a RIVAL re-grab of a TAKEN key
//     (owner_a → owner_b) fails K's `WriteOnce`; every UNTOUCHED key's `WriteOnce` passes
//     idempotently (old == new), so ONE method safely gates N distinct inserts. A
//     double-grab of the same heap key by a rival is a real executor refusal.
//   * USE (a gate / key item) — a per-item `hold_use_<key>` turn gated
//     `HeapField { key, Gte(1) }`: admitted IFF the item is held (absent post-state ⇒
//     refuse), and NON-consuming (the held key is untouched; a benign use-tally heap key
//     bumps so the turn carries a real committed effect and repeat-uses are visible).
//     Use-without-holding is a real `WorldError::Refused`.
//   * CONSUME (a charged item) — a per-item `hold_consume_<key>` turn gated by TWO teeth:
//     `HeapField { held_key, Gte(1) }` (must hold it — absent refuses: use-without-
//     holding on a consumable) AND `HeapField { used_key, Lte(charges) }` (the consumed
//     tally may never exceed the item's charge cap). A single-charge item consumed twice
//     (used 1 → 2 > 1) is refused: a consumed item cannot be re-used.
//
// Replay: the inventory turns ride [`WorldCell::apply_raw`] (the heap path, below the
// choice/passage layer), so their verify-by-replay is the RAW-TURN analog of
// [`spween_dregg::verify_by_replay`] (which replays register-slot CHOICE playthroughs):
// [`replay_hold`] re-deploys an identically-seeded Hold and re-applies the SAME op
// sequence, reproducing the committed heap exactly; a retconned record (a use whose
// pickup was dropped) is REFUSED by the real executor on replay. The room-scene half of
// this universe still re-verifies through the stock [`spween_dregg::verify`] machinery
// unchanged (see `hold_tests::hold_room_playthrough_reverifies`).
//
// HONEST SCOPE. This is a general HEAP-KEYED inventory with executor teeth for
// pickup / use / consume over an unbounded key space. What a FULLER version adds:
//   * true QUANTITIES / STACKING — held as a live count a consume DECREMENTS with a
//     dynamic `consumed <= held` budget. The heap vocabulary is SINGLE-KEY atoms
//     (`Gte`/`Lte`/`WriteOnce`/`Monotonic`/…) with NO heap-vs-heap cross-key `Lte`, so
//     the consume cap here is a per-item COMPILE-TIME constant, not the live held count
//     (the Vault's cross-SLOT `FieldLteField` has no heap twin);
//   * DROP / transfer — heap `WriteOnce` freezes a taken key against erasure (the anti-
//     double-grab tooth), so a droppable/tradeable item needs a non-`WriteOnce` owner
//     atom plus a sender-bound `AnyOf[HeapField, SenderIs]` transfer gate (the vocabulary
//     exists; this slice does not wire it);
//   * MULTIPLAYER-CONCURRENT holding — one cell is one serial writer (the multi-cell
//     ceiling this crate already names): concurrent independent inventories are a cell
//     per player. The rival-refused tooth here is first-grabber-wins on ONE cell.

/// One item in the general heap-keyed inventory: a single `held_key` in the cell heap
/// (`>= STATE_SLOTS`) plus how the item is USED.
#[derive(Clone, Copy, Debug)]
pub struct InvItem {
    /// A human tag (for docs/printing).
    pub name: &'static str,
    /// The heap key holding the item's owner id (nonzero = held; `WriteOnce`-guarded).
    pub held_key: u64,
    /// How the item is used.
    pub kind: ItemKind,
}

/// How an inventory item is used at the executor.
#[derive(Clone, Copy, Debug)]
pub enum ItemKind {
    /// A gate / key item: `use` is a NON-consuming turn admitted IFF held
    /// (`HeapField { held_key, Gte(1) }`). It bumps `tally_key` (unconstrained) so the
    /// turn carries a real committed effect and repeat-uses are visible.
    Gate {
        /// A benign per-item "times used" heap counter (no tooth — just a receipt).
        tally_key: u64,
    },
    /// A charged consumable: `consume` increments `used_key`, capped at `charges`
    /// (`HeapField { used_key, Lte(charges) }`), and requires the item be held
    /// (`HeapField { held_key, Gte(1) }`).
    Consumable {
        /// The heap key tallying how many charges have been consumed.
        used_key: u64,
        /// The compile-time charge cap (over-consume past it is refused).
        charges: u64,
    },
}

/// The generic pickup dispatch method (one turn-type, N item keys — its case is a
/// conjunction of `WriteOnce` over every registered `held_key`).
pub const HOLD_PICKUP_METHOD: &str = "hold_pickup";
/// The coral key — a contested gate item (its heap owner key).
pub const CORAL_KEY: u64 = 200;
/// The rusted lantern — a second gate item.
pub const RUSTED_LANTERN: u64 = 201;
/// The healing draught — a single-charge consumable (heap held key).
pub const HEALING_DRAUGHT: u64 = 300;
/// The oil flask — a three-charge consumable.
pub const OIL_FLASK: u64 = 301;
/// The thunder rune — a two-charge consumable.
pub const THUNDER_RUNE: u64 = 302;

/// The Tidewrack Hold's registered inventory: SIXTEEN gate relics (keys `200..216`, use-
/// tallies `700..716`) plus THREE consumables (`healing_draught` cap 1, `oil_flask`
/// cap 3, `thunder_rune` cap 2). Nineteen distinct heap-keyed items — more than the 16
/// register slots, so the collection can ONLY live on the heap. Register more freely: the
/// key space is unbounded.
pub fn hold_items() -> Vec<InvItem> {
    let mut items = Vec::new();
    for i in 0..16u64 {
        items.push(InvItem {
            name: "relic",
            held_key: 200 + i,
            kind: ItemKind::Gate { tally_key: 700 + i },
        });
    }
    items.push(InvItem {
        name: "healing_draught",
        held_key: HEALING_DRAUGHT,
        kind: ItemKind::Consumable {
            used_key: 400,
            charges: 1,
        },
    });
    items.push(InvItem {
        name: "oil_flask",
        held_key: OIL_FLASK,
        kind: ItemKind::Consumable {
            used_key: 401,
            charges: 3,
        },
    });
    items.push(InvItem {
        name: "thunder_rune",
        held_key: THUNDER_RUNE,
        kind: ItemKind::Consumable {
            used_key: 402,
            charges: 2,
        },
    });
    items
}

/// The dispatch method for a NON-consuming use of the gate item at `held_key`.
fn hold_use_method(held_key: u64) -> String {
    format!("hold_use_{held_key}")
}

/// The dispatch method for consuming a charge of the item at `held_key`.
fn hold_consume_method(held_key: u64) -> String {
    format!("hold_consume_{held_key}")
}

/// The Tidewrack Hold scene — two rooms (`deck` → `bilge`) so the universe deploys as a
/// real world-cell and supports a stock [`Driver`](spween_dregg::Driver) room playthrough
/// (the heap inventory rides [`WorldCell::apply_raw`] on the same cell).
pub const HOLD: &str = r#"---
id: tidewrack-hold
title: The Tidewrack Hold
weight: 1
---

=== deck

The upper deck of a foundered tidewrack hold, timbers groaning under the swell. A hatch
drops away into the flooded bilge, where the salvage — and the hoard — settled.

* [Descend into the flooded bilge]
  -> bilge

=== bilge

The bilge brims with barnacled salvage and a heaped tidewrack hoard glinting in the murk.

* [Seize the tidewrack hoard]
  ~ gold += 900
  -> END
"#;

/// The Hold's opening room (the deck).
pub const ROOM_DECK: &str = "deck";
/// The Hold's flooded lower room (the bilge — the hoard).
pub const ROOM_BILGE: &str = "bilge";
/// `deck`: descend into the bilge (ungated).
pub const HOLD_DESCEND: usize = 0;
/// `bilge`: seize the hoard (ends the story).
pub const HOLD_SEIZE: usize = 0;

/// Parse the Tidewrack Hold scene.
pub fn hold_scene() -> Scene {
    parse(HOLD, "tidewrack-hold.scene").expect("the hold scene parses")
}

/// **Compile the Hold AND augment its program with the general-inventory teeth.** Adds:
/// the generic [`HOLD_PICKUP_METHOD`] case (a `WriteOnce` per registered heap key), a
/// per-gate-item `hold_use_<key>` case (`Gte(1)`), and a per-consumable
/// `hold_consume_<key>` case (`Gte(held, 1)` + `Lte(used, charges)`). Every case is a real
/// `CellProgram` case the [`EmbeddedExecutor`](dregg_app_framework::EmbeddedExecutor)
/// re-checks move-for-move.
pub fn hold_compiled() -> CompiledStory {
    let mut story = compile_scene(&hold_scene()).expect("the hold compiles");
    let items = hold_items();

    // PICKUP — one generic turn-type gating N distinct heap inserts: a WriteOnce per
    // registered item key. Writing one key leaves the rest untouched (old == new ⇒ their
    // WriteOnce passes idempotently); a rival re-grab of a TAKEN key is refused.
    let pickup_teeth = items
        .iter()
        .map(|it| StateConstraint::HeapField {
            key: it.held_key,
            atom: HeapAtom::WriteOnce,
        })
        .collect();
    add_case(&mut story.program, HOLD_PICKUP_METHOD, pickup_teeth);

    for it in &items {
        match it.kind {
            // USE — a gate item is usable IFF held (Gte(1) on the heap owner key), non-
            // consuming (held key untouched; the use-tally key bumps freely).
            ItemKind::Gate { .. } => add_case(
                &mut story.program,
                &hold_use_method(it.held_key),
                vec![StateConstraint::HeapField {
                    key: it.held_key,
                    atom: HeapAtom::Gte {
                        value: field_from_u64(1),
                    },
                }],
            ),
            // CONSUME — must hold it (Gte(held, 1)) AND the consumed tally may never
            // exceed the charge cap (Lte(used, charges)). Absent held ⇒ use-without-
            // holding refused; used past cap ⇒ over-consume refused.
            ItemKind::Consumable { used_key, charges } => add_case(
                &mut story.program,
                &hold_consume_method(it.held_key),
                vec![
                    StateConstraint::HeapField {
                        key: it.held_key,
                        atom: HeapAtom::Gte {
                            value: field_from_u64(1),
                        },
                    },
                    StateConstraint::HeapField {
                        key: used_key,
                        atom: HeapAtom::Lte {
                            value: field_from_u64(charges),
                        },
                    },
                ],
            ),
        }
    }

    story
}

/// Deploy the augmented Hold as a real world-cell (the inventory teeth installed as
/// executor predicates). Deterministic in `seed` (re-deploy reproduces identity + hashes).
pub fn deploy_hold(seed: u8) -> WorldCell {
    WorldCell::deploy_compiled(Arc::new(hold_compiled()), seed).expect("the hold deploys")
}

/// One general-inventory operation — the abstract, deploy-independent record a
/// [`replay_hold`] re-executes (the effects are re-derived against the fresh cell).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HoldOp {
    /// Insert item `held_key` into the heap under `owner` (`WriteOnce`-guarded).
    Pickup {
        /// The item's heap owner key.
        held_key: u64,
        /// The claiming owner id (nonzero).
        owner: u64,
    },
    /// Use a gate item (non-consuming): bump `tally_key`, gated on holding `held_key`.
    UseGate {
        /// The gate item's heap owner key (must be held).
        held_key: u64,
        /// The item's use-tally heap key (bumped).
        tally_key: u64,
    },
    /// Consume a charge of a consumable: increment `used_key`, gated on holding
    /// `held_key` and staying within the item's charge cap.
    Consume {
        /// The consumable's heap owner key (must be held).
        held_key: u64,
        /// The consumed-tally heap key (incremented; capped by the installed `Lte`).
        used_key: u64,
    },
}

/// Drive one [`HoldOp`] as a real cap-bounded turn via [`WorldCell::apply_raw`]. Reads
/// the current tally/used heap value to compute the next write, then submits — so an
/// executor tooth (WriteOnce / Gte / Lte) refers the turn exactly as on the choice path.
pub fn apply_hold_op(
    world: &WorldCell,
    op: &HoldOp,
) -> Result<dregg_app_framework::TurnReceipt, spween_dregg::WorldError> {
    let cell = world.cell_id();
    match *op {
        HoldOp::Pickup { held_key, owner } => world.apply_raw(
            HOLD_PICKUP_METHOD,
            vec![stash_effect(cell, held_key, owner)],
        ),
        HoldOp::UseGate {
            held_key,
            tally_key,
        } => {
            let cur = world.read_heap(tally_key).unwrap_or(0);
            world.apply_raw(
                &hold_use_method(held_key),
                vec![stash_effect(cell, tally_key, cur + 1)],
            )
        }
        HoldOp::Consume { held_key, used_key } => {
            let used = world.read_heap(used_key).unwrap_or(0);
            world.apply_raw(
                &hold_consume_method(held_key),
                vec![stash_effect(cell, used_key, used + 1)],
            )
        }
    }
}

/// The committed heap projection of every registered item (held + tally/used key), sorted
/// — the deterministic fingerprint [`replay_hold`] reproduces (`None` = absent on the
/// heap, distinct from present-zero).
pub fn hold_heap_snapshot(world: &WorldCell) -> Vec<(u64, Option<u64>)> {
    let mut keys = Vec::new();
    for it in hold_items() {
        keys.push(it.held_key);
        match it.kind {
            ItemKind::Gate { tally_key } => keys.push(tally_key),
            ItemKind::Consumable { used_key, .. } => keys.push(used_key),
        }
    }
    keys.sort_unstable();
    keys.dedup();
    keys.into_iter().map(|k| (k, world.read_heap(k))).collect()
}

/// **Verify-by-replay for the heap inventory.** Re-deploy an identically-seeded Hold and
/// re-apply the SAME [`HoldOp`] sequence, returning the per-step heap snapshots. A forged
/// record (a use whose pickup was dropped) is REFUSED by the real executor on replay,
/// surfacing as `Err((step, why))`. The raw-turn analog of
/// [`spween_dregg::verify_by_replay`] (which replays register-slot choice playthroughs).
pub fn replay_hold(
    seed: u8,
    ops: &[HoldOp],
) -> Result<Vec<Vec<(u64, Option<u64>)>>, (usize, String)> {
    let world = deploy_hold(seed);
    let mut snaps = Vec::with_capacity(ops.len());
    for (i, op) in ops.iter().enumerate() {
        apply_hold_op(&world, op).map_err(|e| (i, e.to_string()))?;
        snaps.push(hold_heap_snapshot(&world));
    }
    Ok(snaps)
}

#[cfg(test)]
mod hold_tests {
    //! The general N-slot heap-keyed inventory, DRIVEN on the real `WorldCell`: multiple
    //! distinct items held via the heap; the right item's use commits; an unheld item's
    //! use / a rival re-grab of a taken key / a consumed item's re-use are all REAL
    //! executor refusals that commit NOTHING (anti-ghost).
    use super::*;
    use spween_dregg::{Driver, WorldError, verify, verify_chain_linkage};

    /// The inventory teeth are REAL kernel predicates: the pickup case carries a
    /// `WriteOnce` for every item key; each gate use is `Gte(1)`; each consume is
    /// `Gte(held, 1)` + `Lte(used, charges)`.
    #[test]
    fn hold_teeth_are_real_kernel_predicates() {
        let story = hold_compiled();

        let pickup = case_constraints(&story, HOLD_PICKUP_METHOD);
        for it in hold_items() {
            assert!(
                pickup.iter().any(|c| matches!(
                    c,
                    StateConstraint::HeapField { key, atom: HeapAtom::WriteOnce }
                        if *key == it.held_key
                )),
                "pickup gates WriteOnce on heap key {}",
                it.held_key
            );
        }

        let use_coral = case_constraints(&story, &hold_use_method(CORAL_KEY));
        assert!(
            use_coral.iter().any(|c| matches!(
                c,
                StateConstraint::HeapField { key, atom: HeapAtom::Gte { value } }
                    if *key == CORAL_KEY && *value == field_from_u64(1)
            )),
            "coral-key use is HeapField Gte(1); got {use_coral:?}"
        );

        let consume = case_constraints(&story, &hold_consume_method(HEALING_DRAUGHT));
        assert!(
            consume.iter().any(|c| matches!(
                c,
                StateConstraint::HeapField { key, atom: HeapAtom::Gte { value } }
                    if *key == HEALING_DRAUGHT && *value == field_from_u64(1)
            )),
            "draught consume requires holding (Gte(held,1)); got {consume:?}"
        );
        assert!(
            consume.iter().any(|c| matches!(
                c,
                StateConstraint::HeapField { key, atom: HeapAtom::Lte { value } }
                    if *key == 400 && *value == field_from_u64(1)
            )),
            "draught consume is capped (Lte(used,1)); got {consume:?}"
        );
    }

    /// The general inventory holds MULTIPLE DISTINCT items at once — nineteen, more than
    /// the 16 register slots, so the collection can only live on the heap.
    #[test]
    fn hold_multiple_distinct_items_via_heap() {
        let world = deploy_hold(30);
        let cell = world.cell_id();

        for it in hold_items() {
            world
                .apply_raw(HOLD_PICKUP_METHOD, vec![stash_effect(cell, it.held_key, 1)])
                .unwrap_or_else(|e| panic!("pickup of heap item {} commits: {e}", it.held_key));
            assert_eq!(
                world.read_heap(it.held_key),
                Some(1),
                "the heap holds item {}",
                it.held_key
            );
        }

        let held = hold_items()
            .iter()
            .filter(|it| world.read_heap(it.held_key) == Some(1))
            .count();
        assert!(
            held >= 17,
            "the heap holds {held} distinct items at once (> 16 registers)"
        );
    }

    /// USE the right item — the held coral key's use COMMITS (its tally bumps); an UNHELD
    /// item's use is a REAL executor refusal that commits nothing.
    #[test]
    fn use_right_item_commits_unheld_refused() {
        let world = deploy_hold(31);
        let cell = world.cell_id();

        // Hold ONLY the coral key.
        world
            .apply_raw(HOLD_PICKUP_METHOD, vec![stash_effect(cell, CORAL_KEY, 1)])
            .expect("grab the coral key");

        // Using the held coral key commits (tally 700: absent → 1).
        apply_hold_op(
            &world,
            &HoldOp::UseGate {
                held_key: CORAL_KEY,
                tally_key: 700,
            },
        )
        .expect("using a held gate item commits");
        assert_eq!(world.read_heap(700), Some(1), "the coral key was used once");

        // Using the UNHELD rusted lantern fails FieldGte(held, 1) — a real refusal.
        let refused = apply_hold_op(
            &world,
            &HoldOp::UseGate {
                held_key: RUSTED_LANTERN,
                tally_key: 701,
            },
        );
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "using an unheld item is refused, got {refused:?}"
        );
        assert_eq!(
            world.read_heap(701),
            None,
            "anti-ghost: the unheld lantern left no use-tally"
        );
    }

    /// A RIVAL grabbing a TAKEN heap key is refused (WriteOnce, first-grabber-wins).
    #[test]
    fn rival_regrab_of_taken_key_refused() {
        let world = deploy_hold(32);
        let cell = world.cell_id();

        world
            .apply_raw(HOLD_PICKUP_METHOD, vec![stash_effect(cell, CORAL_KEY, 1)])
            .expect("the first crew grabs the coral key (owner 1)");
        assert_eq!(world.read_heap(CORAL_KEY), Some(1));

        // A rival crew grabs the SAME heap key for a different owner (1 → 2): WriteOnce
        // refuses — the key is already taken.
        let refused = world.apply_raw(HOLD_PICKUP_METHOD, vec![stash_effect(cell, CORAL_KEY, 2)]);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a rival re-grab of a taken heap key is refused (WriteOnce), got {refused:?}"
        );
        assert_eq!(
            world.read_heap(CORAL_KEY),
            Some(1),
            "anti-ghost: the coral key still belongs to the first grabber"
        );
    }

    /// CONSUME requires holding, and a consumed charge cannot be re-used past the cap.
    #[test]
    fn consume_requires_holding_and_caps_reuse() {
        let world = deploy_hold(33);
        let cell = world.cell_id();

        // Consume with NOTHING held — use-without-holding on a consumable: refused.
        let refused = apply_hold_op(
            &world,
            &HoldOp::Consume {
                held_key: HEALING_DRAUGHT,
                used_key: 400,
            },
        );
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "consuming an unheld draught is refused (Gte(held,1)), got {refused:?}"
        );
        assert_eq!(world.read_heap(400), None, "anti-ghost: nothing consumed");

        // Pocket the single-charge draught, then the first consume commits (used 0 → 1).
        world
            .apply_raw(
                HOLD_PICKUP_METHOD,
                vec![stash_effect(cell, HEALING_DRAUGHT, 1)],
            )
            .expect("pocket the healing draught");
        apply_hold_op(
            &world,
            &HoldOp::Consume {
                held_key: HEALING_DRAUGHT,
                used_key: 400,
            },
        )
        .expect("the first consume of a held draught commits");
        assert_eq!(world.read_heap(400), Some(1));

        // A SECOND consume of the single-charge item (used 1 → 2 > cap 1): refused.
        let over = apply_hold_op(
            &world,
            &HoldOp::Consume {
                held_key: HEALING_DRAUGHT,
                used_key: 400,
            },
        );
        assert!(
            matches!(over, Err(WorldError::Refused(_))),
            "a consumed single-charge item cannot be re-used (Lte cap), got {over:?}"
        );
        assert_eq!(
            world.read_heap(400),
            Some(1),
            "anti-ghost: the consumed tally did not advance"
        );

        // A three-charge item: three consumes commit; the fourth over-consumes and refuses.
        world
            .apply_raw(HOLD_PICKUP_METHOD, vec![stash_effect(cell, OIL_FLASK, 1)])
            .expect("pocket the oil flask");
        for _ in 0..3 {
            apply_hold_op(
                &world,
                &HoldOp::Consume {
                    held_key: OIL_FLASK,
                    used_key: 401,
                },
            )
            .expect("a charge within the cap consumes");
        }
        assert_eq!(world.read_heap(401), Some(3));
        let over = apply_hold_op(
            &world,
            &HoldOp::Consume {
                held_key: OIL_FLASK,
                used_key: 401,
            },
        );
        assert!(
            matches!(over, Err(WorldError::Refused(_))),
            "consuming past the 3-charge cap is refused, got {over:?}"
        );
    }

    /// The general inventory REPLAYS deterministically (verify-by-replay), and a retconned
    /// record — a use whose pickup was dropped — is REFUSED by the executor on replay.
    #[test]
    fn hold_inventory_replays_and_a_retcon_fails() {
        let ops = vec![
            HoldOp::Pickup {
                held_key: CORAL_KEY,
                owner: 1,
            },
            HoldOp::Pickup {
                held_key: RUSTED_LANTERN,
                owner: 1,
            },
            HoldOp::Pickup {
                held_key: HEALING_DRAUGHT,
                owner: 1,
            },
            HoldOp::UseGate {
                held_key: CORAL_KEY,
                tally_key: 700,
            },
            HoldOp::UseGate {
                held_key: RUSTED_LANTERN,
                tally_key: 701,
            },
            HoldOp::Consume {
                held_key: HEALING_DRAUGHT,
                used_key: 400,
            },
        ];

        let a = replay_hold(40, &ops).expect("the honest inventory playthrough commits");
        let b = replay_hold(40, &ops).expect("re-deploy + re-apply reproduces it");
        assert_eq!(
            a, b,
            "the general inventory replays deterministically (verify-by-replay)"
        );
        // The end state: both gate keys held+used once, the draught held+consumed once.
        let last = a.last().expect("at least one step");
        assert!(last.contains(&(CORAL_KEY, Some(1))));
        assert!(last.contains(&(700, Some(1))));
        assert!(last.contains(&(HEALING_DRAUGHT, Some(1))));
        assert!(last.contains(&(400, Some(1))));

        // Retcon: SKIP grabbing the coral key but keep using it. On replay the coral-key
        // use (now index 2, after the two remaining pickups) is REFUSED — the record cannot
        // pass, exactly as a choice-path retcon fails `verify_by_replay`.
        let mut forged = ops.clone();
        forged.remove(0);
        match replay_hold(40, &forged) {
            Err((step, why)) => {
                assert_eq!(step, 2, "the unheld coral-key use is the refusing step");
                assert!(
                    why.contains("refused"),
                    "the retcon fails by a real executor refusal, got {why}"
                );
            }
            Ok(_) => panic!("a retconned key-skip must not replay clean"),
        }
    }

    /// The room-scene half of this universe still re-verifies through the STOCK
    /// [`spween_dregg::verify`] machinery unchanged — the heap inventory is fully additive.
    #[test]
    fn hold_room_playthrough_reverifies() {
        let s = hold_scene();
        let mut driver = Driver::start(deploy_hold(41), &s).expect("start the hold");

        driver
            .advance(HOLD_DESCEND)
            .expect("descend into the bilge");
        driver.advance(HOLD_SEIZE).expect("seize the hoard");
        assert!(driver.is_ended(), "the hold is cleared");
        assert_eq!(driver.world().read_var("gold"), 900);

        let play = driver.playthrough();
        assert_eq!(play.receipts().len(), 3, "genesis + 2 moves");
        verify_chain_linkage(&play).expect("the hold receipt chain links");
        verify(deploy_hold(41), &s, &play).expect("the honest hold playthrough re-verifies");
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// A FOURTH UNIVERSE — "The Merchant's Bazaar": an ECONOMY (buy / sell) + QUANTITIES
// ═══════════════════════════════════════════════════════════════════════════════
//
// The Keep proved rules-as-teeth; the Sunken Vault proved item pickup/use; the
// Tidewrack Hold proved an unbounded heap-keyed inventory. The Bazaar deepens all
// three with the mechanic they all lacked: **an economy** — a shop where a purse of
// gold BUYS goods and goods SELL back for gold, and where an item is held in a real
// QUANTITY that a use DECREMENTS to zero. Every rule below is a real
// [`StateConstraint`] the verified [`EmbeddedExecutor`](dregg_app_framework::EmbeddedExecutor)
// re-checks on the turn's post-state — never app bookkeeping, identical enforcement
// to the three worlds before it.
//
// ── THE PROBLEM AN ECONOMY POSES (and why the obvious gate is VACUOUS) ────────────
//
// The natural shop rule is "you cannot buy what you cannot afford" — pre-state
// `gold >= price`. But every tooth here is a POST-state predicate, and the compiler
// lifts a pre-condition through the move's own net delta
// (`compare_constraint`: `pre >= base` ⟺ `post >= base + d`). A purchase's delta is
// exactly `−price`, so `{ gold >= 50 } ~ gold -= 50` lifts to `FieldGte(gold, 0)` —
// **VACUOUS**: an unsigned slot is always `>= 0`. Worse, [`WorldCell::apply_choice`]
// CLAMPS a Modify at zero (`(cur + delta).max(0)`), so a broke player's purchase would
// commit with the purse silently clamped to 0 and the goods delivered. A `FieldGte`
// gold gate on the paying move itself is NOT a balance tooth; it is a no-op.
//
// ── THE REAL BALANCE TOOTH: `StateConstraint::FieldDelta` (EXACT PAYMENT) ─────────
//
// The atom that bites is the exact-delta transition predicate
// [`StateConstraint::FieldDelta`] — `new[gold] == old[gold] + delta` over the u64
// lane (`field_add`, wrapping). Install `FieldDelta { gold, −price }` on the buy case:
//
//   * AFFORDABLE (`gold = 120`, price 50): the driver writes `120 − 50 = 70`; the tooth
//     recomputes `120 + (2^64 − 50) mod 2^64 = 70` — ADMITTED, and the item lands on
//     the SAME turn (one action, all-or-nothing).
//   * BROKE (`gold = 30`, price 50): the clamp writes `0`; the tooth recomputes
//     `30 − 50 mod 2^64` (a huge value) `≠ 0` — **REFUSED**. Nothing commits: no goods,
//     no gold movement (anti-ghost). The underflow the clamp would have swallowed is
//     exactly what the kernel predicate catches.
//   * FORGED (a raw turn paying less, or a sale minting `gold = 9999`): the post-state
//     is not `old ± price` — REFUSED. The price schedule is the kernel's, not the
//     client's: no underpaying, no ghost-minting.
//
// Boundary: spending your LAST coin (`gold == price`) commits exactly (`new == 0 ==
// old − price`) — the tooth is exact, not a "keep one coin" hack.
//
// ── QUANTITIES (a held-count a use DECREMENTS, and the floor at zero) ─────────────
//
// The same atom is the sound DECREMENT gate. A held count lives in a register slot;
// a use writes `held − 1` under `FieldDelta { held, −1 }`. With `held == 0` the clamp
// writes `0`, the tooth expects `0 − 1 mod 2^64` — REFUSED. So a quantity walks
// `3 → 2 → 1 → 0` on real committed turns and the next use is a REAL executor refusal:
// "the count hits zero and the stack is spent." The Hold's `Gte(1)`/`Lte(cap)` heap
// pair models a use-TALLY against a compile-time cap; `FieldDelta` models the LIVE
// held count itself — the two are complementary, and the Bazaar drives both shapes
// (`FieldLte` caps the merchant's STOCK; `FieldDelta` decrements the player's STACK).
//
// ── THE FULL TOOTH TABLE (every rule a kernel predicate) ─────────────────────────
//
// | move (method)              | executor teeth                                                              |
// |----------------------------|-----------------------------------------------------------------------------|
// | buy potion (50g)           | `FieldDelta{gold,−50}` + `FieldDelta{potions,+1}` + `FieldLte{potions_bought,2}` (merchant STOCK) + `Monotonic{potions_bought}` (no forged restock) |
// | buy torch bundle (30g, ×3) | `FieldDelta{gold,−30}` + `FieldDelta{torches,+3}` (exact bundle)             |
// | sell amulet (+120g)        | `FieldDelta{amulet,−1}` (must HOLD it: 0 ⇒ refused) + `FieldDelta{gold,+120}` (exact price, no mint) |
// | enter the counting room    | `FieldGte{gold,100}` (compiler-emitted; the move does NOT touch gold, so the threshold stands — a genuine solvency gate) |
// | rob the niche              | `FieldLte{niches_robbed,1}` (the niche holds ONE amulet) + `Monotonic{niches_robbed}` + `FieldDelta{amulet,+1}` |
// | drink a potion             | `FieldDelta{potions,−1}` (quantity decrement; 0 ⇒ refused) + `FieldDelta{hp,+25}` (exact heal) |
// | light a torch              | `FieldDelta{torches,−1}` (quantity decrement) + `Monotonic{wards_lit}`       |
// | trade a blow               | `FieldGte{hp,1}` (compiler-emitted HP floor — a killing blow is refused)     |
// | seize the takings          | `FieldDelta{gold,+500}` (exact hoard)                                        |
//
// ── HONEST SCOPE — gold is a COUNTER, not a conserved `Effect::Transfer` ──────────
//
// dregg HAS a conserved value move — [`dregg_app_framework::Effect::Transfer`], which
// debits `from` and credits `to` atomically and REFUSES a source that would go below
// zero (`TurnError::InsufficientBalance`, `turn/src/executor/apply.rs`). It is NOT
// usable as this game's gold, and the reason is DRIVEN, not asserted, in
// [`bazaar_tests::conserved_transfer_is_out_of_reach_gold_is_a_counter`]:
//
//   * the value it moves is **computrons** — the substrate's fee/resource currency
//     (every turn burns `fee = 10_000` from the agent cell), so game gold would be
//     spent by the act of playing;
//   * the world-cell is born with **balance 0** and `Effect::CreateCell` REFUSES a
//     nonzero balance (`CreateCellNonZeroBalance` — no minting), so a Transfer out of
//     the world-cell is refused for insufficient balance (the test drives exactly this);
//   * `spween-dregg` exposes cell FIELDS ([`WorldCell::seed_var`]), not cell BALANCES —
//     nothing in this crate's reach can fund a purse of computrons;
//   * and a real merchant would be a SECOND cell — the multi-cell ceiling this crate
//     already names (one cell is one serial writer).
//
// So the Bazaar's gold is a **counter with an exact-delta kernel tooth**: sound against
// underflow, underpayment and minting WITHIN this cell's serialized history, but not
// globally conserved (the niche's amulet and the counting-room hoard are created; the
// merchant's payments are not debited from a merchant's purse). A conserved-Transfer
// economy is a real, reachable NEXT rung — it needs a merchant CELL funded through the
// substrate's issuance path plus the cross-cell `Send` permission, i.e. the multi-cell
// universe, not this one.
//
// What a FULLER economy adds beyond this slice:
//   * **multi-item baskets** — one turn buying N distinct goods at once. Reachable
//     TODAY (a case's constraints are a conjunction: one `FieldDelta` per good + one
//     for the summed price), but the v0 scene compiler has no basket syntax; it would
//     be an augmented raw-turn method like the Hold's `hold_pickup`.
//   * **dynamic pricing** (supply/demand, haggling) — `FieldDelta` pins ONE price per
//     case, so a price that MOVES needs either a case per price point or a cross-slot
//     "pay at least the posted price" atom. The vocabulary's [`StateConstraint::FieldLteOther`]
//     (`new[a] <= new[b] + delta`) can express "the purse fell by at least the posted
//     price slot" — a real closure lane, not a hole.
//   * **cross-player trade** — two purses on two cells: cross-cell, hence the
//     `Witnessed`/`ObservedFieldEquals` machinery the [`multicell`] module already
//     wires, or a conserved `Effect::Transfer` between player cells.
//
// ── NAMED ATOM GAP (nothing added to the core; designed around) ───────────────────
//
// The heap vocabulary ([`HeapAtom`]) has NO exact-delta twin (`Equals`/`Gte`/`Lte`/
// `WriteOnce`/`Monotonic`/`StrictMonotonic`/`MemberOf`/`InRangeTwoSided`/`DeltaBounded`
// — `DeltaBounded` bounds |Δ| but does not PIN it, so it cannot refuse a broke
// purchase's clamped write). A heap-keyed quantity therefore CANNOT carry the
// exact-payment/exact-decrement tooth that makes this economy sound; the Bazaar's
// purse and stacks live in REGISTER slots for exactly that reason (8 of the 15 usable
// slots). The gap is `HeapAtom::Delta { d: i64 }` (the heap twin of
// `StateConstraint::FieldDelta`) — plus a heap cross-key `Lte` for a live
// `consumed <= held` bound, which the Hold already named. Both belong in
// `cell/src/program/` (+ the Lean twin + the AIR), which is OUT OF SCOPE here; the
// Bazaar is built entirely from atoms that already exist.

/// The fourth dungeon — "The Merchant's Bazaar" — in the spween DSL. Three rooms: the
/// `bazaar` (the shop: buy potions/torches, sell the amulet, pay into the counting
/// room), the `ossuary` (rob the niche, fight the warden, and SPEND the goods —
/// quantities decrementing to zero), and the `counting_room` (the takings). The
/// economy RULES lower to real executor teeth (see [`bazaar_compiled`]).
pub const BAZAAR: &str = r#"---
id: merchants-bazaar
title: The Merchant's Bazaar
weight: 1
---

=== coast_road

~ gold = 120
~ hp = 40

The coast road at low tide, a purse of a hundred and twenty on your hip. Ahead, the
awnings of the bazaar snap in the wind.

* [Step under the awnings]
  -> bazaar

=== bazaar

An awning of salt-stiff canvas, a merchant with a ledger, and a locked counting room
where the season's takings are stacked. The prices are posted. The merchant does not
haggle, does not extend credit, and does not open the counting room to a pauper.

* [Buy a healing potion for 50 gold]
  ~ gold -= 50
  ~ potions += 1
  ~ potions_bought += 1
  -> bazaar

* [Buy a bundle of three pitch torches for 30 gold]
  ~ gold -= 30
  ~ torches += 3
  -> bazaar

* [Sell the amber amulet for 120 gold]
  ~ amulet -= 1
  ~ gold += 120
  -> bazaar

* [Pay your way into the counting room] { gold >= 100 }
  -> counting_room

* [Take the stair down to the ossuary]
  -> ossuary

=== ossuary

Bone-dust and cold. An ossuary warden turns its head. In a niche in the far wall an
amulet of black amber waits — and a niche is robbed only once.

* [Rob the niche of its amber amulet]
  ~ niches_robbed += 1
  ~ amulet += 1
  -> ossuary

* [Trade a blow with the ossuary warden] { hp >= 16 }
  ~ hp -= 15
  -> ossuary

* [Drink a healing potion]
  ~ potions -= 1
  ~ hp += 25
  -> ossuary

* [Light a pitch torch]
  ~ torches -= 1
  ~ wards_lit += 1
  -> ossuary

* [Climb back to the bazaar]
  -> bazaar

=== counting_room

The counting room. The season's takings, stacked and unguarded.

* [Seize the season's takings]
  ~ gold += 500
  -> END
"#;

// ── Bazaar room / choice coordinates + the posted price schedule ─────────────────
//
// NOTE (a real behaviour, found by DRIVING): the opening purse is seeded by the INTRO
// passage's entry effects, and a spween passage RE-RUNS its entry effects when it is
// re-entered by navigation. If the shop itself were the intro room, walking back into
// it from the ossuary would RE-SEED the purse (`gold = 120` again) — a refill glitch,
// riding an untoothed move (the return walk carries no economy tooth to refuse it).
// So the economy's seed lives in `coast_road`, a room the story never returns to.

/// The opening room (never re-entered): seeds the purse + HP as genesis entry effects.
pub const ROOM_COAST_ROAD: &str = "coast_road";
/// The shop room: buy, sell, and the gold-gated counting-room door.
pub const ROOM_BAZAAR: &str = "bazaar";
/// The ossuary: the niche (the sellable amulet), the warden, and where goods are SPENT.
pub const ROOM_OSSUARY: &str = "ossuary";
/// The counting room (terminal): the season's takings.
pub const ROOM_COUNTING_ROOM: &str = "counting_room";

/// `coast_road`: step under the awnings into the bazaar (ungated).
pub const BAZ_ENTER: usize = 0;
/// `bazaar`: BUY one healing potion — pays [`POTION_PRICE`], receives 1 potion.
pub const BAZ_BUY_POTION: usize = 0;
/// `bazaar`: BUY a bundle of [`TORCH_BUNDLE`] pitch torches — pays [`TORCH_BUNDLE_PRICE`].
pub const BAZ_BUY_TORCHES: usize = 1;
/// `bazaar`: SELL the amber amulet — gives up 1 amulet, receives [`AMULET_PRICE`].
pub const BAZ_SELL_AMULET: usize = 2;
/// `bazaar`: pay into the counting room — refused below [`COUNTING_ROOM_TOLL`] gold.
pub const BAZ_COUNTING_ROOM: usize = 3;
/// `bazaar`: take the stair down to the ossuary (ungated).
pub const BAZ_TO_OSSUARY: usize = 4;
/// `ossuary`: rob the niche (+1 amulet) — the niche holds exactly one.
pub const BAZ_ROB_NICHE: usize = 0;
/// `ossuary`: trade a blow with the warden (−15 HP, HP-floor gated).
pub const BAZ_TRADE_BLOW: usize = 1;
/// `ossuary`: drink a potion (quantity −1, +[`POTION_HEAL`] HP) — refused at zero held.
pub const BAZ_DRINK: usize = 2;
/// `ossuary`: light a torch (quantity −1) — refused at zero held.
pub const BAZ_LIGHT_TORCH: usize = 3;
/// `ossuary`: climb back to the bazaar (ungated).
pub const BAZ_CLIMB_BACK: usize = 4;
/// `counting_room`: seize the takings (ends the story).
pub const BAZ_SEIZE: usize = 0;

/// The posted price of one healing potion (gold).
pub const POTION_PRICE: u64 = 50;
/// The posted price of one bundle of pitch torches (gold).
pub const TORCH_BUNDLE_PRICE: u64 = 30;
/// How many torches a bundle contains (the QUANTITY a single purchase delivers).
pub const TORCH_BUNDLE: u64 = 3;
/// What the merchant pays for the amber amulet (gold).
pub const AMULET_PRICE: u64 = 120;
/// The merchant's STOCK: how many potions exist to be sold, ever (a `FieldLte` cap on
/// the purchase tally — the (n+1)-th purchase is refused even with gold in hand).
pub const POTION_STOCK: u64 = 2;
/// What the counting-room door demands you can show (gold) — a real `FieldGte` tooth.
pub const COUNTING_ROOM_TOLL: u64 = 100;
/// What one potion heals.
pub const POTION_HEAL: u64 = 25;
/// The season's takings, seized in the counting room.
pub const COUNTING_ROOM_TAKINGS: u64 = 500;
/// The purse the story opens with (a genesis entry effect).
pub const OPENING_PURSE: u64 = 120;

/// The field element for a NEGATIVE u64 delta — the additive inverse of `n` in the
/// executor's u64 lane (`field_add` wraps: `old + neg(n) == old − n mod 2^64`). The
/// encoding [`StateConstraint::FieldDelta`]'s doc names for a decrement.
fn field_neg_u64(n: u64) -> dregg_app_framework::FieldElement {
    field_from_u64(0u64.wrapping_sub(n))
}

/// An EXACT-payment / exact-delivery / exact-decrement tooth on `slot`: the post-state
/// slot must be `old + delta` on the nose. A clamped underflow (a purchase you cannot
/// afford, a use with nothing held) lands a value that is NOT `old + delta` and is
/// REFUSED by the real executor.
fn exact_delta(slot: u8, delta: i64) -> StateConstraint {
    StateConstraint::FieldDelta {
        index: slot,
        delta: if delta >= 0 {
            field_from_u64(delta as u64)
        } else {
            field_neg_u64(delta.unsigned_abs())
        },
    }
}

/// Parse the Merchant's Bazaar scene.
pub fn bazaar_scene() -> Scene {
    parse(BAZAAR, "merchants-bazaar.scene").expect("the bazaar scene parses")
}

/// **Compile the Bazaar AND augment its program with the economy + quantity teeth.**
/// The HP floor (`FieldGte(hp, 1)`) and the counting-room solvency gate
/// (`FieldGte(gold, 100)`) are compiler-emitted from the scene's conditions; this adds
/// the shapes the v0 compiler cannot express — the exact-delta payment/delivery/
/// decrement teeth ([`StateConstraint::FieldDelta`]), the merchant's stock cap
/// (`FieldLte`) and the anti-restock / anti-rewind ratchets (`Monotonic`) — as real
/// `CellProgram` cases the executor re-checks move-for-move.
pub fn bazaar_compiled() -> CompiledStory {
    let mut story = compile_scene(&bazaar_scene()).expect("the bazaar compiles");

    let gold = keep_slot(&story, "gold");
    let hp = keep_slot(&story, "hp");
    let potions = keep_slot(&story, "potions");
    let potions_bought = keep_slot(&story, "potions_bought");
    let torches = keep_slot(&story, "torches");
    let amulet = keep_slot(&story, "amulet");
    let niches_robbed = keep_slot(&story, "niches_robbed");
    let wards_lit = keep_slot(&story, "wards_lit");

    // BUY a potion — the purse falls by EXACTLY the price (a purchase you cannot
    // afford clamps to 0 ≠ old − price and is REFUSED: the real balance tooth), the
    // potion lands on the SAME turn (so goods NEVER arrive without payment), the
    // merchant's stock caps the purchase tally, and the tally cannot be rewound
    // (a forged restock is refused).
    augment_case(
        &mut story.program,
        &choice_method(ROOM_BAZAAR, BAZ_BUY_POTION),
        vec![
            exact_delta(gold, -(POTION_PRICE as i64)),
            exact_delta(potions, 1),
            StateConstraint::FieldLte {
                index: potions_bought,
                value: field_from_u64(POTION_STOCK),
            },
            StateConstraint::Monotonic {
                index: potions_bought,
            },
        ],
    );

    // BUY a torch bundle — exact payment, and the bundle delivers EXACTLY three
    // torches (a QUANTITY landing in one turn).
    augment_case(
        &mut story.program,
        &choice_method(ROOM_BAZAAR, BAZ_BUY_TORCHES),
        vec![
            exact_delta(gold, -(TORCH_BUNDLE_PRICE as i64)),
            exact_delta(torches, TORCH_BUNDLE as i64),
        ],
    );

    // SELL the amulet — you must HOLD one (`amulet: 0` clamps to 0 ≠ −1 ⇒ REFUSED),
    // and the merchant pays EXACTLY the posted price (a forged sale minting more gold
    // is refused: the price schedule is the kernel's).
    augment_case(
        &mut story.program,
        &choice_method(ROOM_BAZAAR, BAZ_SELL_AMULET),
        vec![
            exact_delta(amulet, -1),
            exact_delta(gold, AMULET_PRICE as i64),
        ],
    );

    // ROB the niche — it holds exactly ONE amulet (`FieldLte(1)` on the robbery tally),
    // the tally ratchets (no forged re-robbery by rewinding it), and the amulet lands
    // exactly once per robbery.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_OSSUARY, BAZ_ROB_NICHE),
        vec![
            StateConstraint::FieldLte {
                index: niches_robbed,
                value: field_from_u64(1),
            },
            StateConstraint::Monotonic {
                index: niches_robbed,
            },
            exact_delta(amulet, 1),
        ],
    );

    // DRINK a potion — the held QUANTITY decrements by exactly one (drinking with none
    // held is REFUSED), and the heal is exactly what a potion heals (no ghost-heal).
    augment_case(
        &mut story.program,
        &choice_method(ROOM_OSSUARY, BAZ_DRINK),
        vec![
            exact_delta(potions, -1),
            exact_delta(hp, POTION_HEAL as i64),
        ],
    );

    // LIGHT a torch — the held QUANTITY decrements by exactly one (the stack walks
    // 3 → 2 → 1 → 0 and the next light is REFUSED), and the lit-ward tally ratchets.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_OSSUARY, BAZ_LIGHT_TORCH),
        vec![
            exact_delta(torches, -1),
            StateConstraint::Monotonic { index: wards_lit },
        ],
    );

    // SEIZE the takings — exactly the season's takings, no more (no ghost-minting on
    // the terminal move either).
    augment_case(
        &mut story.program,
        &choice_method(ROOM_COUNTING_ROOM, BAZ_SEIZE),
        vec![exact_delta(gold, COUNTING_ROOM_TAKINGS as i64)],
    );

    story
}

/// Deploy the augmented Bazaar as a real world-cell (the economy + quantity teeth
/// installed as executor predicates). Deterministic in `seed` (a re-deploy reproduces
/// the same cell identity + state hashes — what the replay verifier leans on).
pub fn deploy_bazaar(seed: u8) -> WorldCell {
    WorldCell::deploy_compiled(Arc::new(bazaar_compiled()), seed).expect("the bazaar deploys")
}

#[cfg(test)]
mod bazaar_tests {
    //! The economy, DRIVEN on the real `WorldCell`: a buy with gold enough COMMITS
    //! (gold down, goods up); a buy you cannot afford is a REAL executor refusal that
    //! commits NOTHING (no goods, no gold movement); a sale requires holding the item;
    //! a quantity DECREMENTS on use and, at zero, the next use is refused. Plus the
    //! forged-turn teeth (underpay / mint / restock) and the honest-scope probe that
    //! DRIVES why gold is a counter and not a conserved `Effect::Transfer`.
    use super::*;
    use dregg_app_framework::CellId;
    use spween_dregg::{
        Driver, StepPos, Value, VerifyBreak, WorldError, verify, verify_by_replay,
        verify_chain_linkage,
    };

    /// Seed a bazaar at the executor level (the direct-executor tests bypass genesis so
    /// the executor is the SOLE referee — the same pattern the Keep/Vault tests use).
    fn seeded(seed: u8, gold: u64) -> WorldCell {
        let mut world = deploy_bazaar(seed);
        world.seed_var("gold", Value::Int(gold as i64));
        world.seed_var("hp", Value::Int(40));
        world
    }

    /// A raw `SetField` on a REGISTER slot of the bazaar cell (the forged-turn tests
    /// drive these directly at the executor, bypassing the honest driver arithmetic).
    fn raw_set(cell: CellId, slot: u8, value: u64) -> Effect {
        stash_effect(cell, slot as u64, value)
    }

    /// The executor's VERBATIM refusal reason (panics if the turn was not refused).
    /// The refusal tests below check the reason against the SPECIFIC tooth that bit —
    /// so a test cannot pass on an incidental error that merely happens to refuse.
    fn why<T: std::fmt::Debug>(out: Result<T, WorldError>) -> String {
        match out {
            Err(WorldError::Refused(reason)) => reason,
            other => panic!("expected a REAL executor refusal, got {other:?}"),
        }
    }

    /// How the executor reports an exact-delta (`FieldDelta`) violation on a slot.
    fn delta_violation(slot: u8) -> String {
        format!("field[{slot}] != old + delta")
    }

    /// The slot of a named bazaar var (the refusal reasons name slots, not var names).
    fn slot_of(name: &str) -> u8 {
        keep_slot(&bazaar_compiled(), name)
    }

    /// Every economy rule is a REAL kernel predicate: introspect the installed program
    /// and read back the exact-payment / exact-delivery / stock / solvency / decrement
    /// teeth. (Not a name: the constraint VALUES are checked against the posted prices.)
    #[test]
    fn bazaar_economy_teeth_are_real_kernel_predicates() {
        let story = bazaar_compiled();
        let gold = keep_slot(&story, "gold");
        let potions = keep_slot(&story, "potions");
        let potions_bought = keep_slot(&story, "potions_bought");
        let torches = keep_slot(&story, "torches");
        let amulet = keep_slot(&story, "amulet");
        let hp = keep_slot(&story, "hp");

        // BUY: the purse falls by EXACTLY the posted price, and exactly one potion lands.
        let buy = case_constraints(&story, &choice_method(ROOM_BAZAAR, BAZ_BUY_POTION));
        assert!(
            buy.contains(&exact_delta(gold, -(POTION_PRICE as i64))),
            "buy pays EXACTLY {POTION_PRICE} (FieldDelta on gold); got {buy:?}"
        );
        assert!(
            buy.contains(&exact_delta(potions, 1)),
            "buy delivers EXACTLY one potion (FieldDelta); got {buy:?}"
        );
        // ...and the merchant's stock caps the purchase tally (a real FieldLte).
        assert!(
            buy.iter().any(|c| matches!(
                c,
                StateConstraint::FieldLte { index, value }
                    if *index == potions_bought && *value == field_from_u64(POTION_STOCK)
            )),
            "the merchant's stock is FieldLte(potions_bought, {POTION_STOCK}); got {buy:?}"
        );
        assert!(
            buy.iter().any(
                |c| matches!(c, StateConstraint::Monotonic { index } if *index == potions_bought)
            ),
            "the purchase tally ratchets (no forged restock); got {buy:?}"
        );

        // BUNDLE: one purchase delivers a QUANTITY of three.
        let torch = case_constraints(&story, &choice_method(ROOM_BAZAAR, BAZ_BUY_TORCHES));
        assert!(
            torch.contains(&exact_delta(torches, TORCH_BUNDLE as i64)),
            "the bundle delivers EXACTLY {TORCH_BUNDLE} torches; got {torch:?}"
        );

        // SELL: give up exactly one amulet, receive exactly the posted price.
        let sell = case_constraints(&story, &choice_method(ROOM_BAZAAR, BAZ_SELL_AMULET));
        assert!(
            sell.contains(&exact_delta(amulet, -1)),
            "a sale gives up EXACTLY one amulet (and 0-held ⇒ refused); got {sell:?}"
        );
        assert!(
            sell.contains(&exact_delta(gold, AMULET_PRICE as i64)),
            "a sale pays EXACTLY {AMULET_PRICE} (no minting); got {sell:?}"
        );

        // The counting-room door is a real compiler-emitted SOLVENCY gate on gold — and
        // it is fully executor-enforced (the move does not touch gold, so the threshold
        // survives the net-delta lift: a genuine FieldGte, not a vacuous `>= 0`).
        let m_door = choice_method(ROOM_BAZAAR, BAZ_COUNTING_ROOM);
        assert_eq!(
            story.fully_gated.get(&m_door),
            Some(&true),
            "the counting-room door is fully executor-enforced"
        );
        let door = case_constraints(&story, &m_door);
        assert!(
            door.iter().any(|c| matches!(
                c,
                StateConstraint::FieldGte { index, value }
                    if *index == gold && *value == field_from_u64(COUNTING_ROOM_TOLL)
            )),
            "the door is FieldGte(gold, {COUNTING_ROOM_TOLL}); got {door:?}"
        );

        // QUANTITY decrements: drinking and lighting each take exactly one off the stack.
        let drink = case_constraints(&story, &choice_method(ROOM_OSSUARY, BAZ_DRINK));
        assert!(
            drink.contains(&exact_delta(potions, -1)),
            "a drink decrements the held potion count by EXACTLY one; got {drink:?}"
        );
        assert!(
            drink.contains(&exact_delta(hp, POTION_HEAL as i64)),
            "a drink heals EXACTLY {POTION_HEAL} (no ghost-heal); got {drink:?}"
        );
        let light = case_constraints(&story, &choice_method(ROOM_OSSUARY, BAZ_LIGHT_TORCH));
        assert!(
            light.contains(&exact_delta(torches, -1)),
            "lighting decrements the held torch count by EXACTLY one; got {light:?}"
        );

        // The HP floor still bites (the compiler's FieldGte(hp, 1) on the blow).
        let blow = case_constraints(&story, &choice_method(ROOM_OSSUARY, BAZ_TRADE_BLOW));
        assert!(
            blow.iter().any(|c| matches!(
                c,
                StateConstraint::FieldGte { index, value }
                    if *index == hp && *value == field_from_u64(1)
            )),
            "the warden's blow is FieldGte(hp, 1); got {blow:?}"
        );
    }

    /// BUY WITH ENOUGH GOLD — DRIVEN. The purchase COMMITS as a real `TurnReceipt`:
    /// the purse falls by exactly the price, the potion lands, the merchant's tally
    /// bumps. And spending your LAST coin (gold == price) commits exactly.
    #[test]
    fn buy_with_enough_gold_commits_gold_down_item_up() {
        let s = bazaar_scene();
        let world = seeded(50, OPENING_PURSE);
        let buy = choice_at(&s, ROOM_BAZAAR, BAZ_BUY_POTION);

        let r = world
            .apply_choice(ROOM_BAZAAR, BAZ_BUY_POTION, &buy)
            .expect("a purchase you can afford commits");
        assert_eq!(
            world.read_var("gold"),
            OPENING_PURSE - POTION_PRICE,
            "the purse fell by exactly the posted price"
        );
        assert_eq!(world.read_var("potions"), 1, "the potion landed");
        assert_eq!(world.read_var("potions_bought"), 1, "the tally bumped");
        assert_ne!(r.turn_hash, [0u8; 32], "a genuine committed turn");

        // The BOUNDARY: a purse of exactly the price buys exactly once, to zero.
        let broke = seeded(51, POTION_PRICE);
        broke
            .apply_choice(ROOM_BAZAAR, BAZ_BUY_POTION, &buy)
            .expect("spending your last coin commits (new == 0 == old − price)");
        assert_eq!(broke.read_var("gold"), 0, "the purse is empty");
        assert_eq!(broke.read_var("potions"), 1, "and the potion landed");

        // ...and the NEXT purchase, now broke, is refused (see the refusal test).
        assert!(matches!(
            broke.apply_choice(ROOM_BAZAAR, BAZ_BUY_POTION, &buy),
            Err(WorldError::Refused(_))
        ));
    }

    /// BUY WITH TOO LITTLE GOLD — DRIVEN. The REAL executor REFUSES the purchase (the
    /// clamped underflow is not `old − price`, so the exact-payment `FieldDelta` fails)
    /// and NOTHING commits: no potion, no gold movement, no tally bump (anti-ghost).
    /// This is the tooth the vacuous `FieldGte(gold, 0)` lift would have missed.
    #[test]
    fn buy_with_insufficient_gold_refused_no_item_gold_unchanged() {
        let s = bazaar_scene();
        let world = seeded(52, 30); // 30 gold; a potion costs 50.
        let buy = choice_at(&s, ROOM_BAZAAR, BAZ_BUY_POTION);

        let reason = why(world.apply_choice(ROOM_BAZAAR, BAZ_BUY_POTION, &buy));
        assert!(
            reason.contains(&delta_violation(slot_of("gold"))),
            "the purchase is refused by the EXACT-PAYMENT tooth on gold (the clamped \
             underflow is not `old − price`); got: {reason}"
        );
        assert_eq!(
            world.read_var("gold"),
            30,
            "anti-ghost: the purse is intact"
        );
        assert_eq!(world.read_var("potions"), 0, "anti-ghost: no potion landed");
        assert_eq!(
            world.read_var("potions_bought"),
            0,
            "anti-ghost: the merchant's tally did not move"
        );

        // The goods NEVER arrive without payment: a FORGED raw turn that takes the
        // potion while underpaying (or not paying at all) fails the same tooth.
        let cell = world.cell_id();
        let story = bazaar_compiled();
        let gold = keep_slot(&story, "gold");
        let potions = keep_slot(&story, "potions");
        let shoplift = why(world.apply_raw(
            &choice_method(ROOM_BAZAAR, BAZ_BUY_POTION),
            vec![raw_set(cell, gold, 30), raw_set(cell, potions, 1)],
        ));
        assert!(
            shoplift.contains(&delta_violation(gold)),
            "taking the potion without paying is refused by the exact-payment tooth; \
             got: {shoplift}"
        );
        assert_eq!(
            world.read_var("potions"),
            0,
            "anti-ghost: nothing shoplifted"
        );
    }

    /// SELL REQUIRES HOLDING — DRIVEN. Selling an amulet you do not hold is a REAL
    /// executor refusal (the exact `−1` decrement cannot land from zero) and mints no
    /// gold. After robbing the niche the SAME move commits: the amulet leaves, the gold
    /// arrives — and a second sale is refused again (you sold the only one you had).
    #[test]
    fn sell_requires_holding_the_item() {
        let s = bazaar_scene();
        let world = seeded(53, 0);
        let sell = choice_at(&s, ROOM_BAZAAR, BAZ_SELL_AMULET);
        let rob = choice_at(&s, ROOM_OSSUARY, BAZ_ROB_NICHE);

        // Sell with nothing held: refused, and no gold is minted.
        let reason = why(world.apply_choice(ROOM_BAZAAR, BAZ_SELL_AMULET, &sell));
        assert!(
            reason.contains(&delta_violation(slot_of("amulet"))),
            "selling an item you do not hold is refused by the `−1` decrement tooth on \
             the amulet (it cannot land from zero); got: {reason}"
        );
        assert_eq!(world.read_var("gold"), 0, "anti-ghost: no gold was minted");
        assert_eq!(
            world.read_var("amulet"),
            0,
            "anti-ghost: no amulet appeared"
        );

        // Rob the niche, then the same sale commits: item out, gold in.
        world
            .apply_choice(ROOM_OSSUARY, BAZ_ROB_NICHE, &rob)
            .expect("robbing the niche commits");
        assert_eq!(world.read_var("amulet"), 1, "the amulet is held");

        let r = world
            .apply_choice(ROOM_BAZAAR, BAZ_SELL_AMULET, &sell)
            .expect("selling an amulet you HOLD commits");
        assert_eq!(world.read_var("amulet"), 0, "the amulet left the pack");
        assert_eq!(
            world.read_var("gold"),
            AMULET_PRICE,
            "the merchant paid the posted price"
        );
        assert_ne!(r.turn_hash, [0u8; 32]);

        // A second sale of the one amulet you had: refused (nothing left to give).
        let again = world.apply_choice(ROOM_BAZAAR, BAZ_SELL_AMULET, &sell);
        assert!(
            matches!(again, Err(WorldError::Refused(_))),
            "selling the amulet twice is refused, got {again:?}"
        );
        assert_eq!(
            world.read_var("gold"),
            AMULET_PRICE,
            "anti-ghost: the double sale minted nothing"
        );

        // And the niche is not a money press: robbing it a SECOND time is refused
        // (FieldLte(niches_robbed, 1)) — so the amulet cannot be farmed for gold.
        let reprise = world.apply_choice(ROOM_OSSUARY, BAZ_ROB_NICHE, &rob);
        assert!(
            matches!(reprise, Err(WorldError::Refused(_))),
            "the niche holds exactly one amulet; a second robbery is refused, got {reprise:?}"
        );
        assert_eq!(world.read_var("amulet"), 0, "anti-ghost: no second amulet");
    }

    /// A FORGED SALE cannot mint gold: a raw turn dispatching the sell method while
    /// writing an inflated purse fails the exact-price `FieldDelta`. The price schedule
    /// is the kernel's, not the client's.
    #[test]
    fn forged_sale_cannot_mint_gold() {
        let s = bazaar_scene();
        let world = seeded(54, 0);
        let cell = world.cell_id();
        let story = bazaar_compiled();
        let gold = keep_slot(&story, "gold");
        let amulet = keep_slot(&story, "amulet");

        world
            .apply_choice(
                ROOM_OSSUARY,
                BAZ_ROB_NICHE,
                &choice_at(&s, ROOM_OSSUARY, BAZ_ROB_NICHE),
            )
            .expect("rob the niche");

        // The honest sale would write gold = 120. Forge 9_999 instead.
        let minted = why(world.apply_raw(
            &choice_method(ROOM_BAZAAR, BAZ_SELL_AMULET),
            vec![raw_set(cell, amulet, 0), raw_set(cell, gold, 9_999)],
        ));
        assert!(
            minted.contains(&delta_violation(gold)),
            "a forged over-payment is refused by the exact-price tooth on gold; got: {minted}"
        );
        assert_eq!(world.read_var("gold"), 0, "anti-ghost: no gold was minted");
        assert_eq!(
            world.read_var("amulet"),
            1,
            "anti-ghost: the amulet is still held"
        );
    }

    /// QUANTITIES — DRIVEN. One purchase delivers a STACK of three torches; each use
    /// decrements the held count by exactly one on a real committed turn (3 → 2 → 1 → 0);
    /// and the FOURTH use — the stack now empty — is a REAL executor refusal.
    #[test]
    fn quantity_decrements_on_use_and_hits_zero() {
        let s = bazaar_scene();
        let world = seeded(55, TORCH_BUNDLE_PRICE);
        let buy = choice_at(&s, ROOM_BAZAAR, BAZ_BUY_TORCHES);
        let light = choice_at(&s, ROOM_OSSUARY, BAZ_LIGHT_TORCH);

        // A use BEFORE the purchase: nothing held ⇒ refused.
        let empty = world.apply_choice(ROOM_OSSUARY, BAZ_LIGHT_TORCH, &light);
        assert!(
            matches!(empty, Err(WorldError::Refused(_))),
            "lighting a torch you do not hold is refused, got {empty:?}"
        );
        assert_eq!(
            world.read_var("wards_lit"),
            0,
            "anti-ghost: no ward was lit"
        );

        // Buy the bundle: one turn, a QUANTITY of three lands.
        world
            .apply_choice(ROOM_BAZAAR, BAZ_BUY_TORCHES, &buy)
            .expect("the bundle purchase commits");
        assert_eq!(
            world.read_var("torches"),
            TORCH_BUNDLE,
            "three torches held"
        );
        assert_eq!(world.read_var("gold"), 0, "paid exactly for the bundle");

        // Spend the stack: 3 → 2 → 1 → 0, each a real committed turn.
        for expect_left in (0..TORCH_BUNDLE).rev() {
            let r = world
                .apply_choice(ROOM_OSSUARY, BAZ_LIGHT_TORCH, &light)
                .expect("lighting a held torch commits");
            assert_ne!(r.turn_hash, [0u8; 32]);
            assert_eq!(
                world.read_var("torches"),
                expect_left,
                "the held count decremented by exactly one"
            );
        }
        assert_eq!(world.read_var("torches"), 0, "the stack is spent");
        assert_eq!(world.read_var("wards_lit"), TORCH_BUNDLE, "three wards lit");

        // The stack is EMPTY: the next use is a real executor refusal (anti-ghost).
        let spent = why(world.apply_choice(ROOM_OSSUARY, BAZ_LIGHT_TORCH, &light));
        assert!(
            spent.contains(&delta_violation(slot_of("torches"))),
            "using a spent stack is refused by the `−1` decrement tooth on the held count \
             (it cannot go below zero); got: {spent}"
        );
        assert_eq!(
            world.read_var("wards_lit"),
            TORCH_BUNDLE,
            "anti-ghost: no fourth ward was lit"
        );
    }

    /// The MERCHANT'S STOCK — DRIVEN. Two potions exist to be sold. With gold in hand
    /// the first two purchases commit; the THIRD is a REAL executor refusal (`FieldLte`
    /// on the purchase tally) even though the purse can afford it — and a forged
    /// "restock" (rewinding the tally in a raw turn) is refused by the `Monotonic`
    /// ratchet.
    #[test]
    fn merchant_stock_caps_purchases_and_a_forged_restock_is_refused() {
        let s = bazaar_scene();
        let world = seeded(56, 500); // plenty of gold — stock, not money, is the bound.
        let buy = choice_at(&s, ROOM_BAZAAR, BAZ_BUY_POTION);

        for n in 1..=POTION_STOCK {
            world
                .apply_choice(ROOM_BAZAAR, BAZ_BUY_POTION, &buy)
                .unwrap_or_else(|e| panic!("purchase {n} (within stock) commits: {e}"));
        }
        assert_eq!(world.read_var("potions_bought"), POTION_STOCK);
        assert_eq!(world.read_var("potions"), POTION_STOCK);

        // The stock is exhausted: the next purchase is refused, gold in hand or not —
        // and it is the STOCK CAP that bites (the purse could afford it).
        let gold_before = world.read_var("gold");
        let sold_out = why(world.apply_choice(ROOM_BAZAAR, BAZ_BUY_POTION, &buy));
        assert!(
            sold_out.contains(&format!("field[{}] > maximum", slot_of("potions_bought"))),
            "buying past the merchant's stock is refused by the FieldLte stock cap on the \
             purchase tally (not by the purse); got: {sold_out}"
        );
        assert_eq!(
            world.read_var("gold"),
            gold_before,
            "anti-ghost: nothing paid"
        );
        assert_eq!(
            world.read_var("potions"),
            POTION_STOCK,
            "anti-ghost: no potion beyond the stock"
        );

        // A FORGED restock — a raw buy-turn that pays honestly but rewinds the tally to
        // 0 to slip under the cap — is refused by the Monotonic ratchet.
        let cell = world.cell_id();
        let story = bazaar_compiled();
        let gold = keep_slot(&story, "gold");
        let potions = keep_slot(&story, "potions");
        let bought = keep_slot(&story, "potions_bought");
        let restock = why(world.apply_raw(
            &choice_method(ROOM_BAZAAR, BAZ_BUY_POTION),
            vec![
                raw_set(cell, gold, gold_before - POTION_PRICE),
                raw_set(cell, potions, POTION_STOCK + 1),
                raw_set(cell, bought, 0),
            ],
        ));
        assert!(
            restock.contains(&format!("field[{bought}] decreased")),
            "a forged restock (rewinding the merchant's tally) is refused by the Monotonic \
             ratchet; got: {restock}"
        );
        assert_eq!(
            world.read_var("potions_bought"),
            POTION_STOCK,
            "anti-ghost: the merchant's tally is intact"
        );
    }

    /// The SOLVENCY gate — DRIVEN. The counting-room door demands you can SHOW 100 gold
    /// (a real compiler-emitted `FieldGte(gold, 100)`, non-vacuous because the move does
    /// not touch gold). Broke, you are refused at the door; after selling the amulet the
    /// same move commits and carries you through.
    #[test]
    fn counting_room_door_is_a_real_solvency_gate() {
        let s = bazaar_scene();
        let world = seeded(57, 40); // 40 gold; the door wants 100.
        let door = choice_at(&s, ROOM_BAZAAR, BAZ_COUNTING_ROOM);

        let counting_room = *bazaar_compiled()
            .passage_index
            .get(ROOM_COUNTING_ROOM)
            .expect("the counting room is a passage");

        let refused = world.apply_choice(ROOM_BAZAAR, BAZ_COUNTING_ROOM, &door);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a pauper is refused at the counting-room door, got {refused:?}"
        );
        assert_ne!(
            world.read_passage(),
            Some(counting_room),
            "anti-ghost: the door did not open"
        );

        // Rob the niche, sell the amulet (40 + 120 = 160), and the door opens.
        world
            .apply_choice(
                ROOM_OSSUARY,
                BAZ_ROB_NICHE,
                &choice_at(&s, ROOM_OSSUARY, BAZ_ROB_NICHE),
            )
            .expect("rob the niche");
        world
            .apply_choice(
                ROOM_BAZAAR,
                BAZ_SELL_AMULET,
                &choice_at(&s, ROOM_BAZAAR, BAZ_SELL_AMULET),
            )
            .expect("sell the amulet");
        assert_eq!(world.read_var("gold"), 40 + AMULET_PRICE);

        world
            .apply_choice(ROOM_BAZAAR, BAZ_COUNTING_ROOM, &door)
            .expect("solvent, the door opens and the move commits");
        assert_eq!(
            world.read_passage(),
            Some(counting_room),
            "into the counting room"
        );
    }

    /// A FULL SHOPPING PLAYTHROUGH over the stock runtime — buy, spend the goods, rob,
    /// sell, pay in, seize — commits a real receipt chain through every economy tooth
    /// and RE-VERIFIES by replay against a fresh, identically-seeded, identically-
    /// augmented Bazaar.
    #[test]
    fn full_bazaar_playthrough_reverifies() {
        let s = bazaar_scene();
        let mut driver = Driver::start(deploy_bazaar(58), &s).expect("start the bazaar");

        // The purse opens at 120 (a genesis entry effect on the coast road).
        assert_eq!(driver.world().read_var("gold"), OPENING_PURSE);

        driver.advance(BAZ_ENTER).expect("under the awnings");
        driver.advance(BAZ_BUY_POTION).expect("buy a potion"); // gold 120→70, potions 1
        driver.advance(BAZ_BUY_TORCHES).expect("buy torches"); // gold 70→40, torches 3
        driver.advance(BAZ_TO_OSSUARY).expect("down to the ossuary");
        driver.advance(BAZ_ROB_NICHE).expect("rob the niche"); // amulet 1
        driver.advance(BAZ_TRADE_BLOW).expect("trade a blow"); // hp 40→25 (FieldGte)
        driver.advance(BAZ_DRINK).expect("drink the potion"); // potions 1→0, hp 25→50
        driver.advance(BAZ_LIGHT_TORCH).expect("light a torch"); // torches 3→2
        driver.advance(BAZ_CLIMB_BACK).expect("back to the bazaar");
        driver.advance(BAZ_SELL_AMULET).expect("sell the amulet"); // gold 40→160, amulet 0
        driver
            .advance(BAZ_COUNTING_ROOM)
            .expect("pay into the counting room"); // gold ≥ 100
        driver.advance(BAZ_SEIZE).expect("seize the takings"); // gold 160→660

        assert!(driver.is_ended(), "the bazaar is cleared");
        let w = driver.world();
        assert_eq!(
            w.read_var("gold"),
            OPENING_PURSE - POTION_PRICE - TORCH_BUNDLE_PRICE
                + AMULET_PRICE
                + COUNTING_ROOM_TAKINGS,
            "the purse balances: 120 − 50 − 30 + 120 + 500"
        );
        assert_eq!(w.read_var("potions"), 0, "the potion was drunk");
        assert_eq!(w.read_var("potions_bought"), 1, "one potion off the stock");
        assert_eq!(w.read_var("torches"), TORCH_BUNDLE - 1, "one torch burned");
        assert_eq!(w.read_var("amulet"), 0, "the amulet was sold");
        assert_eq!(w.read_var("niches_robbed"), 1);
        assert_eq!(w.read_var("wards_lit"), 1);
        assert_eq!(w.read_var("hp"), 40 - 15 + POTION_HEAL, "blow then potion");

        let play = driver.playthrough();
        assert_eq!(play.receipts().len(), 13, "genesis + 12 moves");
        verify_chain_linkage(&play).expect("the bazaar receipt chain links");
        verify(deploy_bazaar(58), &s, &play).expect("the honest shopping playthrough re-verifies");
    }

    /// A RETCONNED shopping record FAILS replay: forge the history so the amulet is SOLD
    /// before it was ever robbed. The real executor REFUSES the phantom sale on replay
    /// (or the reproduced state/passage order diverges first) — a forged economy cannot
    /// pass verification.
    #[test]
    fn retconned_shopping_record_fails_replay() {
        let s = bazaar_scene();
        let mut driver = Driver::start(deploy_bazaar(59), &s).expect("start the bazaar");
        driver.advance(BAZ_ENTER).expect("under the awnings");
        driver.advance(BAZ_TO_OSSUARY).expect("down to the ossuary");
        driver.advance(BAZ_ROB_NICHE).expect("rob the niche");
        driver.advance(BAZ_CLIMB_BACK).expect("back to the bazaar");
        driver.advance(BAZ_SELL_AMULET).expect("sell the amulet");
        driver
            .advance(BAZ_COUNTING_ROOM)
            .expect("pay in (gold 240)");
        driver.advance(BAZ_SEIZE).expect("seize the takings");

        let play = driver.playthrough();
        verify(deploy_bazaar(59), &s, &play).expect("the honest record re-verifies");

        // Forge step 2: don't rob the niche — trade a blow instead. The later sale is
        // now a sale of an amulet that was never held: REFUSED on replay.
        let mut forged = play.clone();
        forged.steps[2].choice_index = BAZ_TRADE_BLOW;
        let out = verify_by_replay(deploy_bazaar(59), &s, &forged);
        assert!(
            matches!(
                out,
                Err(VerifyBreak::RefusedOnReplay { .. })
                    | Err(VerifyBreak::PassageOutOfOrder { .. })
                    | Err(VerifyBreak::StateMismatch {
                        step: StepPos::Step(_)
                    })
            ),
            "a forged sale (of an unrobbed amulet) fails replay, got {out:?}"
        );
    }

    /// HONEST SCOPE, DRIVEN (not asserted): the Bazaar's gold is a COUNTER with an
    /// exact-delta kernel tooth, NOT a conserved [`Effect::Transfer`] of computrons.
    /// The substrate HAS the conserved move — and this test drives it to show exactly
    /// why it is out of reach here: the world-cell is born with **balance 0**, nothing
    /// in this crate's reach can fund it (`spween-dregg` seeds cell FIELDS, not
    /// balances), and `Effect::CreateCell` refuses a nonzero balance (no minting) — so
    /// the conserved move is REFUSED for insufficient balance. A conserved economy needs
    /// a funded merchant CELL (the multi-cell rung), not this single-cell universe.
    #[test]
    fn conserved_transfer_is_out_of_reach_gold_is_a_counter() {
        // A bazaar with ONE extra, deliberately unconstrained case, so that the ONLY
        // thing that can refuse the transfer is the KERNEL's balance arithmetic — not a
        // missing program case (unknown methods are default-denied).
        const PROBE: &str = "transfer_probe";
        let mut story = bazaar_compiled();
        add_case(&mut story.program, PROBE, vec![]);
        let world = WorldCell::deploy_compiled(Arc::new(story), 60).expect("the probe deploys");
        let cell = world.cell_id();

        // Birth a merchant cell (balance 0 — the kernel refuses any other), then try to
        // pay it 50 computrons out of the world-cell's purse.
        let merchant = CellId::derive_raw(&[0xBA; 32], &[0x2A; 32]);
        let out = world.apply_raw(
            PROBE,
            vec![
                Effect::CreateCell {
                    public_key: [0xBA; 32],
                    token_id: [0x2A; 32],
                    balance: 0,
                },
                Effect::Transfer {
                    from: cell,
                    to: merchant,
                    amount: 50,
                },
            ],
        );
        let WorldError::Refused(why) = out.expect_err("the conserved transfer cannot commit")
        else {
            panic!("expected a real executor refusal");
        };
        assert!(
            why.to_lowercase().contains("insufficient balance"),
            "the world-cell holds 0 computrons: the conserved move is refused for \
             insufficient balance (this is WHY gold is a counter here), got: {why}"
        );

        // Meanwhile the COUNTER economy is fully executor-refereed on the same cell.
        let s = bazaar_scene();
        let shop = seeded(61, OPENING_PURSE);
        shop.apply_choice(
            ROOM_BAZAAR,
            BAZ_BUY_POTION,
            &choice_at(&s, ROOM_BAZAAR, BAZ_BUY_POTION),
        )
        .expect("the counter economy's buy commits under its exact-payment tooth");
        assert_eq!(shop.read_var("gold"), OPENING_PURSE - POTION_PRICE);
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// A FIFTH UNIVERSE — "The Whispering Crypt": STEALTH / DETECTION, executor-refereed
// ═══════════════════════════════════════════════════════════════════════════════
//
// The Keep proved rules-as-teeth; the Vault, item pickup/use; the Hold, an unbounded
// heap inventory; the Bazaar, an economy with exact-delta quantities. The Crypt adds
// the mechanic they all lacked: **stealth** — an `alert` counter that noisy moves RAISE
// and a distraction move LOWERS, with the objective gated so you must reach the vault
// **without tripping the alarm**. Every rule below is a real [`StateConstraint`] the
// verified [`EmbeddedExecutor`](dregg_app_framework::EmbeddedExecutor) re-checks on the
// turn's post-state — never app bookkeeping, identical enforcement to the four before it.
//
// ── THE MODEL — `alert` (a register slot), two thresholds, three tooth-shapes ──────
//
//   * NOISE (a guarded step) — the noisy move `~ alert += FORCE_NOISE` carries TWO
//     augmented teeth: an EXACT [`StateConstraint::FieldDelta`]`{alert, +FORCE_NOISE}`
//     (the noise it makes is the kernel's, un-forgeable to `+0`) AND a hard-ceiling
//     [`StateConstraint::FieldLte`]`{alert, ALERT_CAP}`. A force that would push `alert`
//     PAST the cap (`post > ALERT_CAP`) is a REAL `WorldError::Refused` — "one more sound
//     and the sentinels swarm." This is the guarded step the stealth puzzle turns on.
//   * HUSH (the distraction) — `~ alert -= HUSH` carries an EXACT
//     `FieldDelta{alert, −HUSH}`: it LOWERS `alert` by exactly `HUSH` on a real committed
//     turn (un-forgeable to a bigger drop; and with `alert < HUSH` the clamp-at-zero write
//     is not `old − HUSH` ⇒ refused: you cannot quiet an alarm that was never raised).
//     A hush re-enables a force the cap had refused, and re-opens the alert-gated door.
//   * THE OBJECTIVE DOOR — `{ alert <= SANCTUM_ALERT && cage_open >= 1 }` is a
//     compiler-emitted CONJUNCTION (the move touches neither var, so both thresholds
//     survive the net-delta lift NON-VACUOUSLY): a `FieldLte{alert, SANCTUM_ALERT}`
//     solvency-style gate on the alarm AND a `FieldGte{cage_open, 1}` requirement that
//     the reliquary cage was forced first. Slipping into the sanctum LOUD (`alert >
//     SANCTUM_ALERT`) is a REAL executor refusal — the alarm is the kernel's referee.
//
// THE PUZZLE. The only way in is through the reliquary cage, and forcing it is NOISY
// (`cage_open` needs a `force`, which raises `alert` past the door's `SANCTUM_ALERT`
// threshold). So the sound solution is FORCE (make the needed noise) → HUSH (quiet back
// down) → EASE the door open while silent — the "reach the vault without tripping the
// alarm" playthrough. Being greedy with noise trips the hard cap; the door stays shut
// until you have hushed back under the threshold.
//
// ── RE-ENTRY (the Bazaar's lesson, applied) ───────────────────────────────────────
//
// `alert` is NEVER seeded — an unset register slot reads 0, which is exactly the "silent"
// start, so there is no genesis entry effect to re-run. And the stealth room (`nave`)
// carries NO entry effects: the force/hush/creep moves all loop `-> nave`, and a re-entry
// re-runs a passage's entry effects (the behaviour the Bazaar lane found), so a room that
// SEEDED `alert` and looped to itself would CLEANSE the alarm every turn. The Crypt sidesteps
// this by construction: `alert` has no seed to re-run, and `nave` has nothing to cleanse.
//
// ── HONEST SCOPE — what this stealth model is, and what a FULLER one adds ──────────
//
// This is a single global `alert` scalar with an executor-refereed raise/lower/cap and an
// alert-gated objective — sound against forged noise, over-quieting, and a loud entry
// WITHIN this cell's serialized history. What a fuller stealth game adds is OUT OF SCOPE
// here (each a real, named next rung, not a hole):
//   * GUARD PATROLS / line-of-sight — a per-tick guard position + a "seen iff in the guard's
//     cone" rule is a temporal/geometric predicate over MANY slots, not a single scalar; it
//     wants the multi-cell substrate (a guard cell per patroller) the crate already names;
//   * PER-GUARD ALERT — one `alert` slot per sentinel (a suspicion vector) rather than one
//     global counter: reachable TODAY as N register slots (or N heap keys) each with its own
//     `FieldDelta`/`FieldLte` pair, but the v0 scene compiler has no per-guard syntax, so it
//     would be augmented raw-turn methods like the Hold's `hold_pickup`;
//   * a DECAYING alarm (alert bleeds down over time) — a per-turn `−1` ratchet needs a
//     turn-clock the scene layer does not expose; a `Monotonic`-style DOWN atom plus a clock
//     slot would express it. No core atom is added here; the Crypt is built entirely from
//     `FieldDelta` / `FieldLte` / `FieldGte` that already exist.

/// The fifth dungeon — "The Whispering Crypt" — in the spween DSL. Three rooms: the
/// `threshold` (the way in, never re-entered), the `nave` (the stealth room: force the
/// noisy cage, hush the alarm with a distraction, ease the alert-gated sanctum door), and
/// the `reliquary` (the whispering relic — the hoard). The stealth RULES lower to real
/// executor teeth (see [`crypt_compiled`]).
pub const CRYPT: &str = r#"---
id: whispering-crypt
title: The Whispering Crypt
weight: 1
---

=== threshold

A collapsed lychgate, moss-choked, breathing cold. Beyond it the nave of a drowned crypt
waits — and something in the dark is listening.

* [Slip through the broken lychgate]
  -> nave

=== nave

The nave. A barnacled reliquary cage stands over the sanctum door, and down the black
transept the wraith-sentinels drift, roused by every echo. Loud, and they swarm; the
sanctum will not open for a hand that woke the whole crypt.

* [Force the groaning reliquary cage]
  ~ alert += 2
  ~ cage_open = 1
  -> nave

* [Creep along the shadowed colonnade]
  -> nave

* [Cast a bone-shard down the black transept]
  ~ alert -= 2
  -> nave

* [Ease open the sanctum door] { alert <= 1 && cage_open >= 1 }
  -> reliquary

=== reliquary

The reliquary, hushed and blue. On a bier of black glass the whispering relic waits.

* [Lift the whispering relic]
  ~ gold += 800
  -> END
"#;

// ── Crypt room / choice coordinates + the stealth thresholds ─────────────────────

/// The way in (never re-entered): no entry effect, so nothing re-seeds `alert`.
pub const ROOM_THRESHOLD: &str = "threshold";
/// The stealth room: force the cage, hush the alarm, ease the alert-gated sanctum door.
pub const ROOM_NAVE: &str = "nave";
/// The reliquary (terminal): the whispering relic.
pub const ROOM_RELIQUARY: &str = "reliquary";

/// `threshold`: slip inside into the nave (ungated).
pub const CRYPT_ENTER: usize = 0;
/// `nave`: FORCE the reliquary cage — a NOISY move (`alert += FORCE_NOISE`, `cage_open = 1`),
/// gated so a force that would push `alert` past [`ALERT_CAP`] is refused.
pub const NAVE_FORCE: usize = 0;
/// `nave`: creep the colonnade — a purely QUIET move (touches nothing; `alert` unchanged).
pub const NAVE_CREEP: usize = 1;
/// `nave`: cast a bone-shard — the DISTRACTION (`alert -= HUSH`), lowering the alarm.
pub const NAVE_HUSH: usize = 2;
/// `nave`: ease the sanctum door — refused unless `alert <= SANCTUM_ALERT` AND the cage
/// was forced (`cage_open >= 1`). The objective gate.
pub const NAVE_OPEN: usize = 3;
/// `reliquary`: lift the whispering relic (ends the crypt).
pub const CRYPT_SEIZE: usize = 0;

/// How much noise one forced cage makes (`alert += FORCE_NOISE`).
pub const FORCE_NOISE: u64 = 2;
/// How much a distraction quiets the alarm (`alert -= HUSH`).
pub const HUSH: u64 = 2;
/// The HARD CEILING on the alarm: a force that would push `alert` above this is refused
/// ("one more sound and the sentinels swarm") — a real `FieldLte{alert, ALERT_CAP}` tooth.
pub const ALERT_CAP: u64 = 4;
/// The sanctum door threshold: it opens only while `alert <= SANCTUM_ALERT` — a real
/// compiler-emitted `FieldLte{alert, SANCTUM_ALERT}` gate (the move does not touch `alert`,
/// so the threshold survives non-vacuously).
pub const SANCTUM_ALERT: u64 = 1;
/// The whispering relic's hoard, seized in the reliquary.
pub const CRYPT_HOARD: u64 = 800;

/// Parse the Whispering Crypt scene.
pub fn crypt_scene() -> Scene {
    parse(CRYPT, "whispering-crypt.scene").expect("the crypt scene parses")
}

/// **Compile the Crypt AND augment its program with the stealth teeth.** The objective
/// door's alert-and-cage gate (`FieldLte{alert, SANCTUM_ALERT}` + `FieldGte{cage_open, 1}`)
/// is compiler-emitted from the scene condition; this adds the shapes the v0 compiler does
/// not emit — the exact-noise + hard-cap teeth on the force, and the exact-quiet tooth on
/// the distraction — as real `CellProgram` cases the executor re-checks move-for-move.
pub fn crypt_compiled() -> CompiledStory {
    let mut story = compile_scene(&crypt_scene()).expect("the crypt compiles");

    let alert = keep_slot(&story, "alert");

    // FORCE — the guarded NOISY step: it makes EXACTLY `FORCE_NOISE` of noise
    // (`FieldDelta{alert, +FORCE_NOISE}`, un-forgeable to silence) AND is capped
    // (`FieldLte{alert, ALERT_CAP}`), so a force that would push the alarm past the ceiling
    // is a REAL executor refusal.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_NAVE, NAVE_FORCE),
        vec![
            exact_delta(alert, FORCE_NOISE as i64),
            StateConstraint::FieldLte {
                index: alert,
                value: field_from_u64(ALERT_CAP),
            },
        ],
    );

    // HUSH — the distraction lowers the alarm by EXACTLY `HUSH` (`FieldDelta{alert, −HUSH}`,
    // un-forgeable to a bigger drop; and quieting an unraised alarm — `alert < HUSH` — is
    // refused because the clamp-at-zero write is not `old − HUSH`).
    augment_case(
        &mut story.program,
        &choice_method(ROOM_NAVE, NAVE_HUSH),
        vec![exact_delta(alert, -(HUSH as i64))],
    );

    story
}

/// Deploy the augmented Crypt as a real world-cell (the stealth teeth installed as executor
/// predicates). Deterministic in `seed` (a re-deploy reproduces the same cell identity +
/// state hashes — what the replay verifier leans on).
pub fn deploy_crypt(seed: u8) -> WorldCell {
    WorldCell::deploy_compiled(Arc::new(crypt_compiled()), seed).expect("the crypt deploys")
}

#[cfg(test)]
mod crypt_tests {
    //! The stealth mechanic, DRIVEN on the real `WorldCell`: a quiet playthrough reaches
    //! the reliquary; a noisy move that would trip the alarm ceiling is a REAL executor
    //! refusal that commits NOTHING (anti-ghost); a distraction lowers the alarm and the
    //! previously-refused step then commits; the alert-gated sanctum door refuses a loud
    //! entry and opens once hushed. Plus a full playthrough that re-verifies by replay and
    //! a retcon (dropping the distraction) that fails.
    use super::*;
    use spween_dregg::{
        Driver, StepPos, VerifyBreak, WorldError, verify, verify_by_replay, verify_chain_linkage,
    };

    /// The reliquary's passage index (the direct tests assert the door did / did not open).
    fn reliquary_index() -> usize {
        *crypt_compiled()
            .passage_index
            .get(ROOM_RELIQUARY)
            .expect("the reliquary is a passage")
    }

    /// Every stealth rule is a REAL kernel predicate: introspect the installed program and
    /// read back the exact-noise + hard-cap teeth on the force, the exact-quiet tooth on the
    /// distraction, and the alert-and-cage conjunction on the fully-gated objective door.
    #[test]
    fn crypt_stealth_teeth_are_real_kernel_predicates() {
        let story = crypt_compiled();
        let alert = keep_slot(&story, "alert");
        let cage = keep_slot(&story, "cage_open");

        // FORCE: exact noise (FieldDelta +FORCE_NOISE) AND the hard cap (FieldLte ALERT_CAP).
        let force = case_constraints(&story, &choice_method(ROOM_NAVE, NAVE_FORCE));
        assert!(
            force.contains(&exact_delta(alert, FORCE_NOISE as i64)),
            "a force raises alert by EXACTLY {FORCE_NOISE} (FieldDelta); got {force:?}"
        );
        assert!(
            force.iter().any(|c| matches!(
                c,
                StateConstraint::FieldLte { index, value }
                    if *index == alert && *value == field_from_u64(ALERT_CAP)
            )),
            "a force is capped at ALERT_CAP={ALERT_CAP} (FieldLte on alert); got {force:?}"
        );

        // HUSH: the distraction lowers alert by EXACTLY HUSH (FieldDelta −HUSH).
        let hush = case_constraints(&story, &choice_method(ROOM_NAVE, NAVE_HUSH));
        assert!(
            hush.contains(&exact_delta(alert, -(HUSH as i64))),
            "a distraction lowers alert by EXACTLY {HUSH} (FieldDelta); got {hush:?}"
        );

        // THE DOOR: fully executor-enforced, and its conjunction is FieldLte(alert, thr) +
        // FieldGte(cage_open, 1) — both non-vacuous (the move touches neither slot).
        let m_door = choice_method(ROOM_NAVE, NAVE_OPEN);
        assert_eq!(
            story.fully_gated.get(&m_door),
            Some(&true),
            "the sanctum door is fully executor-enforced"
        );
        let door = case_constraints(&story, &m_door);
        assert!(
            door.iter().any(|c| matches!(
                c,
                StateConstraint::FieldLte { index, value }
                    if *index == alert && *value == field_from_u64(SANCTUM_ALERT)
            )),
            "the door gates on alert <= SANCTUM_ALERT={SANCTUM_ALERT} (FieldLte); got {door:?}"
        );
        assert!(
            door.iter().any(|c| matches!(
                c,
                StateConstraint::FieldGte { index, value }
                    if *index == cage && *value == field_from_u64(1)
            )),
            "the door requires the cage forced (FieldGte(cage_open, 1)); got {door:?}"
        );
    }

    /// THE STEALTH PUZZLE, DRIVEN — a quiet playthrough reaches the reliquary. Force the
    /// noisy cage (the only way in), HUSH the alarm back under the door threshold, then ease
    /// the sanctum door open while silent and lift the relic. The alarm never trips.
    #[test]
    fn quiet_playthrough_reaches_the_reliquary() {
        let s = crypt_scene();
        let world = deploy_crypt(70);

        let force = choice_at(&s, ROOM_NAVE, NAVE_FORCE);
        let hush = choice_at(&s, ROOM_NAVE, NAVE_HUSH);
        let door = choice_at(&s, ROOM_NAVE, NAVE_OPEN);

        // Force the cage: noisy (alert 0→2), but it opens the cage the door needs.
        world
            .apply_choice(ROOM_NAVE, NAVE_FORCE, &force)
            .expect("forcing the cage (alert 0→2 ≤ cap) commits");
        assert_eq!(world.read_var("alert"), 2, "the force woke the crypt to 2");
        assert_eq!(world.read_var("cage_open"), 1, "the reliquary cage is open");

        // The door is LOUD-shut: alert 2 > SANCTUM_ALERT (1) ⇒ refused (see the door test).
        // Hush the alarm back down (alert 2→0) — now silent.
        world
            .apply_choice(ROOM_NAVE, NAVE_HUSH, &hush)
            .expect("the distraction quiets the alarm (alert 2→0)");
        assert_eq!(world.read_var("alert"), 0, "hushed back to silence");

        // Silent AND the cage open: the sanctum door eases open.
        world
            .apply_choice(ROOM_NAVE, NAVE_OPEN, &door)
            .expect("silent (alert 0 ≤ 1) with the cage open, the door commits");
        assert_eq!(
            world.read_passage(),
            Some(reliquary_index()),
            "slipped into the reliquary undetected"
        );

        // Lift the relic — the hoard is claimed.
        let seize = choice_at(&s, ROOM_RELIQUARY, CRYPT_SEIZE);
        world
            .apply_choice(ROOM_RELIQUARY, CRYPT_SEIZE, &seize)
            .expect("lifting the relic commits");
        assert_eq!(world.read_var("gold"), CRYPT_HOARD, "the relic is taken");
    }

    /// THE NOISY PATH, DRIVEN — a force that would push the alarm past the hard ceiling is a
    /// REAL executor refusal (`FieldLte{alert, ALERT_CAP}`), committing nothing; and the
    /// DISTRACTION then lowers the alarm and RE-ENABLES the very step the cap had refused.
    #[test]
    fn noisy_force_trips_the_cap_and_a_distraction_re_enables_it() {
        let s = crypt_scene();
        let world = deploy_crypt(71);

        let force = choice_at(&s, ROOM_NAVE, NAVE_FORCE);
        let hush = choice_at(&s, ROOM_NAVE, NAVE_HUSH);

        // Two forces raise the alarm to the ceiling (0→2→4), each a real committed turn.
        let r1 = world
            .apply_choice(ROOM_NAVE, NAVE_FORCE, &force)
            .expect("force 1 (alert 0→2) commits");
        assert_eq!(world.read_var("alert"), 2);
        let r2 = world
            .apply_choice(ROOM_NAVE, NAVE_FORCE, &force)
            .expect("force 2 (alert 2→4 == cap) commits");
        assert_eq!(world.read_var("alert"), 4, "the alarm is at the ceiling");
        assert_ne!(r1.turn_hash, [0u8; 32]);
        assert_eq!(
            r2.pre_state_hash, r1.post_state_hash,
            "the force receipts chain (pre == prev.post)"
        );

        // A THIRD force (4→6) would exceed ALERT_CAP=4: the guarded step is REFUSED.
        let refused = world.apply_choice(ROOM_NAVE, NAVE_FORCE, &force);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a force past the alarm ceiling is refused by the FieldLte cap, got {refused:?}"
        );
        assert_eq!(
            world.read_var("alert"),
            4,
            "anti-ghost: the refused force made no noise"
        );

        // The DISTRACTION lowers the alarm (4→2), re-enabling the capped step.
        world
            .apply_choice(ROOM_NAVE, NAVE_HUSH, &hush)
            .expect("the distraction quiets the alarm (alert 4→2)");
        assert_eq!(
            world.read_var("alert"),
            2,
            "the alarm is back under the ceiling"
        );

        // The previously-refused force now commits (2→4 ≤ cap): a real committed turn.
        let r3 = world
            .apply_choice(ROOM_NAVE, NAVE_FORCE, &force)
            .expect("with the alarm hushed, the force commits again");
        assert_eq!(world.read_var("alert"), 4);
        assert_ne!(r3.turn_hash, [0u8; 32]);
    }

    /// THE OBJECTIVE DOOR, DRIVEN — the sanctum door is refused LOUD (`alert >
    /// SANCTUM_ALERT`) and refused with the cage UNFORCED, and opens only when both clauses
    /// hold. The distraction is what carries the alarm back under the threshold.
    #[test]
    fn sanctum_door_gated_on_alert_and_cage() {
        let s = crypt_scene();
        let world = deploy_crypt(72);

        let force = choice_at(&s, ROOM_NAVE, NAVE_FORCE);
        let hush = choice_at(&s, ROOM_NAVE, NAVE_HUSH);
        let door = choice_at(&s, ROOM_NAVE, NAVE_OPEN);

        // Silent but the cage UNFORCED (cage_open 0): the FieldGte(cage_open, 1) clause bites.
        let no_cage = world.apply_choice(ROOM_NAVE, NAVE_OPEN, &door);
        assert!(
            matches!(no_cage, Err(WorldError::Refused(_))),
            "the door is refused with the cage unforced, got {no_cage:?}"
        );
        assert_ne!(
            world.read_passage(),
            Some(reliquary_index()),
            "anti-ghost: the door did not open"
        );

        // Force the cage — cage_open 1, but the noise (alert 0→2) now trips the door threshold.
        world
            .apply_choice(ROOM_NAVE, NAVE_FORCE, &force)
            .expect("force the cage");
        assert_eq!(world.read_var("cage_open"), 1);
        assert_eq!(world.read_var("alert"), 2);

        // LOUD (alert 2 > SANCTUM_ALERT 1): the FieldLte(alert, 1) clause refuses the entry.
        let loud = world.apply_choice(ROOM_NAVE, NAVE_OPEN, &door);
        assert!(
            matches!(loud, Err(WorldError::Refused(_))),
            "a loud entry (alert 2 > 1) is refused by the alert gate, got {loud:?}"
        );
        assert_ne!(
            world.read_passage(),
            Some(reliquary_index()),
            "anti-ghost: the alarm kept the sanctum shut"
        );

        // Hush the alarm (2→0), and NOW — silent, cage open — the door commits.
        world
            .apply_choice(ROOM_NAVE, NAVE_HUSH, &hush)
            .expect("quiet the alarm");
        assert_eq!(world.read_var("alert"), 0);
        world
            .apply_choice(ROOM_NAVE, NAVE_OPEN, &door)
            .expect("silent + cage open: the sanctum door opens");
        assert_eq!(
            world.read_passage(),
            Some(reliquary_index()),
            "into the reliquary"
        );
    }

    /// A full LEGAL stealth playthrough over the stock runtime — slip in, force the cage,
    /// hush the alarm, ease the door open, lift the relic — commits a real receipt chain
    /// through the stealth teeth and re-verifies by replay against a fresh, identically-
    /// seeded, identically-augmented Crypt.
    #[test]
    fn full_crypt_playthrough_reverifies() {
        let s = crypt_scene();
        let mut driver = Driver::start(deploy_crypt(73), &s).expect("start the crypt");

        driver.advance(CRYPT_ENTER).expect("slip inside"); // -> nave
        driver.advance(NAVE_FORCE).expect("force the cage"); // alert 0→2, cage_open 1 (FieldDelta + cap)
        driver.advance(NAVE_HUSH).expect("hush the alarm"); // alert 2→0 (FieldDelta)
        driver.advance(NAVE_OPEN).expect("ease the door"); // alert 0 ≤ 1 && cage_open ≥ 1
        driver.advance(CRYPT_SEIZE).expect("lift the relic");
        assert!(driver.is_ended(), "the crypt is cleared");
        assert_eq!(driver.world().read_var("gold"), CRYPT_HOARD);
        assert_eq!(driver.world().read_var("alert"), 0, "slipped out silent");
        assert_eq!(driver.world().read_var("cage_open"), 1);

        let play = driver.playthrough();
        assert_eq!(play.receipts().len(), 6, "genesis + 5 moves");
        verify_chain_linkage(&play).expect("the crypt receipt chain links");
        verify(deploy_crypt(73), &s, &play).expect("the honest stealth playthrough re-verifies");
    }

    /// A retconned stealth record FAILS replay: forge the history to DROP the distraction
    /// (creep instead of hush), leaving the alarm loud (alert 2) at the sanctum door. The
    /// real executor REFUSES the loud entry on replay (or the reproduced state/passage order
    /// diverges first) — a forged stealth run cannot pass verification.
    #[test]
    fn retconned_crypt_playthrough_fails() {
        let s = crypt_scene();
        let mut driver = Driver::start(deploy_crypt(74), &s).expect("start the crypt");
        driver.advance(CRYPT_ENTER).expect("slip inside");
        driver.advance(NAVE_FORCE).expect("force the cage");
        driver.advance(NAVE_HUSH).expect("hush the alarm");
        driver.advance(NAVE_OPEN).expect("ease the door");
        driver.advance(CRYPT_SEIZE).expect("lift the relic");

        let play = driver.playthrough();
        verify(deploy_crypt(74), &s, &play).expect("the honest record re-verifies");

        // Forge step 2: creep (a no-op quiet move) instead of hushing. The alarm stays at 2,
        // and the later door step (alert 2 > 1) is REFUSED on replay.
        let mut forged = play.clone();
        forged.steps[2].choice_index = NAVE_CREEP;
        let out = verify_by_replay(deploy_crypt(74), &s, &forged);
        assert!(
            matches!(
                out,
                Err(VerifyBreak::RefusedOnReplay { .. })
                    | Err(VerifyBreak::PassageOutOfOrder { .. })
                    | Err(VerifyBreak::StateMismatch {
                        step: StepPos::Step(_)
                    })
            ),
            "a retconned stealth run (alarm left loud at the door) fails replay, got {out:?}"
        );
    }
}
