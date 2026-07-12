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
