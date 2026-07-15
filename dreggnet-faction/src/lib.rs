//! # `dreggnet-faction` — FACTIONS / REPUTATION as real gated cell state.
//!
//! The [`dungeon_on_dregg::dialogue`] slice proved a single NPC's DISPOSITION is real
//! committed cell state: rise-only warmth GATES friendly content ([`FieldGte`]), a
//! warmed NPC REFUSES a threat ([`FieldLte`]), a goad is a [`WriteOnce`]-permanent
//! memory that closes a topic forever. That module named the frontier precisely —
//! *"FACTION REPUTATION is the multi-cell disposition graph."* This crate builds it:
//! per-NPC disposition generalized to a **faction cell** whose owned slots are your
//! STANDING with each faction, and whose teeth are the same real
//! [`StateConstraint`](dregg_app_framework::StateConstraint)s the verified executor
//! re-checks on every turn.
//!
//! ## The FactionCell — standing as committed cell state (not a host tally)
//!
//! "The Feud at the Ashenmoor Gate": two rival factions hold the moor — the **Embers**
//! (a fire-cult that keeps the beacons) and the **Tide** (a drowned-coast clan). You
//! win their trust turn by turn, and the moor's content opens — or seals — on your
//! standing. Every slot is a real cell slot, every rule a real executor predicate:
//!
//! | slot              | what it remembers                    | tooth (executor-enforced [`StateConstraint`])                     |
//! |-------------------|--------------------------------------|-------------------------------------------------------------------|
//! | `rep_embers`      | your standing with the Embers        | [`Monotonic`] — rep can rise but is never un-earned                |
//! | `rep_tide`        | your standing with the Tide          | [`Monotonic`]                                                     |
//! | `embers_ceiling`  | how high the Embers will EVER trust you | drops as you pledge the Tide — the rival cap's headroom slot     |
//! | `tide_ceiling`    | how high the Tide will ever trust you | drops as you pledge the Embers                                    |
//! | `ember_quest`     | the Ember trial is unlocked          | [`WriteOnce`]; gated on [`FieldGte`]`(rep_embers, THRESHOLD)` + never-betrayed |
//! | `tide_region`     | the Tide's deeps are opened          | [`WriteOnce`]; gated on `FieldGte(rep_tide, THRESHOLD)` + never-betrayed |
//! | `embers_betrayed` | you turned on the Embers             | [`WriteOnce`]; once set, seals the Ember content forever          |
//! | `tide_betrayed`   | you turned on the Tide               | [`WriteOnce`]                                                     |
//!
//! ## The four teeth, each a real predicate, each driven NON-VACUOUSLY
//!
//! * **Reputation is [`Monotonic`] — it cannot be un-earned.** A pledge RAISES your
//!   standing (a real committed turn the Keeper's `disposition += 1` re-homes to a
//!   faction); an attempt to WRITE IT DOWN (`~ rep_embers = 0`) is a real
//!   [`WorldError::Refused`](spween_dregg::WorldError) that commits nothing — you can't
//!   fake losing (or, in a rival's telling, "forgiving") a standing you truly hold.
//! * **Content is GATED on standing.** The Ember trial unlocks only at
//!   `FieldGte(rep_embers, `[`REP_THRESHOLD`]`)` — below the threshold the SAME
//!   undertaking is refused (anti-ghost: the quest stays locked), at the threshold it
//!   commits; and the gated REGION (`ember_sanctum`) is reachable only once its unlock
//!   flag is set. You cannot enter content your standing has not earned.
//! * **A betrayal is a [`WriteOnce`]-permanent SEAL.** Turning on the Embers sets
//!   `embers_betrayed` (a `WriteOnce` the faction remembers forever) and the Ember
//!   content's gate carries `FieldEquals(embers_betrayed, 0)`: once you betray them, the
//!   trial is refused however high your standing later climbs, and the seal is
//!   UN-REOPENABLE (a recant — `~ embers_betrayed = 0` — is refused by `WriteOnce`).
//!   The exact tooth the goad uses to close the Lantern-Keeper's friendly topic.
//! * **FACTION-VS-FACTION is a real CROSS-SLOT cap.** Raising your standing with the
//!   Embers DROPS `tide_ceiling`, and the Tide pledge is gated `{ rep_tide <
//!   "$tide_ceiling" }` — the compiler's var-op-var lowering emits a real
//!   [`FieldLteOther`] cross-slot tooth (`new[rep_tide] <= new[tide_ceiling]`). So the
//!   two factions are RIVALS on the verified executor: pledge the Embers deep enough and
//!   the Tide will no longer have you — over-raising the Tide while the Embers are high
//!   is a real `Refused`, not a host courtesy.
//!
//! ## Honest scope + edge
//!
//! * Standing is committed cell state and every gate is executor-refereed: you cannot
//!   fake being trusted, and content gated on standing is a kernel predicate a stranger
//!   re-checks — not app bookkeeping (the LARP the rebuild kills). Each tooth is driven
//!   both ways (refused, then admitted, one committed turn the only difference) in
//!   [`mod tests`].
//! * This is ONE faction cell — one serial writer under one owner key (the same
//!   single-cell envelope [`dungeon_on_dregg::dialogue`] names). Rep persisted on the
//!   player's CHARACTER cell alongside echoes/boon (the progression sheet), faction-WAR
//!   world events (a beacon-seeded moor whose control shifts), and faction quests
//!   COMPOSING with `dreggnet-quest` are named seams over this real core, not gaps in it.
//! * The rival cap rides a HEADROOM slot (`tide_ceiling`) the pledge decrements: a
//!   direct atom cannot subtract one slot from another, so the "sum-capped allegiance"
//!   is carried as a maintained ceiling. The cross-slot `FieldLteOther` that reads it is
//!   the real tooth; a native cross-slot SUM bound is the noted sharpening.
//!
//! [`FieldGte`]: dregg_app_framework::StateConstraint::FieldGte
//! [`FieldLte`]: dregg_app_framework::StateConstraint::FieldLte
//! [`FieldEquals`]: dregg_app_framework::StateConstraint::FieldEquals
//! [`FieldLteOther`]: dregg_app_framework::StateConstraint::FieldLteOther
//! [`WriteOnce`]: dregg_app_framework::StateConstraint::WriteOnce
//! [`Monotonic`]: dregg_app_framework::StateConstraint::Monotonic
//! [`StateConstraint`]: dregg_app_framework::StateConstraint

use std::sync::Arc;

use dregg_app_framework::{CellProgram, StateConstraint, TransitionGuard, field_from_u64, symbol};
use spween::{Choice, PassageContent, Scene, Value};
use spween_dregg::{CompiledStory, WorldCell, choice_method, compile_scene, parse};

pub mod roster;
pub mod standing;
pub mod surface;

pub use roster::{FactionDef, FactionLines, Roster};
pub use standing::{FactionStanding, StandingSnapshot, StandingStore};

// ── The factions (the rival pair the whole feud turns on) ─────────────────────────

/// The fire-cult that keeps the moor's beacons — faction A.
pub const EMBERS: &str = "the Embers";
/// The drowned-coast clan — faction B, the Embers' rival.
pub const TIDE: &str = "the Tide";

/// The room the whole feud plays out in (a faction hall you return to each turn).
pub const ROOM_HALL: &str = "hall";
/// The Ember sanctum — a REGION reached only once the Ember trial is unlocked.
pub const ROOM_EMBER_SANCTUM: &str = "ember_sanctum";
/// The Tide deeps — a REGION reached only once the Tide rite is unlocked.
pub const ROOM_TIDE_DEEPS: &str = "tide_deeps";

/// The standing floor a faction's gated content requires (`rep >= 2`). Reached in two
/// pledges from the unaffiliated start (0).
pub const REP_THRESHOLD: u64 = 2;

/// The starting trust-ceiling a faction extends (`3`) — how high your standing with it
/// can climb before its RIVAL's pull caps it. Each pledge to the rival drops it by one.
pub const TRUST_CEILING: u64 = 3;

// ── The feud scene — the whole faction graph as one spween scene ──────────────────

/// **"The Feud at the Ashenmoor Gate" — the faction hall, in the spween narrative DSL.**
/// One room (`hall`) where every faction action is a self-looping choice (a real turn
/// that stays in the hall), plus the two gated REGIONS reached only once their unlock is
/// earned. The compiler lowers the gates it CAN — the standing thresholds
/// (`{ rep_embers >= 2 }`), the region entries (`{ ember_quest >= 1 }`), and — the
/// keystone — the cross-faction cap (`{ rep_tide < "$tide_ceiling" }`, the var-op-var
/// [`FieldLteOther`](dregg_app_framework::StateConstraint::FieldLteOther) lowering) — and
/// [`faction_compiled`] AUGMENTS the teeth the v0 compiler does not emit (the
/// `Monotonic` rep ratchet, the `WriteOnce` unlock/betrayal flags, the
/// `FieldEquals(betrayed, 0)` seal) — exactly the [`dungeon_on_dregg`] `vigil_compiled`
/// idiom.
pub const FEUD: &str = r#"---
id: ashenmoor-feud
title: The Feud at the Ashenmoor Gate
weight: 1
---

=== hall

~ embers_ceiling = 3
~ tide_ceiling = 3

Two banners hang over the Ashenmoor gate: the Embers' guttered flame and the Tide's
grey wave. Both wardens watch you, and neither loves the other.

* [Pledge your arm to the Embers] { rep_embers < "$embers_ceiling" }
  ~ rep_embers += 1
  ~ tide_ceiling -= 1
  -> hall

* [Pledge your arm to the Tide] { rep_tide < "$tide_ceiling" }
  ~ rep_tide += 1
  ~ embers_ceiling -= 1
  -> hall

* [Undertake the Ember trial] { rep_embers >= 2 }
  ~ ember_quest = 1
  -> hall

* [Undertake the Tide rite] { rep_tide >= 2 }
  ~ tide_region = 1
  -> hall

* [Betray the Embers]
  ~ embers_betrayed = 1
  -> hall

* [Betray the Tide]
  ~ tide_betrayed = 1
  -> hall

* [Renounce your Ember standing]
  ~ rep_embers = 0
  -> hall

* [Renounce your Tide standing]
  ~ rep_tide = 0
  -> hall

* [Recant the betrayal of the Embers]
  ~ embers_betrayed = 0
  -> hall

* [Enter the Ember sanctum] { ember_quest >= 1 }
  -> ember_sanctum

* [Enter the Tide deeps] { tide_region >= 1 }
  -> tide_deeps

=== ember_sanctum

The beacon-keepers part for you. Within the sanctum the eternal flame burns, and the
Embers name you kin.

* [Kneel at the eternal flame]
  -> END

=== tide_deeps

The grey wave draws back from a stair going down. The Tide's drowned hall opens to one
they trust.

* [Descend into the drowned hall]
  -> END
"#;

// ── Line coordinates (the driver + verifier speak in these) ───────────────────────

/// `hall`: pledge to the Embers — raises `rep_embers` (`Monotonic`) AND drops
/// `tide_ceiling` (the rival cap on the Tide). Gated `{ rep_embers < "$embers_ceiling" }`.
pub const LN_PLEDGE_EMBERS: usize = 0;
/// `hall`: pledge to the Tide — raises `rep_tide` AND drops `embers_ceiling`. Gated on
/// the cross-slot `FieldLteOther` (`{ rep_tide < "$tide_ceiling" }`).
pub const LN_PLEDGE_TIDE: usize = 1;
/// `hall`: undertake the Ember trial — the gated CONTENT. `FieldGte(rep_embers, 2)` AND
/// `FieldEquals(embers_betrayed, 0)`; unlocks `ember_quest` (`WriteOnce`).
pub const LN_EMBER_TRIAL: usize = 2;
/// `hall`: undertake the Tide rite — `FieldGte(rep_tide, 2)` + never-betrayed; unlocks
/// `tide_region` (`WriteOnce`).
pub const LN_TIDE_RITE: usize = 3;
/// `hall`: betray the Embers — sets `embers_betrayed` (`WriteOnce`), sealing the Ember
/// content forever.
pub const LN_BETRAY_EMBERS: usize = 4;
/// `hall`: betray the Tide — sets `tide_betrayed` (`WriteOnce`).
pub const LN_BETRAY_TIDE: usize = 5;
/// `hall`: renounce your Ember standing — an attempted WRITE-DOWN of `rep_embers`,
/// refused by `Monotonic` (rep is never un-earned).
pub const LN_RENOUNCE_EMBERS: usize = 6;
/// `hall`: renounce your Tide standing — refused by `Monotonic` on `rep_tide`.
pub const LN_RENOUNCE_TIDE: usize = 7;
/// `hall`: recant the betrayal of the Embers — an attempted un-set of `embers_betrayed`,
/// refused by `WriteOnce` (the betrayal is un-reopenable).
pub const LN_RECANT_EMBERS: usize = 8;
/// `hall`: enter the Ember sanctum — the gated REGION (`{ ember_quest >= 1 }`).
pub const LN_ENTER_SANCTUM: usize = 9;
/// `hall`: enter the Tide deeps — the gated REGION (`{ tide_region >= 1 }`).
pub const LN_ENTER_DEEPS: usize = 10;
/// `ember_sanctum`: kneel at the eternal flame (ends the run in the sanctum).
pub const SANCTUM_KNEEL: usize = 0;
/// `tide_deeps`: descend into the drowned hall.
pub const DEEPS_DESCEND: usize = 0;

/// Parse the feud scene.
pub fn feud_scene() -> Scene {
    parse(FEUD, "ashenmoor-feud.scene").expect("the feud scene parses")
}

// ── Compiling the faction teeth (dialogue's `vigil_compiled` idiom, re-homed) ─────

/// Look up a var's compiled cell slot (panics on an unnamed var — every var below is
/// named by an effect/condition in [`FEUD`], so it always resolves).
pub(crate) fn faction_slot(story: &CompiledStory, name: &str) -> u8 {
    (*story
        .var_slots
        .get(name)
        .unwrap_or_else(|| panic!("faction var `{name}` has a compiled slot"))) as u8
}

/// Append `extra` constraints onto the compiled method-guarded case for `method` (a
/// faction tooth the v0 compiler does not emit). Panics on a coordinate typo. Mirrors
/// [`dungeon_on_dregg`]'s `augment_case`; an augmented case is enforced identically to a
/// compiled one — the executor never distinguishes who authored a [`TransitionCase`].
pub(crate) fn augment_case(program: &mut CellProgram, method: &str, extra: Vec<StateConstraint>) {
    let m = symbol(method);
    let CellProgram::Cases(cases) = program else {
        panic!("feud program is Cases");
    };
    let case = cases
        .iter_mut()
        .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method: mm } if *mm == m))
        .unwrap_or_else(|| panic!("no compiled case for method `{method}`"));
    case.constraints.extend(extra);
}

/// **Compile the feud AND augment its program with the faction teeth.** The standing
/// thresholds (`FieldGte(rep, 2)`), the region-entry gates (`FieldGte(unlock, 1)`), and
/// the cross-faction cap (`FieldLteOther(rep_tide <= tide_ceiling)`) are already
/// compiler-emitted from the scene conditions; this adds the shapes the v0 compiler does
/// not express:
///
/// * `LN_PLEDGE_*` / `LN_RENOUNCE_*` — [`StateConstraint::Monotonic`] on the rep slot
///   (a pledge's raise passes; a renounce's write-down is refused — rep is never
///   un-earned);
/// * `LN_EMBER_TRIAL` / `LN_TIDE_RITE` — [`StateConstraint::FieldEquals`]`(betrayed, 0)`
///   (a betrayal permanently seals the content) + [`StateConstraint::WriteOnce`] on the
///   unlock flag;
/// * `LN_BETRAY_*` / `LN_RECANT_EMBERS` — [`StateConstraint::WriteOnce`] on the betrayal
///   flag (the betrayal is remembered forever and cannot be un-set).
///
/// The result is a [`CellProgram`] the real executor enforces line-for-line.
pub fn faction_compiled() -> CompiledStory {
    let mut story = compile_scene(&feud_scene()).expect("the feud compiles");

    let rep_embers = faction_slot(&story, "rep_embers");
    let rep_tide = faction_slot(&story, "rep_tide");
    let ember_quest = faction_slot(&story, "ember_quest");
    let tide_region = faction_slot(&story, "tide_region");
    let embers_betrayed = faction_slot(&story, "embers_betrayed");
    let tide_betrayed = faction_slot(&story, "tide_betrayed");

    let zero = field_from_u64(0);

    // The rep RATCHET — Monotonic on every case that writes a rep slot. A pledge's
    // `+= 1` trivially satisfies `new >= old`; a renounce's `= 0` write-down lands
    // `0 < old` and is REFUSED. Rep can rise but is never un-earned.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_HALL, LN_PLEDGE_EMBERS),
        vec![StateConstraint::Monotonic { index: rep_embers }],
    );
    augment_case(
        &mut story.program,
        &choice_method(ROOM_HALL, LN_PLEDGE_TIDE),
        vec![StateConstraint::Monotonic { index: rep_tide }],
    );
    augment_case(
        &mut story.program,
        &choice_method(ROOM_HALL, LN_RENOUNCE_EMBERS),
        vec![StateConstraint::Monotonic { index: rep_embers }],
    );
    augment_case(
        &mut story.program,
        &choice_method(ROOM_HALL, LN_RENOUNCE_TIDE),
        vec![StateConstraint::Monotonic { index: rep_tide }],
    );

    // The Ember trial — the compiled `FieldGte(rep_embers, 2)` already bars a low
    // standing; this adds `FieldEquals(embers_betrayed, 0)` (a betrayal permanently
    // closes the content) and `WriteOnce` on the unlock flag.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_HALL, LN_EMBER_TRIAL),
        vec![
            StateConstraint::FieldEquals {
                index: embers_betrayed,
                value: zero,
            },
            StateConstraint::WriteOnce { index: ember_quest },
        ],
    );
    augment_case(
        &mut story.program,
        &choice_method(ROOM_HALL, LN_TIDE_RITE),
        vec![
            StateConstraint::FieldEquals {
                index: tide_betrayed,
                value: zero,
            },
            StateConstraint::WriteOnce { index: tide_region },
        ],
    );

    // The betrayals — a WriteOnce seal, remembered forever and un-reopenable.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_HALL, LN_BETRAY_EMBERS),
        vec![StateConstraint::WriteOnce {
            index: embers_betrayed,
        }],
    );
    augment_case(
        &mut story.program,
        &choice_method(ROOM_HALL, LN_BETRAY_TIDE),
        vec![StateConstraint::WriteOnce {
            index: tide_betrayed,
        }],
    );
    // The recant tries to un-set the Ember betrayal — refused by the SAME WriteOnce.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_HALL, LN_RECANT_EMBERS),
        vec![StateConstraint::WriteOnce {
            index: embers_betrayed,
        }],
    );

    story
}

/// **Deploy the feud as a real world-cell** (the faction teeth installed as executor
/// predicates). Deterministic in `seed`. The two trust-ceilings are seeded to
/// [`TRUST_CEILING`] (a faction hall opens with its full trust available); everything
/// else starts at zero — you arrive at the moor unaffiliated.
pub fn deploy_feud(seed: u8) -> WorldCell {
    let mut world =
        WorldCell::deploy_compiled(Arc::new(faction_compiled()), seed).expect("the feud deploys");
    world.seed_var("embers_ceiling", Value::Int(TRUST_CEILING as i64));
    world.seed_var("tide_ceiling", Value::Int(TRUST_CEILING as i64));
    world
}

// ── Introspection (proof each faction rule is a real kernel predicate) ────────────

/// The executor-enforced constraints installed on the case guarded by `method`. Mirrors
/// [`dungeon_on_dregg`]'s `case_constraints`.
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

/// The dispatch method for line `index` in the `hall` (the coordinate a driven line
/// presents). A thin re-export of [`choice_method`] pinned to the faction hall.
pub fn hall_method(index: usize) -> String {
    choice_method(ROOM_HALL, index)
}

/// Pull a specific `Choice` out of a parsed scene — the exact value
/// [`WorldCell::apply_choice`](spween_dregg::WorldCell::apply_choice) drives directly at
/// the executor (bypassing the client-side runtime so the executor gate is the sole
/// referee).
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

#[cfg(test)]
mod tests {
    use super::*;
    use spween_dregg::WorldError;

    fn line(scene: &Scene, room: &str, index: usize) -> Choice {
        choice_at(scene, room, index)
    }

    /// Drive a hall line, expecting it to COMMIT. Panics with the refusal on failure.
    fn commit(world: &WorldCell, s: &Scene, index: usize) {
        world
            .apply_choice(ROOM_HALL, index, &line(s, ROOM_HALL, index))
            .unwrap_or_else(|e| panic!("hall line {index} should commit: {e}"));
    }

    /// The faction gates lower to REAL executor teeth — a kernel predicate per rule, not
    /// app bookkeeping. Reads the installed program back and asserts each tooth present.
    #[test]
    fn faction_gates_lower_to_real_teeth() {
        let story = faction_compiled();
        let rep_embers = faction_slot(&story, "rep_embers");
        let rep_tide = faction_slot(&story, "rep_tide");
        let tide_ceiling = faction_slot(&story, "tide_ceiling");
        let ember_quest = faction_slot(&story, "ember_quest");
        let embers_betrayed = faction_slot(&story, "embers_betrayed");

        // Rep is Monotonic on the pledge AND on the renounce (the ratchet is global).
        for ln in [LN_PLEDGE_EMBERS, LN_RENOUNCE_EMBERS] {
            let cs = case_constraints(&story, &hall_method(ln));
            assert!(
                cs.iter().any(|c| matches!(c,
                    StateConstraint::Monotonic { index } if *index == rep_embers)),
                "line {ln} carries Monotonic(rep_embers); got {cs:?}"
            );
        }

        // The Ember trial is gated on standing (FieldGte, compiler-emitted) AND on
        // never-betrayed (FieldEquals, augmented) AND unlocks WriteOnce content.
        let trial = case_constraints(&story, &hall_method(LN_EMBER_TRIAL));
        assert!(
            trial.iter().any(|c| matches!(c,
                StateConstraint::FieldGte { index, value }
                    if *index == rep_embers && *value == field_from_u64(REP_THRESHOLD))),
            "Ember trial gated FieldGte(rep_embers, {REP_THRESHOLD}); got {trial:?}"
        );
        assert!(
            trial.iter().any(|c| matches!(c,
                StateConstraint::FieldEquals { index, value }
                    if *index == embers_betrayed && *value == field_from_u64(0))),
            "Ember trial sealed by FieldEquals(embers_betrayed, 0); got {trial:?}"
        );
        assert!(
            trial.iter().any(|c| matches!(c,
                StateConstraint::WriteOnce { index } if *index == ember_quest)),
            "Ember trial unlock is WriteOnce(ember_quest); got {trial:?}"
        );

        // The betrayal is a WriteOnce seal.
        let betray = case_constraints(&story, &hall_method(LN_BETRAY_EMBERS));
        assert!(
            betray.iter().any(|c| matches!(c,
                StateConstraint::WriteOnce { index } if *index == embers_betrayed)),
            "betrayal is WriteOnce(embers_betrayed); got {betray:?}"
        );

        // THE KEYSTONE: faction-vs-faction is a real CROSS-SLOT FieldLteOther tooth —
        // the Tide pledge reads the tide_ceiling slot the Ember pledge drops.
        let tide_pledge = case_constraints(&story, &hall_method(LN_PLEDGE_TIDE));
        assert!(
            tide_pledge.iter().any(|c| matches!(c,
                StateConstraint::FieldLteOther { index, other, .. }
                    if *index == rep_tide && *other == tide_ceiling)),
            "Tide pledge gated by cross-slot FieldLteOther(rep_tide <= tide_ceiling); got {tide_pledge:?}"
        );
    }

    /// REPUTATION ACCRUES (Monotonic): a pledge is a real committed turn that RAISES your
    /// standing and the faction REMEMBERS it across turns; an attempt to WRITE IT DOWN is
    /// a real refusal that commits nothing. Non-vacuous: the SAME renounce is a harmless
    /// no-op at zero standing but REFUSED once standing is earned.
    #[test]
    fn reputation_is_monotonic_a_write_down_is_refused() {
        let s = feud_scene();
        let world = deploy_feud(10);
        assert_eq!(world.read_var("rep_embers"), 0, "you arrive unaffiliated");

        // A renounce at zero standing is a harmless no-op (0 -> 0, Monotonic holds).
        world
            .apply_choice(
                ROOM_HALL,
                LN_RENOUNCE_EMBERS,
                &line(&s, ROOM_HALL, LN_RENOUNCE_EMBERS),
            )
            .expect("renouncing a standing you don't hold is a no-op");

        // Two pledges — standing accrues and PERSISTS across turns (read off the ledger).
        commit(&world, &s, LN_PLEDGE_EMBERS);
        assert_eq!(
            world.read_var("rep_embers"),
            1,
            "the pledge raised your standing"
        );
        commit(&world, &s, LN_PLEDGE_EMBERS);
        assert_eq!(
            world.read_var("rep_embers"),
            2,
            "the standing persists + accrues"
        );

        // Now the SAME renounce is REFUSED — you cannot un-earn a standing you hold.
        let refused = world.apply_choice(
            ROOM_HALL,
            LN_RENOUNCE_EMBERS,
            &line(&s, ROOM_HALL, LN_RENOUNCE_EMBERS),
        );
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a Monotonic write-down of earned rep is refused, got {refused:?}"
        );
        assert_eq!(
            world.read_var("rep_embers"),
            2,
            "anti-ghost: the standing stands"
        );
    }

    /// CONTENT GATED ON STANDING: the Ember trial is REFUSED below the threshold (the
    /// quest stays locked — anti-ghost) and COMMITS at the threshold; the gated REGION
    /// (`ember_sanctum`) is reachable only once the unlock is earned. Non-vacuous — the
    /// SAME undertaking, refused then admitted, two pledges the only difference.
    #[test]
    fn content_gated_on_standing_unlocks_at_the_threshold() {
        let s = feud_scene();
        let world = deploy_feud(11);

        // Below the threshold (rep_embers 0 < 2): the trial is refused, quest locked.
        let refused = world.apply_choice(
            ROOM_HALL,
            LN_EMBER_TRIAL,
            &line(&s, ROOM_HALL, LN_EMBER_TRIAL),
        );
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "the Ember trial is refused below the standing threshold, got {refused:?}"
        );
        assert_eq!(
            world.read_var("ember_quest"),
            0,
            "anti-ghost: quest still locked"
        );

        // The gated region is likewise sealed while the unlock is unset.
        let no_region = world.apply_choice(
            ROOM_HALL,
            LN_ENTER_SANCTUM,
            &line(&s, ROOM_HALL, LN_ENTER_SANCTUM),
        );
        assert!(
            matches!(no_region, Err(WorldError::Refused(_))),
            "the Ember sanctum is unreachable before the trial is unlocked, got {no_region:?}"
        );

        // Earn the standing (two pledges), then the SAME trial commits.
        commit(&world, &s, LN_PLEDGE_EMBERS);
        commit(&world, &s, LN_PLEDGE_EMBERS);
        assert_eq!(world.read_var("rep_embers"), 2);
        commit(&world, &s, LN_EMBER_TRIAL);
        assert_eq!(
            world.read_var("ember_quest"),
            1,
            "the trial is now unlocked"
        );

        // And the gated region now opens — a real turn moving into `ember_sanctum`.
        commit(&world, &s, LN_ENTER_SANCTUM);
        assert_eq!(
            world.read_passage(),
            Some(*world.story().passage_index.get(ROOM_EMBER_SANCTUM).unwrap()),
            "the Ember sanctum region is now entered"
        );
    }

    /// A BETRAYAL PERMANENTLY SEALS a faction's content (WriteOnce): after you betray the
    /// Embers, the trial is refused HOWEVER high your standing later climbs, and the seal
    /// is UN-REOPENABLE (a recant is refused by WriteOnce). Non-vacuous — the SAME trial
    /// would commit at this standing were the faction not betrayed.
    #[test]
    fn a_betrayal_permanently_seals_the_faction_content() {
        let s = feud_scene();
        let world = deploy_feud(12);

        // Earn the standing that WOULD unlock the trial, then betray the Embers.
        commit(&world, &s, LN_PLEDGE_EMBERS);
        commit(&world, &s, LN_PLEDGE_EMBERS);
        assert_eq!(
            world.read_var("rep_embers"),
            2,
            "standing over the threshold"
        );
        commit(&world, &s, LN_BETRAY_EMBERS);
        assert_eq!(
            world.read_var("embers_betrayed"),
            1,
            "the betrayal is remembered"
        );

        // The trial is now REFUSED despite the qualifying standing — the seal bites.
        let sealed = world.apply_choice(
            ROOM_HALL,
            LN_EMBER_TRIAL,
            &line(&s, ROOM_HALL, LN_EMBER_TRIAL),
        );
        assert!(
            matches!(sealed, Err(WorldError::Refused(_))),
            "a betrayed faction's content is sealed even at qualifying standing, got {sealed:?}"
        );
        assert_eq!(world.read_var("ember_quest"), 0, "anti-ghost: still sealed");

        // Raising standing higher does NOT reopen it — the seal is permanent.
        commit(&world, &s, LN_PLEDGE_EMBERS); // rep_embers 2 -> 3
        let still_sealed = world.apply_choice(
            ROOM_HALL,
            LN_EMBER_TRIAL,
            &line(&s, ROOM_HALL, LN_EMBER_TRIAL),
        );
        assert!(
            matches!(still_sealed, Err(WorldError::Refused(_))),
            "no amount of standing reopens a betrayed faction, got {still_sealed:?}"
        );

        // And the betrayal cannot be UN-DONE — a recant is refused by WriteOnce.
        let recant = world.apply_choice(
            ROOM_HALL,
            LN_RECANT_EMBERS,
            &line(&s, ROOM_HALL, LN_RECANT_EMBERS),
        );
        assert!(
            matches!(recant, Err(WorldError::Refused(_))),
            "the betrayal is un-reopenable (WriteOnce), got {recant:?}"
        );
        assert_eq!(world.read_var("embers_betrayed"), 1, "the betrayal stands");
    }

    /// FACTION-VS-FACTION CAP (the cross-slot tooth bites): raising your standing with the
    /// Embers DROPS `tide_ceiling`, so over-raising the Tide while the Embers are high is
    /// REFUSED. Non-vacuous — the SAME Tide pledge commits on a fresh moor and is refused
    /// once the Embers are pledged deep, the dropped ceiling the only difference.
    #[test]
    fn faction_vs_faction_raising_one_caps_the_rival() {
        let s = feud_scene();

        // Baseline: on a fresh moor the Tide pledge commits (tide_ceiling at full trust).
        let fresh = deploy_feud(13);
        commit(&fresh, &s, LN_PLEDGE_TIDE);
        assert_eq!(
            fresh.read_var("rep_tide"),
            1,
            "the Tide has you on a fresh moor"
        );

        // Now pledge the Embers to the hilt — each pledge drops tide_ceiling by one.
        let world = deploy_feud(14);
        for _ in 0..TRUST_CEILING {
            commit(&world, &s, LN_PLEDGE_EMBERS);
        }
        assert_eq!(
            world.read_var("rep_embers"),
            TRUST_CEILING,
            "you are an Ember to the hilt"
        );
        assert_eq!(
            world.read_var("tide_ceiling"),
            0,
            "the Tide's trust in you has been capped to nothing by your Ember pledges"
        );

        // The SAME Tide pledge is now REFUSED — the cross-slot FieldLteOther bites
        // (new[rep_tide]=1 <= new[tide_ceiling]=0 is false).
        let capped = world.apply_choice(
            ROOM_HALL,
            LN_PLEDGE_TIDE,
            &line(&s, ROOM_HALL, LN_PLEDGE_TIDE),
        );
        assert!(
            matches!(capped, Err(WorldError::Refused(_))),
            "over-raising the rival Tide while the Embers are high is refused, got {capped:?}"
        );
        assert_eq!(
            world.read_var("rep_tide"),
            0,
            "anti-ghost: the rival faction will not have you"
        );
    }
}
