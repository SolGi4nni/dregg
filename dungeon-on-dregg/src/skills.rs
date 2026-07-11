//! # `skills` — a d20 SKILL CHECK as a verifiable roll gated by an executor tooth
//!
//! A skill check in a tabletop RPG is `d20 + <ability modifier> vs a Difficulty
//! Class (DC)`. This module makes that a REAL dregg turn: the ability modifier is a
//! committed [`STAT_SLOT`] register of a character cell, the d20 is a real
//! [`dregg_dice::DrawStream`] draw bound into the real [`TurnReceipt`] (exactly the
//! receipt-binding [`crate::dice_combat`] uses for a combat blow), and **a
//! check-GATED action — a locked door that opens only on a passed check — is an
//! executor-enforced [`StateConstraint`], not app bookkeeping.**
//!
//! ## The check (stat + verifiable d20), recorded as the outcome
//!
//! A check resolves in the [`crate::dice_combat`] three-step shape:
//!
//! 1. **Derive the draw's context.** A [`RandomnessRequest`] binds the check's
//!    context — the character's committed `stat` (its `pre_state_root`), the action
//!    (the check method + die), the purpose (`event_kind = "skill/check"`), the
//!    sequence, `draw_count = 1`. Its [`EventId`](dregg_dice::EventId) seeds the
//!    draw; grinding the stat, action, or sequence moves the seed, hence the roll.
//! 2. **Roll the d20.** The verified [`Seed`](dregg_dice::draw::Seed) feeds a
//!    [`DrawStream`] whose [`draw_die`](DrawStream::draw_die)`(0, 20)` is the face
//!    (`1..=20`). The check TOTAL is `stat + roll` — a real committed field write to
//!    [`CHECK_TOTAL_SLOT`] (the recorded OUTCOME). Success is `total >= DC`,
//!    deterministic from `(stat + roll)` vs the DC.
//! 3. **Commit + bind.** The check commits as ONE real cap-bounded turn: it writes
//!    the total, advances the [`StrictMonotonic`](StateConstraint::StrictMonotonic)
//!    [`CHECKS_SLOT`] counter, and binds `[event_id ‖ transcript ‖ roll ‖ total]`
//!    into the SAME receipt via an [`Effect::EmitEvent`] under [`SKILL_TOPIC`] — so
//!    the roll rides the real receipt chain, not a parallel ledger.
//!
//! ## The check-GATE is an executor `StateConstraint`, not an `if`
//!
//! The locked door carries its own DC in a [`WriteOnce`](StateConstraint::WriteOnce)
//! [`DC_SLOT`], seeded at creation. Opening it is a real turn under
//! [`OPEN_DOOR_METHOD`] whose case carries
//! [`FieldLteField`](StateConstraint::FieldLteField)`{ DC_SLOT, CHECK_TOTAL_SLOT }`
//! — i.e. `DC <= last check total` ⟺ `total >= DC` ⟺ **the check passed**. A door
//! opened after a FAILED check (or before any check, when the total slot is 0) is a
//! REAL [`WorldError::Refused`](spween_dregg::WorldError) that commits nothing
//! (anti-ghost). The gate reads the recorded outcome; it is a kernel predicate.
//!
//! ## Reproduced on replay — a forged roll is caught
//!
//! [`reverify_check`] is the replay tooth: it re-derives the seed from the RECORDED
//! `(request, evidence)` through `dregg-dice`'s pure verifier, re-derives the d20,
//! recomputes `total = stat + roll`, and checks the roll AND total BOUND into the
//! receipt match. A forger who rewrites the bound roll/total to fake a passed check
//! is CAUGHT — the re-derived draw is the honest one and no longer matches. A
//! non-vacuous tamper tooth (the honest check passes the same tooth).
//!
//! ## Honest scope
//!
//! - **Reproducibility, not unpredictability** — the [`Deterministic`] source (as in
//!   [`crate::dice_combat`]): the draw is a pure function of the public context, so
//!   it reproduces on replay and offline, which is what the binding + replay tooth
//!   demonstrate. Wiring an unpredictable `dregg-dice` source is a named follow-up.
//! - **Single character cell**, one serial writer under one owner key. The DC lives
//!   in the same cell as the check total (the check-gate is intra-cell); a door whose
//!   DC must read a peer cell is the [`crate::multicell`] frontier.
//! - The `stat`/`DC` numbers are design params; the TEETH guarantee the invariants
//!   (a passed check is a real d20 over a committed stat; the gate admits only on a
//!   pass; a forged roll is caught).

use dregg_app_framework::{
    CellId, CellProgram, Effect, Event, FieldElement, StateConstraint, TransitionCase,
    TransitionGuard, TurnReceipt, field_from_u64, symbol,
};
use dregg_dice::source::Deterministic;
use dregg_dice::{
    DrawError, DrawStream, RandomnessEvidence, RandomnessRequest, RandomnessSource, VerifyError,
};
use spween_dregg::{CompiledStory, WorldCell, WorldError, field_to_u64};
use std::sync::Arc;

// ── The character cell's slot layout ─────────────────────────────────────────────

/// `stat` — the character's ability modifier (a committed register), added to the
/// d20 roll. [`WriteOnce`](StateConstraint::WriteOnce): set once at creation.
pub const STAT_SLOT: u8 = 1;
/// `check_total` — `stat + roll` of the LAST resolved check: the recorded OUTCOME the
/// check-gate reads.
pub const CHECK_TOTAL_SLOT: u8 = 2;
/// `door` — the locked door: `0` locked, `1` open. Globally
/// [`Monotonic`](StateConstraint::Monotonic) (once open, stays open).
pub const DOOR_SLOT: u8 = 3;
/// `checks` — a [`StrictMonotonic`](StateConstraint::StrictMonotonic) counter a check
/// advances (a real committed count of checks made).
pub const CHECKS_SLOT: u8 = 4;
/// `dc` — the locked door's Difficulty Class. [`WriteOnce`](StateConstraint::WriteOnce):
/// seeded at creation; the check-gate compares it against [`CHECK_TOTAL_SLOT`].
pub const DC_SLOT: u8 = 5;

/// The d20 a skill check rolls.
pub const SKILL_DIE_SIDES: u64 = 20;

/// The topic a skill check's draw binding is emitted under (distinct from any state
/// method and from the dice-combat topic).
pub const SKILL_TOPIC: &str = "dungeon-on-dregg/skill-check-commitment-v1";
/// The `dregg-dice` `event_kind` domain-separating skill-check draws.
pub const CHECK_EVENT_KIND: &str = "skill/check";
/// The committed game identity folded into every check request's `game_binding`.
const GAME_BINDING: &[u8] = b"dungeon-on-dregg/skills/d20-check/v1";

// ── Turn methods (driver + program agree) ────────────────────────────────────────

/// The method the creation turn presents (writes `stat` + `dc`, both `WriteOnce`).
pub const CREATE_ADVENTURER_METHOD: &str = "adventurer/create";
/// The method a skill-check turn presents (advances `checks`, binds the d20).
pub const CHECK_METHOD: &str = "skill/check";
/// The method the door-open turn presents (carries the check-gate `FieldLteField`).
pub const OPEN_DOOR_METHOD: &str = "door/open";

/// The scene id driving the character cell's deterministic identity.
pub const ADVENTURER_SCENE_ID: &str = "dungeon-on-dregg/skills-adventurer/v1";

// ── The character cell program ───────────────────────────────────────────────────

/// **Build the adventurer cell's [`CompiledStory`]** — slot layout + the
/// executor-enforced skill program (a real [`CellProgram::Cases`]).
///
/// Cases:
/// 1. **Global invariants** (`Always`): `stat` + `dc` [`WriteOnce`], `checks` +
///    `door` [`Monotonic`] (a check count never rewinds; an opened door stays open).
/// 2. **`adventurer/create`**: `FieldGte(stat, 1)` — a real adventurer has a stat.
/// 3. **`skill/check`**: `StrictMonotonic(checks)` — a check advances the counter.
/// 4. **`door/open`**: `FieldLteField(dc <= check_total)` — **THE CHECK-GATE** (the
///    door opens only when the last check total meets the DC) + `FieldEquals(door, 1)`.
pub fn adventurer_story() -> CompiledStory {
    let mut cases = Vec::new();

    // 1. Global invariants — ANDed onto every admitted turn.
    cases.push(TransitionCase {
        guard: TransitionGuard::Always,
        constraints: vec![
            StateConstraint::WriteOnce { index: STAT_SLOT },
            StateConstraint::WriteOnce { index: DC_SLOT },
            StateConstraint::Monotonic { index: CHECKS_SLOT },
            StateConstraint::Monotonic { index: DOOR_SLOT },
        ],
    });

    // 2. create — a real adventurer has at least a stat of 1.
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(CREATE_ADVENTURER_METHOD),
        },
        constraints: vec![StateConstraint::FieldGte {
            index: STAT_SLOT,
            value: field_from_u64(1),
        }],
    });

    // 3. skill/check — advances the real checks counter.
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(CHECK_METHOD),
        },
        constraints: vec![StateConstraint::StrictMonotonic { index: CHECKS_SLOT }],
    });

    // 4. door/open — THE CHECK-GATE: dc <= check_total (the check passed) + door lands open.
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(OPEN_DOOR_METHOD),
        },
        constraints: vec![
            StateConstraint::FieldLteField {
                left_index: DC_SLOT,
                right_index: CHECK_TOTAL_SLOT,
            },
            StateConstraint::FieldEquals {
                index: DOOR_SLOT,
                value: field_from_u64(1),
            },
        ],
    });

    CompiledStory {
        scene_id: ADVENTURER_SCENE_ID.to_string(),
        var_slots: [
            ("stat".to_string(), STAT_SLOT as usize),
            ("check_total".to_string(), CHECK_TOTAL_SLOT as usize),
            ("door".to_string(), DOOR_SLOT as usize),
            ("checks".to_string(), CHECKS_SLOT as usize),
            ("dc".to_string(), DC_SLOT as usize),
        ]
        .into_iter()
        .collect(),
        has_slots: Default::default(),
        passage_index: Default::default(),
        program: CellProgram::Cases(cases),
        fully_gated: Default::default(),
    }
}

/// **Deploy a fresh adventurer** as a real world-cell. Deterministic in `seed`.
pub fn deploy_adventurer(seed: u8) -> WorldCell {
    WorldCell::deploy_compiled(Arc::new(adventurer_story()), seed)
        .expect("the adventurer cell deploys")
}

// ── The turns ────────────────────────────────────────────────────────────────────

/// **Create the adventurer** — the one-time creation move writing `stat` and the
/// door's `dc` (both `WriteOnce`; a rival re-creation is refused). `stat >= 1`.
pub fn create_adventurer(world: &WorldCell, stat: u64, dc: u64) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    world.apply_raw(
        CREATE_ADVENTURER_METHOD,
        vec![
            Effect::SetField {
                cell,
                index: STAT_SLOT as usize,
                value: field_from_u64(stat),
            },
            Effect::SetField {
                cell,
                index: DC_SLOT as usize,
                value: field_from_u64(dc),
            },
        ],
    )
}

/// A resolved skill check: the request + evidence the d20 was derived from, the roll,
/// the committed `stat`, and the total (`stat + roll`, the recorded outcome).
#[derive(Clone, Debug)]
pub struct CheckDraw {
    /// The randomness request binding the check's context (its `EventId` seeds the d20).
    pub request: RandomnessRequest,
    /// The recorded evidence a verifier re-derives the seed from.
    pub evidence: RandomnessEvidence,
    /// The d20 face rolled (`1..=20`).
    pub roll: u64,
    /// The character's committed ability stat (folded into the request's pre-state root).
    pub stat: u64,
    /// The check total `stat + roll` — the recorded OUTCOME.
    pub total: u64,
}

/// A committed skill check: the real receipt plus the [`CheckDraw`] and the
/// commitments bound into its `EmitEvent`.
#[derive(Clone, Debug)]
pub struct CheckReceipt {
    /// The real committed turn receipt (binds the draw in `effects_hash`/`turn_hash`).
    pub receipt: TurnReceipt,
    /// The draw the check was resolved from.
    pub draw: CheckDraw,
    /// The committed `check_total` after the check.
    pub total_after: u64,
}

/// The fields bound into a check receipt's `EmitEvent`, read back off the receipt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundCheck {
    /// The draw's `EventId` bytes.
    pub event_id: FieldElement,
    /// The draw-transcript commitment.
    pub transcript: FieldElement,
    /// The d20 face bound into the turn.
    pub roll: u64,
    /// The total (`stat + roll`) bound into the turn.
    pub total: u64,
}

/// Whether a check passed against a DC (a pure decision over the recorded outcome).
pub fn check_succeeds(total: u64, dc: u64) -> bool {
    total >= dc
}

/// A deterministic (reproducible) draw context derived from the request's `EventId`.
fn check_context(req: &RandomnessRequest) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dungeon-on-dregg/skills/context/v1");
    h.update(req.event_id().as_bytes());
    *h.finalize().as_bytes()
}

/// The pre-state root a check draw binds: the character's committed ability stat (the
/// value the check is FOR). Grinding the stat moves the seed, hence the roll.
fn stat_root(stat: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dungeon-on-dregg/skills/pre-state/v1");
    h.update(&stat.to_le_bytes());
    *h.finalize().as_bytes()
}

/// A commitment to the finalized check action (the method + die).
fn action_hash(sides: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dungeon-on-dregg/skills/action/v1");
    h.update(CHECK_METHOD.as_bytes());
    h.update(&sides.to_le_bytes());
    *h.finalize().as_bytes()
}

/// Build the [`RandomnessRequest`] for a check at sequence `seq` over `stat`.
pub fn check_request(stat: u64, seq: u64) -> RandomnessRequest {
    RandomnessRequest {
        game_binding: GAME_BINDING.to_vec(),
        seq,
        pre_state_root: stat_root(stat),
        action_hash: action_hash(SKILL_DIE_SIDES),
        event_kind: CHECK_EVENT_KIND.to_string(),
        draw_count: 1,
    }
}

/// **Roll a skill check** — derive the request from the character's committed `stat`,
/// produce `dregg-dice` evidence + a verified seed, and read the d20 off the real
/// [`DrawStream`]. No world mutation yet — [`resolve_check`] commits it.
pub fn roll_check(world: &WorldCell, seq: u64) -> CheckDraw {
    let stat = world.read_var("stat");
    let request = check_request(stat, seq);
    let source = Deterministic {
        context: check_context(&request),
    };
    let evidence = source.evidence(&request);
    let seed =
        Deterministic::seed(&request, &evidence).expect("freshly-produced check evidence verifies");
    let roll = DrawStream::new(seed, request.draw_count)
        .draw_die(0, SKILL_DIE_SIDES)
        .expect("draw_count = 1, so index 0 is in range");
    CheckDraw {
        request,
        evidence,
        roll,
        stat,
        total: stat + roll,
    }
}

/// The `EmitEvent` binding a check draw into the turn: `[event_id ‖ transcript ‖ roll
/// ‖ total]` under [`SKILL_TOPIC`].
fn check_event_effect(cell: CellId, draw: &CheckDraw) -> Effect {
    let data = vec![
        *draw.request.event_id().as_bytes(),
        draw.evidence.draw_transcript_commitment,
        field_from_u64(draw.roll),
        field_from_u64(draw.total),
    ];
    Effect::EmitEvent {
        cell,
        event: Event::new(symbol(SKILL_TOPIC), data),
    }
}

/// **Commit a rolled check as ONE real cap-bounded turn.** Writes `check_total = stat
/// + roll` (the recorded outcome), advances the [`StrictMonotonic`] `checks` counter,
/// and binds the d20 into the SAME receipt via an `EmitEvent`.
pub fn resolve_check(world: &WorldCell, draw: &CheckDraw) -> Result<CheckReceipt, WorldError> {
    let cell = world.cell_id();
    let next_checks = world.read_var("checks") + 1;
    let effects = vec![
        Effect::SetField {
            cell,
            index: CHECK_TOTAL_SLOT as usize,
            value: field_from_u64(draw.total),
        },
        Effect::SetField {
            cell,
            index: CHECKS_SLOT as usize,
            value: field_from_u64(next_checks),
        },
        check_event_effect(cell, draw),
    ];
    let receipt = world.apply_raw(CHECK_METHOD, effects)?;
    Ok(CheckReceipt {
        receipt,
        draw: draw.clone(),
        total_after: world.read_var("check_total"),
    })
}

/// **Roll AND commit a check** in one call: [`roll_check`] then [`resolve_check`].
pub fn make_check(world: &WorldCell, seq: u64) -> Result<CheckReceipt, WorldError> {
    let draw = roll_check(world, seq);
    resolve_check(world, &draw)
}

/// **Open the locked door** — a real turn under [`OPEN_DOOR_METHOD`] writing `door =
/// 1`. The executor GATES it on `FieldLteField(dc <= check_total)`: the door opens
/// ONLY when the last check total met the DC (a passed check). A door-open after a
/// failed check (or before any check) is a real [`WorldError::Refused`] — nothing
/// commits.
pub fn open_door(world: &WorldCell) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    world.apply_raw(
        OPEN_DOOR_METHOD,
        vec![Effect::SetField {
            cell,
            index: DOOR_SLOT as usize,
            value: field_from_u64(1),
        }],
    )
}

/// Read the bound check draw off a committed receipt — the exact path a replayer uses.
pub fn bound_check(receipt: &TurnReceipt) -> Option<BoundCheck> {
    let topic = symbol(SKILL_TOPIC);
    let e = receipt.emitted_events.iter().find(|e| e.topic == topic)?;
    if e.data.len() < 4 {
        return None;
    }
    Some(BoundCheck {
        event_id: e.data[0],
        transcript: e.data[1],
        roll: field_to_u64(&e.data[2]),
        total: field_to_u64(&e.data[3]),
    })
}

/// Why re-verifying a bound check failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SkillReplayError {
    /// The receipt bound no check event under [`SKILL_TOPIC`].
    NoBinding,
    /// The recorded evidence did not verify against the recorded request.
    Evidence(VerifyError),
    /// Re-deriving the draw from the verified seed failed.
    Draw(DrawError),
    /// The bound `EventId` is not the recorded request's (the context was retconned).
    EventIdMismatch,
    /// The bound transcript commitment is not the recorded evidence's.
    TranscriptMismatch,
    /// The bound roll is not the one re-derived from the seed — a FORGED roll.
    RollMismatch {
        /// The roll bound into the receipt.
        bound: u64,
        /// The roll re-derived from the recorded request + evidence.
        rederived: u64,
    },
    /// The bound total is not `stat + roll` — a forged outcome (a faked passed check).
    TotalMismatch {
        /// The total bound into the receipt.
        bound: u64,
        /// The total the stat + re-derived roll fixes.
        expected: u64,
    },
}

impl std::fmt::Display for SkillReplayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SkillReplayError::NoBinding => write!(f, "the receipt bound no skill check"),
            SkillReplayError::Evidence(e) => write!(f, "the check evidence did not verify: {e:?}"),
            SkillReplayError::Draw(e) => write!(f, "re-deriving the draw failed: {e:?}"),
            SkillReplayError::EventIdMismatch => {
                write!(f, "the bound EventId is not the recorded request's")
            }
            SkillReplayError::TranscriptMismatch => {
                write!(f, "the bound transcript is not the recorded evidence's")
            }
            SkillReplayError::RollMismatch { bound, rederived } => write!(
                f,
                "forged roll: the receipt binds {bound} but the seed re-derives {rederived}"
            ),
            SkillReplayError::TotalMismatch { bound, expected } => write!(
                f,
                "forged outcome: the receipt binds total {bound} but stat + roll fixes {expected}"
            ),
        }
    }
}

impl std::error::Error for SkillReplayError {}

/// **The replay tooth — re-derive the d20 and catch a forgery.** Re-derive the seed
/// from the RECORDED `(request, evidence)`, re-derive the roll, recompute `total =
/// stat + roll`, and confirm the roll AND total BOUND into the receipt match.
/// Returns the re-derived roll on success. A rewritten roll or total — a faked passed
/// check — is a [`SkillReplayError`].
pub fn reverify_check(committed: &CheckReceipt) -> Result<u64, SkillReplayError> {
    let seed = Deterministic::seed(&committed.draw.request, &committed.draw.evidence)
        .map_err(SkillReplayError::Evidence)?;
    let rederived = DrawStream::new(seed, committed.draw.request.draw_count)
        .draw_die(0, SKILL_DIE_SIDES)
        .map_err(SkillReplayError::Draw)?;
    let bound = bound_check(&committed.receipt).ok_or(SkillReplayError::NoBinding)?;
    if bound.event_id != *committed.draw.request.event_id().as_bytes() {
        return Err(SkillReplayError::EventIdMismatch);
    }
    if bound.transcript != committed.draw.evidence.draw_transcript_commitment {
        return Err(SkillReplayError::TranscriptMismatch);
    }
    if bound.roll != rederived {
        return Err(SkillReplayError::RollMismatch {
            bound: bound.roll,
            rederived,
        });
    }
    let expected_total = committed.draw.stat + rederived;
    if bound.total != expected_total {
        return Err(SkillReplayError::TotalMismatch {
            bound: bound.total,
            expected: expected_total,
        });
    }
    Ok(rederived)
}

/// Introspect the executor-enforced constraints installed on a method's case (proof
/// each rule is a real kernel predicate — for the example to print the teeth).
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

    /// The check-gate lowers to a REAL `FieldLteField(dc <= check_total)` on the
    /// door-open case, and the check advances a real `StrictMonotonic` counter — the
    /// rules are kernel predicates keyed by the method, not app bookkeeping.
    #[test]
    fn the_check_gate_is_a_real_fieldltefield_tooth() {
        let story = adventurer_story();
        let door = case_constraints(&story, OPEN_DOOR_METHOD);
        assert!(
            door.iter().any(|c| matches!(
                c,
                StateConstraint::FieldLteField { left_index, right_index }
                    if *left_index == DC_SLOT && *right_index == CHECK_TOTAL_SLOT
            )),
            "door/open carries FieldLteField(dc <= check_total); got {door:?}"
        );
        let check = case_constraints(&story, CHECK_METHOD);
        assert!(
            check.iter().any(|c| matches!(
                c,
                StateConstraint::StrictMonotonic { index } if *index == CHECKS_SLOT
            )),
            "skill/check advances StrictMonotonic(checks); got {check:?}"
        );
    }

    /// A check ROLLS a real d20 (`1..=20`), records `total = stat + roll`, BINDS the
    /// roll into the receipt, and RE-VERIFIES: replay re-derives the same roll+total.
    #[test]
    fn a_check_rolls_binds_and_reverifies() {
        let world = deploy_adventurer(10);
        create_adventurer(&world, 3, 15).expect("creation commits");
        assert_eq!(world.read_var("stat"), 3);

        let committed = make_check(&world, 0).expect("a skill check commits");

        assert!(
            (1..=SKILL_DIE_SIDES).contains(&committed.draw.roll),
            "the roll is a real d20 face, got {}",
            committed.draw.roll
        );
        assert_eq!(
            committed.draw.total,
            3 + committed.draw.roll,
            "the total is stat + roll"
        );
        assert_eq!(
            world.read_var("check_total"),
            committed.draw.total,
            "the outcome is a real committed field write"
        );
        assert_eq!(world.read_var("checks"), 1, "the checks counter advanced");
        assert_ne!(
            committed.receipt.turn_hash, [0u8; 32],
            "a real committed turn"
        );

        let bound = bound_check(&committed.receipt).expect("the draw is bound");
        assert_eq!(bound.roll, committed.draw.roll);
        assert_eq!(bound.total, committed.draw.total);

        let rederived = reverify_check(&committed).expect("the honest check re-verifies");
        assert_eq!(rederived, committed.draw.roll, "replay re-derives the roll");
    }

    /// The draw is DETERMINISTIC in the context: two identically-created adventurers
    /// (same stat) roll the same first check.
    #[test]
    fn the_check_reproduces_across_identical_worlds() {
        let wa = deploy_adventurer(11);
        let wb = deploy_adventurer(11);
        create_adventurer(&wa, 4, 15).expect("A");
        create_adventurer(&wb, 4, 15).expect("B");
        let ra = make_check(&wa, 0).expect("A check");
        let rb = make_check(&wb, 0).expect("B check");
        assert_eq!(
            ra.draw.roll, rb.draw.roll,
            "identical context reproduces the identical roll"
        );
    }

    /// THE CHECK-GATE (both directions, non-vacuous): the SAME `door/open` move is
    /// REFUSED after a failed check and ADMITTED after a passed one — the only
    /// difference is the DC (one point either side of the identical roll's total).
    #[test]
    fn a_check_gated_door_is_refused_on_fail_admitted_on_success() {
        // Probe the roll (independent of DC — the request binds only the stat).
        let stat = 3;
        let probe = deploy_adventurer(12);
        create_adventurer(&probe, stat, 100).expect("probe");
        let roll = roll_check(&probe, 0).roll;
        let total = stat + roll;

        // FAIL world: DC one above the total — the check cannot meet it.
        let fail = deploy_adventurer(12);
        create_adventurer(&fail, stat, total + 1).expect("fail-world creation");
        make_check(&fail, 0).expect("the check commits (records the total)");
        assert_eq!(fail.read_var("check_total"), total);
        let refused = open_door(&fail);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a door-open after a FAILED check is refused by FieldLteField(dc<=total), got {refused:?}"
        );
        assert_eq!(
            fail.read_var("door"),
            0,
            "anti-ghost: the door stays locked"
        );

        // SUCCESS world: DC exactly the total — the check meets it.
        let pass = deploy_adventurer(12);
        create_adventurer(&pass, stat, total).expect("pass-world creation");
        make_check(&pass, 0).expect("the check commits");
        assert_eq!(pass.read_var("check_total"), total);
        open_door(&pass).expect("a door-open after a PASSED check commits");
        assert_eq!(
            pass.read_var("door"),
            1,
            "the door opened on the passed check"
        );
    }

    /// A door-open BEFORE any check is refused (check_total 0 < DC).
    #[test]
    fn a_door_open_before_any_check_is_refused() {
        let world = deploy_adventurer(13);
        create_adventurer(&world, 5, 12).expect("creation");
        let refused = open_door(&world);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "no check yet ⇒ check_total 0 < DC ⇒ refused, got {refused:?}"
        );
        assert_eq!(world.read_var("door"), 0, "anti-ghost: still locked");
    }

    /// THE FORGED-ROLL TOOTH (non-vacuous): forge a passed check by rewriting the
    /// bound roll+total to 20/23. Replay re-derives the TRUE roll from the recorded
    /// evidence and CATCHES the forgery. The honest check passes the same tooth.
    #[test]
    fn a_forged_check_is_caught_on_replay() {
        let world = deploy_adventurer(14);
        create_adventurer(&world, 3, 20).expect("creation");
        let honest = make_check(&world, 0).expect("an honest check commits");
        assert_eq!(
            reverify_check(&honest).expect("honest re-verifies"),
            honest.draw.roll
        );
        assert!(
            honest.draw.roll < 20,
            "seed 14 rolls below the forge ceiling"
        );

        // FORGE a natural-20 pass: rewrite the bound roll + total.
        let mut forged = honest.clone();
        let topic = symbol(SKILL_TOPIC);
        let event = forged
            .receipt
            .emitted_events
            .iter_mut()
            .find(|e| e.topic == topic)
            .expect("the check event to rewrite");
        event.data[2] = field_from_u64(20);
        event.data[3] = field_from_u64(23);
        forged.draw.roll = 20;
        forged.draw.total = 23;

        let out = reverify_check(&forged);
        assert_eq!(
            out,
            Err(SkillReplayError::RollMismatch {
                bound: 20,
                rederived: honest.draw.roll,
            }),
            "the forged roll is caught on replay, got {out:?}"
        );
    }

    /// A forged TOTAL alone (roll left honest, total inflated to fake a pass) is
    /// caught — the total must be exactly `stat + roll`.
    #[test]
    fn a_forged_total_is_caught_on_replay() {
        let world = deploy_adventurer(15);
        create_adventurer(&world, 2, 25).expect("creation");
        let honest = make_check(&world, 0).expect("honest check");

        let mut forged = honest.clone();
        let topic = symbol(SKILL_TOPIC);
        let event = forged
            .receipt
            .emitted_events
            .iter_mut()
            .find(|e| e.topic == topic)
            .expect("check event");
        event.data[3] = field_from_u64(25); // inflate the total; roll left honest.
        forged.draw.total = 25;

        let out = reverify_check(&forged);
        assert_eq!(
            out,
            Err(SkillReplayError::TotalMismatch {
                bound: 25,
                expected: 2 + honest.draw.roll,
            }),
            "a forged total is caught, got {out:?}"
        );
    }

    /// The stat is WriteOnce: a rival re-creation is a real executor refusal.
    #[test]
    fn the_stat_is_write_once() {
        let world = deploy_adventurer(16);
        create_adventurer(&world, 4, 15).expect("creation commits");
        let refused = create_adventurer(&world, 99, 1);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "re-creating the adventurer is refused (WriteOnce), got {refused:?}"
        );
        assert_eq!(
            world.read_var("stat"),
            4,
            "anti-ghost: the stat is unchanged"
        );
    }

    /// Check receipts CHAIN onto the real receipt chain: creation → check → check
    /// link `pre == prev.post` (one serial writer, one cell).
    #[test]
    fn check_receipts_chain() {
        let world = deploy_adventurer(17);
        let r0 = create_adventurer(&world, 3, 15).expect("creation");
        let c1 = make_check(&world, 0).expect("first check");
        let c2 = make_check(&world, 1).expect("second check");
        assert_eq!(c1.receipt.pre_state_hash, r0.post_state_hash, "chains");
        assert_eq!(
            c2.receipt.pre_state_hash, c1.receipt.post_state_hash,
            "the checks chain"
        );
    }
}
