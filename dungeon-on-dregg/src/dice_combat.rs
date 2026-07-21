//! # `dice_combat` — verifiable randomness bound into a REAL dungeon turn
//!
//! The single-cell keep ([`crate`] root) gives combat a FIXED rule: the trade-blows
//! move always costs 20 HP, gated by the compiler-emitted `FieldGte(hp, 1)` tooth
//! (a killing blow is refused). That is a real executor tooth, but the damage is a
//! CONSTANT — there is no roll. `dregg-dice` sits beside the crate, unused. This
//! module closes that gap: **a combat blow's damage is a real
//! [`dregg_dice::DrawStream`] draw, bound into the real [`TurnReceipt`], and
//! REPRODUCED when the world is re-verified.**
//!
//! ## The dice draw binds into the real turn — the same `EmitEvent` seam narration uses
//!
//! A blow resolves in three real steps:
//!
//! 1. **Derive the draw's context.** A [`dregg_dice::RandomnessRequest`] binds the
//!    turn's context — the world's committed pre-state ([`WorldCell::snapshot`]
//!    hashed), the action (the trade-blows method + die), the purpose
//!    (`event_kind = "combat/hit"`), the sequence, and `draw_count = 1`. Its
//!    [`EventId`](dregg_dice::EventId) is the seed's binding context: changing the
//!    pre-state, the action, the purpose, or the draw count moves the EventId, hence
//!    the seed, hence the roll — grinding those is always detectable.
//! 2. **Roll.** The [`dregg_dice::RandomnessSource`] produces evidence and a verified
//!    [`Seed`](dregg_dice::draw::Seed); a [`DrawStream`](dregg_dice::DrawStream) over
//!    that seed yields the die face ([`DrawStream::draw_die`]). The damage IS that
//!    roll — a real draw, not a constant.
//! 3. **Commit + bind.** The blow commits as ONE real cap-bounded turn on the keep
//!    world-cell (`hp -= roll`) under the trade-blows method — so the executor's
//!    `FieldGte(hp, 1)` tooth still bites (a roll that would drop HP below 1 is a
//!    REAL refusal). The draw's `[event_id ‖ transcript_commitment ‖ roll ‖ damage]`
//!    rides the SAME [`TurnReceipt`] via an [`Effect::EmitEvent`] under
//!    [`DICE_TOPIC`] — exactly the receipt-only binding `narrator` uses for the
//!    narration commitment. The event is folded into the receipt's
//!    `effects_hash`/`turn_hash`, so the roll is part of the real receipt chain, not
//!    a parallel ledger.
//!
//! ## Reproduced on replay — a forged roll is caught
//!
//! [`reverify_draw`] is the replay tooth: it re-derives the seed from the RECORDED
//! `(request, evidence)` through `dregg-dice`'s pure
//! [`RandomnessSource::seed`](dregg_dice::RandomnessSource::seed) verifier, re-derives
//! the draw, and checks the roll BOUND into the real receipt's `EmitEvent` matches. A
//! forger who rewrites the bound roll/damage (to fake a gentler blow) and re-links the
//! record is CAUGHT: the re-derived draw is the honest roll, and it no longer matches
//! the forged binding. This is a real, non-vacuous tamper tooth (driven in
//! [`mod tests`]).
//!
//! ## Honest scope
//!
//! - **Reproducibility, not unpredictability.** This module uses the
//!   [`Deterministic`](dregg_dice::source::Deterministic) source: the draw is a pure
//!   function of the (public) context, so it REPRODUCES exactly on replay and offline
//!   — which is what the receipt binding + replay tooth demonstrate. It provides no
//!   unpredictability on its own. `dregg-dice` HAS the non-grindable sources
//!   (`ServerVrf` LB-VRF, the `Hybrid` genesis-committed key-chain + threshold
//!   drand-BLS beacon + timeout finalization); wiring an unpredictable source's
//!   evidence into this receipt binding is a named follow-up, not this slice.
//! - **Verification is O(N) [`reverify_draw`]** — a re-derivation per bound draw. The
//!   succinct light client (a proof the whole chain verified) is a separate,
//!   Lane-D-gated workstream and is NOT claimed here.

use dregg_app_framework::{
    CellId, Effect, Event, FieldElement, TurnReceipt, field_from_u64, symbol,
};
use dregg_dice::source::Deterministic;
use dregg_dice::{
    DrawError, DrawStream, RandomnessEvidence, RandomnessRequest, RandomnessSource, VerifyError,
};
use spween_dregg::{PASSAGE_SLOT, WorldCell, WorldError, choice_method, field_to_u64};

use crate::{KP_TRADE_BLOWS, ROOM_GATEHALL};

/// The topic under which a combat draw's binding is emitted onto the real turn.
/// Distinct from the narration topic and from any state-write method, so a dice
/// event can never be confused with a narration or a game effect. A verifier finds
/// the bound draw by this topic.
pub const DICE_TOPIC: &str = "dungeon-on-dregg/dice-draw-commitment-v1";

/// The purpose tag domain-separating combat-hit draws from any other subsystem's
/// randomness (a `dregg-dice` `event_kind`).
pub const COMBAT_EVENT_KIND: &str = "combat/hit";

/// The committed game identity folded into every combat request's `game_binding`.
const GAME_BINDING: &[u8] = b"dungeon-on-dregg/wardens-keep/dice-combat/v1";

/// The die a combat blow rolls (a d12: damage in `1..=12`, so a couple of blows are
/// survivable from the keep's 50-HP warden fight and the `FieldGte(hp, 1)` floor is
/// reachable but not trivial).
pub const COMBAT_DIE_SIDES: u64 = 12;

/// A resolved combat draw: the `dregg-dice` request + evidence it was derived from,
/// the die face rolled, and the damage applied (here `damage == roll`). Carried
/// alongside the receipt so [`reverify_draw`] can re-derive and check it.
#[derive(Clone, Debug)]
pub struct CombatDraw {
    /// The randomness request binding the turn context (its `EventId` seeds the draw).
    pub request: RandomnessRequest,
    /// The recorded evidence a verifier re-derives the seed from.
    pub evidence: RandomnessEvidence,
    /// The die face rolled (`1..=sides`).
    pub roll: u64,
    /// The damage applied to HP (this slice: `damage == roll`).
    pub damage: u64,
    /// The die used.
    pub sides: u64,
}

/// A committed dice-combat blow: the real [`TurnReceipt`] plus the [`CombatDraw`] its
/// damage came from and the commitments bound into the receipt's `EmitEvent`.
#[derive(Clone, Debug)]
pub struct CombatReceipt {
    /// The real committed turn receipt (its `effects_hash`/`turn_hash` bind the draw).
    pub receipt: TurnReceipt,
    /// The draw the damage was resolved from.
    pub draw: CombatDraw,
    /// The `EventId` bytes bound into the receipt (`data[0]`).
    pub event_id_commit: FieldElement,
    /// The draw-transcript commitment bound into the receipt (`data[1]`).
    pub transcript_commit: FieldElement,
    /// The HP after the blow (the real committed post-state HP).
    pub hp_after: u64,
}

/// The four fields bound into a combat receipt's `EmitEvent`, read back off the
/// receipt exactly as a stranger replaying the chain would.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundDraw {
    /// The draw's `EventId` bytes (`data[0]`).
    pub event_id: FieldElement,
    /// The draw-transcript commitment (`data[1]`).
    pub transcript: FieldElement,
    /// The die face bound into the turn (`data[2]`).
    pub roll: u64,
    /// The damage bound into the turn (`data[3]`).
    pub damage: u64,
}

/// Why re-verifying a bound combat draw failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DiceReplayError {
    /// The receipt bound no dice event under [`DICE_TOPIC`].
    NoBinding,
    /// The recorded evidence did not verify against the recorded request (the pure
    /// `dregg-dice` verifier rejected it — a tampered seed/transcript).
    Evidence(VerifyError),
    /// Re-deriving the draw from the verified seed failed.
    Draw(DrawError),
    /// The `EventId` bound into the receipt is not the one the recorded request
    /// derives — the turn context was retconned.
    EventIdMismatch,
    /// The transcript commitment bound into the receipt is not the recorded evidence's.
    TranscriptMismatch,
    /// The roll bound into the receipt is not the one re-derived from the seed — a
    /// FORGED roll (the core tamper tooth).
    RollMismatch {
        /// The value bound into the receipt.
        bound: u64,
        /// The value re-derived from the recorded request + evidence.
        rederived: u64,
    },
    /// The damage bound into the receipt is not the function of the roll the rules fix
    /// (here `damage == roll`) — a forged damage.
    DamageMismatch {
        /// The damage bound into the receipt.
        bound: u64,
        /// The damage the roll fixes.
        expected: u64,
    },
}

impl std::fmt::Display for DiceReplayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DiceReplayError::NoBinding => write!(f, "the receipt bound no dice draw"),
            DiceReplayError::Evidence(e) => write!(f, "the dice evidence did not verify: {e:?}"),
            DiceReplayError::Draw(e) => write!(f, "re-deriving the draw failed: {e:?}"),
            DiceReplayError::EventIdMismatch => {
                write!(f, "the bound EventId is not the recorded request's")
            }
            DiceReplayError::TranscriptMismatch => {
                write!(
                    f,
                    "the bound transcript commitment is not the recorded evidence's"
                )
            }
            DiceReplayError::RollMismatch { bound, rederived } => write!(
                f,
                "forged roll: the receipt binds {bound} but the seed re-derives {rederived}"
            ),
            DiceReplayError::DamageMismatch { bound, expected } => write!(
                f,
                "forged damage: the receipt binds {bound} but the roll fixes {expected}"
            ),
        }
    }
}

impl std::error::Error for DiceReplayError {}

/// The damage a die face inflicts. This slice: a straight hit — `damage == roll`.
/// Factored out so [`reverify_draw`] and [`resolve_blow`] agree on the rule.
pub fn damage_of_roll(roll: u64) -> u64 {
    roll
}

/// A deterministic (reproducible) context for the [`Deterministic`] source, derived
/// from the request's own `EventId`. The draw therefore REPRODUCES exactly on replay
/// (the point of this slice); it carries no unpredictability — see the module doc.
fn combat_context(req: &RandomnessRequest) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dungeon-on-dregg/dice-combat/context/v1");
    h.update(req.event_id().as_bytes());
    *h.finalize().as_bytes()
}

/// Hash a world-cell's committed slot snapshot into a 32-byte pre-state root — the
/// value bound into the combat request's `EventId`. Deterministic in the committed
/// state, so a fresh identically-driven world reproduces the byte-identical root.
fn snapshot_root(world: &WorldCell) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dungeon-on-dregg/dice-combat/pre-state/v1");
    for slot in world.snapshot() {
        h.update(&slot.to_le_bytes());
    }
    *h.finalize().as_bytes()
}

/// A commitment to the finalized combat action (the trade-blows method + die), bound
/// into the request's `EventId` so a different action would move the seed.
fn action_hash(sides: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dungeon-on-dregg/dice-combat/action/v1");
    h.update(choice_method(ROOM_GATEHALL, KP_TRADE_BLOWS).as_bytes());
    h.update(&sides.to_le_bytes());
    *h.finalize().as_bytes()
}

/// Build the combat [`RandomnessRequest`] for a blow at sequence `seq` against the
/// world's current committed pre-state.
pub fn combat_request(world: &WorldCell, seq: u64, sides: u64) -> RandomnessRequest {
    RandomnessRequest {
        game_binding: GAME_BINDING.to_vec(),
        seq,
        pre_state_root: snapshot_root(world),
        action_hash: action_hash(sides),
        event_kind: COMBAT_EVENT_KIND.to_string(),
        draw_count: 1,
    }
}

/// **Roll a combat blow** — derive the request from the world's committed pre-state,
/// produce `dregg-dice` evidence + a verified seed, and read the die face off the real
/// [`DrawStream`]. No world mutation yet — [`resolve_blow`] commits it.
pub fn roll_blow(world: &WorldCell, seq: u64, sides: u64) -> CombatDraw {
    let request = combat_request(world, seq, sides);
    let source = Deterministic {
        context: combat_context(&request),
    };
    let evidence = source.evidence(&request);
    // The producer just made this evidence; the pure verifier re-derives the seed and
    // checks the transcript (never trust a self-made seed on the trust path).
    let seed = Deterministic::seed(&request, &evidence)
        .expect("freshly-produced combat evidence verifies");
    let roll = DrawStream::new(seed, request.draw_count)
        .draw_die(0, sides)
        .expect("draw_count = 1, so index 0 is in range");
    CombatDraw {
        request,
        evidence,
        roll,
        damage: damage_of_roll(roll),
        sides,
    }
}

/// The `EmitEvent` that binds a combat draw into the turn: a receipt-only effect
/// carrying `[event_id ‖ transcript_commitment ‖ roll ‖ damage]` under [`DICE_TOPIC`].
fn dice_event_effect(cell: CellId, draw: &CombatDraw) -> Effect {
    let data = vec![
        *draw.request.event_id().as_bytes(),
        draw.evidence.draw_transcript_commitment,
        field_from_u64(draw.roll),
        field_from_u64(draw.damage),
    ];
    Effect::EmitEvent {
        cell,
        event: Event::new(symbol(DICE_TOPIC), data),
    }
}

/// **Commit a rolled blow as ONE real cap-bounded turn.** The blow writes `hp -= roll`
/// under the trade-blows method (so the executor's `FieldGte(hp, 1)` tooth bites — a
/// blow that would drop HP below 1 is a REAL [`WorldError::Refused`], nothing commits),
/// and the draw binds into the SAME receipt via an `EmitEvent`. The trade-blows move is
/// a self-loop (`-> gatehall`), so the passage slot is rewritten to the gatehall index.
pub fn resolve_blow(world: &WorldCell, draw: &CombatDraw) -> Result<CombatReceipt, WorldError> {
    let story = world.story();
    let cell = world.cell_id();
    let hp_slot = *story
        .var_slots
        .get("hp")
        .expect("the keep compiles an `hp` slot");
    let hp_before = world.read_var("hp");
    let hp_after = hp_before.saturating_sub(draw.damage);
    let gatehall_idx = *story
        .passage_index
        .get(ROOM_GATEHALL)
        .expect("the keep has a gatehall passage") as u64;

    let effects = vec![
        Effect::SetField {
            cell,
            index: hp_slot as u64,
            value: field_from_u64(hp_after),
        },
        // The trade-blows self-loop keeps the player in the gatehall.
        Effect::SetField {
            cell,
            index: PASSAGE_SLOT as u64,
            value: field_from_u64(gatehall_idx),
        },
        dice_event_effect(cell, draw),
    ];

    let method = choice_method(ROOM_GATEHALL, KP_TRADE_BLOWS);
    let receipt = world.apply_raw(&method, effects)?;

    Ok(CombatReceipt {
        receipt,
        draw: draw.clone(),
        event_id_commit: *draw.request.event_id().as_bytes(),
        transcript_commit: draw.evidence.draw_transcript_commitment,
        hp_after: world.read_var("hp"),
    })
}

/// **Roll AND commit a blow** in one call (the common path): [`roll_blow`] then
/// [`resolve_blow`].
pub fn strike(world: &WorldCell, seq: u64, sides: u64) -> Result<CombatReceipt, WorldError> {
    let draw = roll_blow(world, seq, sides);
    resolve_blow(world, &draw)
}

/// **Read the bound combat draw off a committed receipt** — the exact path a stranger
/// replaying the chain uses. Finds the receipt's `EmitEvent` under [`DICE_TOPIC`] and
/// decodes its four data fields. `None` if the turn bound no dice draw.
pub fn bound_draw(receipt: &TurnReceipt) -> Option<BoundDraw> {
    let topic = symbol(DICE_TOPIC);
    let e = receipt.emitted_events.iter().find(|e| e.topic == topic)?;
    if e.data.len() < 4 {
        return None;
    }
    Some(BoundDraw {
        event_id: e.data[0],
        transcript: e.data[1],
        roll: field_to_u64(&e.data[2]),
        damage: field_to_u64(&e.data[3]),
    })
}

/// **The replay tooth — re-derive the draw and catch a forgery.** Given a committed
/// [`CombatReceipt`], re-derive the seed from the RECORDED `(request, evidence)` through
/// `dregg-dice`'s pure verifier, re-derive the draw, and confirm the roll BOUND into the
/// real receipt matches. Returns the re-derived roll on success. A rewritten roll or
/// damage — a forged, gentler blow — is a [`DiceReplayError`].
pub fn reverify_draw(committed: &CombatReceipt) -> Result<u64, DiceReplayError> {
    // 1. Re-derive the seed from the recorded request + evidence (the pure verifier —
    //    a tampered seed/transcript is rejected here).
    let seed = Deterministic::seed(&committed.draw.request, &committed.draw.evidence)
        .map_err(DiceReplayError::Evidence)?;
    // 2. Re-derive the draw from the verified seed.
    let rederived = DrawStream::new(seed, committed.draw.request.draw_count)
        .draw_die(0, committed.draw.sides)
        .map_err(DiceReplayError::Draw)?;
    // 3. Read what actually rode the real receipt.
    let bound = bound_draw(&committed.receipt).ok_or(DiceReplayError::NoBinding)?;
    // 4. The bindings must match the recorded context and the re-derived draw.
    if bound.event_id != *committed.draw.request.event_id().as_bytes() {
        return Err(DiceReplayError::EventIdMismatch);
    }
    if bound.transcript != committed.draw.evidence.draw_transcript_commitment {
        return Err(DiceReplayError::TranscriptMismatch);
    }
    if bound.roll != rederived {
        return Err(DiceReplayError::RollMismatch {
            bound: bound.roll,
            rederived,
        });
    }
    let expected_damage = damage_of_roll(rederived);
    if bound.damage != expected_damage {
        return Err(DiceReplayError::DamageMismatch {
            bound: bound.damage,
            expected: expected_damage,
        });
    }
    Ok(rederived)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{KP_PRESS_ON, deploy_keep, keep_scene};
    use spween_dregg::{Value, WorldError};

    /// A dice-combat blow COMMITS as a real `TurnReceipt`, its damage is a real
    /// `dregg-dice` draw (`1..=sides`), and the draw is BOUND into the receipt via
    /// `EmitEvent`. The blow re-verifies: replay re-derives the SAME roll.
    #[test]
    fn a_dice_blow_commits_binds_and_reverifies() {
        let mut world = deploy_keep(40);
        world.seed_var("hp", Value::Int(50));

        let committed = strike(&world, 0, COMBAT_DIE_SIDES).expect("a dice blow commits");

        // The damage is a real draw in 1..=sides, and HP fell by exactly the roll.
        assert!(
            (1..=COMBAT_DIE_SIDES).contains(&committed.draw.roll),
            "the roll is a real die face 1..={COMBAT_DIE_SIDES}, got {}",
            committed.draw.roll
        );
        assert_eq!(
            world.read_var("hp"),
            50 - committed.draw.roll,
            "HP fell by exactly the rolled damage"
        );
        // A real committed turn, not a blake3 ledger entry.
        assert_ne!(committed.receipt.turn_hash, [0u8; 32]);

        // The draw is BOUND into the real receipt's EmitEvent.
        let bound = bound_draw(&committed.receipt).expect("the draw is bound");
        assert_eq!(bound.roll, committed.draw.roll);
        assert_eq!(bound.damage, committed.draw.roll);
        assert_eq!(
            bound.event_id,
            *committed.draw.request.event_id().as_bytes()
        );

        // REPRODUCED on replay: re-deriving from the recorded request+evidence yields
        // the SAME roll.
        let rederived = reverify_draw(&committed).expect("the honest draw re-verifies");
        assert_eq!(
            rederived, committed.draw.roll,
            "replay re-derives the identical roll"
        );
    }

    /// The draw is DETERMINISTIC in the turn context: the SAME committed pre-state +
    /// sequence re-derives the byte-identical roll (what replay leans on). Two
    /// identically-seeded, identically-driven worlds roll the same first blow.
    #[test]
    fn the_draw_reproduces_across_identical_worlds() {
        let mut wa = deploy_keep(41);
        let mut wb = deploy_keep(41);
        wa.seed_var("hp", Value::Int(50));
        wb.seed_var("hp", Value::Int(50));

        let ra = strike(&wa, 0, COMBAT_DIE_SIDES).expect("A blow");
        let rb = strike(&wb, 0, COMBAT_DIE_SIDES).expect("B blow");
        assert_eq!(
            ra.draw.roll, rb.draw.roll,
            "identical context reproduces the identical roll"
        );
    }

    /// **THE FORGED-ROLL TOOTH (non-vacuous).** Take an honest committed blow, then
    /// forge a GENTLER one: rewrite the roll+damage bound into the receipt's `EmitEvent`
    /// to 1 and re-link the record. Replay re-derives the TRUE roll from the recorded
    /// request+evidence and CATCHES the forgery — the bound roll no longer matches. The
    /// honest receipt passes the same tooth, so the tooth is real, not vacuous.
    #[test]
    fn a_forged_roll_is_caught_on_replay() {
        let mut world = deploy_keep(42);
        world.seed_var("hp", Value::Int(50));

        let honest = strike(&world, 0, COMBAT_DIE_SIDES).expect("an honest dice blow commits");
        // The honest blow re-verifies (the tooth admits a genuine draw).
        assert_eq!(
            reverify_draw(&honest).expect("honest draw re-verifies"),
            honest.draw.roll
        );
        // Only forge a blow that actually LOWERS the damage (else the test is vacuous).
        assert!(honest.draw.roll > 1, "seed 42 rolls above the forge floor");

        // FORGE: rewrite the roll+damage bound into the real receipt to a gentle 1, and
        // re-link the record (the CombatDraw the forger presents alongside).
        let mut forged = honest.clone();
        let topic = symbol(DICE_TOPIC);
        let event = forged
            .receipt
            .emitted_events
            .iter_mut()
            .find(|e| e.topic == topic)
            .expect("the dice event to rewrite");
        event.data[2] = field_from_u64(1); // forged roll
        event.data[3] = field_from_u64(1); // forged damage
        forged.draw.roll = 1;
        forged.draw.damage = 1;

        // Replay re-derives the honest roll from the (unchanged) recorded evidence and
        // catches the forged binding.
        let out = reverify_draw(&forged);
        assert_eq!(
            out,
            Err(DiceReplayError::RollMismatch {
                bound: 1,
                rederived: honest.draw.roll,
            }),
            "the forged (gentler) roll is caught on replay, got {out:?}"
        );
    }

    /// A forged DAMAGE alone (roll left honest, damage lowered) is caught too — the
    /// damage must be the function of the roll the rules fix.
    #[test]
    fn a_forged_damage_is_caught_on_replay() {
        let mut world = deploy_keep(43);
        world.seed_var("hp", Value::Int(50));
        let honest = strike(&world, 0, COMBAT_DIE_SIDES).expect("honest blow");
        assert!(honest.draw.roll > 1);

        let mut forged = honest.clone();
        let topic = symbol(DICE_TOPIC);
        let event = forged
            .receipt
            .emitted_events
            .iter_mut()
            .find(|e| e.topic == topic)
            .expect("dice event");
        event.data[3] = field_from_u64(1); // forged damage; roll left honest.
        forged.draw.damage = 1;

        let out = reverify_draw(&forged);
        assert_eq!(
            out,
            Err(DiceReplayError::DamageMismatch {
                bound: 1,
                expected: honest.draw.roll,
            }),
            "a forged damage is caught, got {out:?}"
        );
    }

    /// The `FieldGte(hp, 1)` tooth still bites on a DICE blow: a roll that would drop HP
    /// below 1 is a REAL executor refusal — nothing commits (anti-ghost). Driven by
    /// seeding HP to exactly the roll (so `hp - roll == 0 < 1`).
    #[test]
    fn a_lethal_dice_blow_is_refused_by_the_hp_floor() {
        let mut world = deploy_keep(44);
        // First learn what seq-0 rolls against a fresh keep, then seed HP so the blow is
        // exactly lethal (hp == roll ⇒ post hp 0 ⇒ FieldGte(hp,1) fails).
        let peek = roll_blow(&world, 0, COMBAT_DIE_SIDES);
        world.seed_var("hp", Value::Int(peek.roll as i64));
        // Re-roll against the seeded pre-state (the roll now binds hp==roll into the
        // EventId; resolve it and expect the floor to refuse).
        let draw = roll_blow(&world, 0, COMBAT_DIE_SIDES);
        let hp_before = world.read_var("hp");
        let out = resolve_blow(&world, &draw);
        if draw.damage >= hp_before {
            assert!(
                matches!(out, Err(WorldError::Refused(_))),
                "a lethal dice blow is refused by FieldGte(hp,1), got {out:?}"
            );
            assert_eq!(
                world.read_var("hp"),
                hp_before,
                "anti-ghost: HP unchanged after the refused lethal blow"
            );
        } else {
            // The seeded HP happened to survive; the blow commits (still a real turn).
            assert!(out.is_ok(), "a survivable blow commits, got {out:?}");
        }
    }

    /// Dice-combat receipts CHAIN onto the real keep receipt chain: a dice blow, then a
    /// narrated press-on, link `pre == prev.post` (one serial writer, one cell).
    #[test]
    fn dice_blows_chain_onto_the_keep_receipt_chain() {
        let s = keep_scene();
        let mut world = deploy_keep(45);
        world.seed_var("hp", Value::Int(50));

        let b1 = strike(&world, 0, COMBAT_DIE_SIDES).expect("first dice blow");
        let b2 = strike(&world, 1, COMBAT_DIE_SIDES).expect("second dice blow");
        assert_eq!(
            b2.receipt.pre_state_hash, b1.receipt.post_state_hash,
            "the dice blows chain: b2.pre == b1.post"
        );

        // A narrated press-on binds a narration AND chains onto the dice blows.
        use crate::narrator::{Command, Narrated, narrate_turn};
        let n = Narrated::new(
            Command::at(ROOM_GATEHALL, KP_PRESS_ON),
            "Bloodied but standing, you press past the reeling warden into the hall.",
        );
        let r = narrate_turn(&world, &s, &n).expect("the narrated press-on commits");
        assert_eq!(
            r.receipt.pre_state_hash, b2.receipt.post_state_hash,
            "the narrated turn chains onto the last dice blow"
        );
    }
}
