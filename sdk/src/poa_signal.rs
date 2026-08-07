//! Path of Angels Signal claim transport.
//!
//! A public claim carries a mission id and the TRANSCRIPT that was played —
//! between one and `SignalTriangulation.MAX_TURNS` bounded Signal codes, in the
//! order they were submitted.  Identity and state authority ride outside the
//! event in the signed/finalized turn; there is no slot here for a signer key,
//! actor root, Canon/config, or a replay counter.
//!
//! # ⚑ FLAG DAY, 2026-08-07 — the claim stopped being a lone code
//!
//! It used to carry exactly one code and four field lanes, and that was the whole
//! blind path: `SignalTriangulation.judge` scores a ONE-ACTION transcript, so any
//! caller who guessed the target settled without ever playing — 1 in 216, and no
//! session, no feedback, no deduction anywhere in the causal chain of a settled
//! turn.  A claim now names every round, and the node refuses one whose rounds it
//! did not itself classify (`node::poa_signal_adapter::verify_claim_transcript_was_played`).
//!
//! **What re-emits / refuses to load:**
//!
//! * Every previously built `poa-signal` carrier **refuses to decode**:
//!   [`classify_signal_event`] demands exactly [`SIGNAL_CLAIM_EVENT_LANES`] lanes
//!   and an old carrier has four, so it is a `MalformedReserved` refusal rather
//!   than an event that falls through to an ordinary consumer.
//! * The canonical claim FEE moved (the event carries seventeen lanes instead of
//!   four), so every genesis player grant priced off [`signal_claim_fee_v1`] must
//!   be re-emitted.  It is still a constant of the SHAPE — see that function.
//! * `request.actions` in the `POA-SIGNAL-IN-1` judge wire is now the played
//!   transcript rather than a singleton, so retained judge inputs from before the
//!   flag day replay against a different receipt `transcriptDigest`; the PoA
//!   authority is re-genesised.
//!
//! # ⚠ Why the reserved TOPIC did not move with the payload
//!
//! The topic is the RESERVATION — the marker that says "this is a Signal claim,
//! judge it" — not the payload version.  Bumping it to `/v2` would have made every
//! old carrier classify as [`SignalEventRoute::Ordinary`] and execute as a plain
//! event turn: reinterpreted, silently, which is the one thing a flag day may not
//! do.  Keeping the reservation and changing the LANE LAYOUT makes the old shape
//! refuse by name instead.

use dregg_cell::{CellId, FieldElement, Preconditions, field_from_u64, field_to_u64};
use dregg_turn::action::{Authorization, CommitmentMode, Event, symbol};
use dregg_turn::{ComputronCosts, TurnExecutor};

/// Exact reserved event topic for a Signal claim.  See the module header for why
/// this string did not move when the payload did.
pub const SIGNAL_CLAIM_TOPIC_V1: &str = "pathofangels.network/signal-claim/v1";

/// Exact method carried by the one-action Signal claim turn.
pub const SIGNAL_CLAIM_METHOD_V1: &str = "poa-signal";

/// Signal codes use three base-six bands.
pub const SIGNAL_BAND_MAX: u64 = 5;

/// The public mission-id wire is the same bounded id lane as the Lean judge.
pub const SIGNAL_MISSION_ID_MAX: u64 = u32::MAX as u64;

/// The complete action budget of one judged run.
///
/// ⚠ This is `SignalTriangulation.MAX_TURNS`, and it is also
/// `NetworkJudgeWire.WIRE_ACTION_LIMIT` and
/// `dregg_persist::POA_SIGNAL_SESSION_MAX_ROUNDS`.  A claim longer than this is
/// refused here rather than at the judge, because `replay`'s sixth `step` returns
/// `none` and the player would have paid a turn fee to learn it.
pub const SIGNAL_MAX_TRANSCRIPT_ROUNDS: usize = 5;

/// Field lanes in the reserved event: `mission_id`, `rounds`, then FIVE band
/// triples — the played ones followed by exact zeros.
///
/// ⚠ FIXED WIDTH ON PURPOSE.  A variable-length event would make the claim fee a
/// function of how many bursts the player needed, so a three-round solver and a
/// five-round solver would need different genesis grants and
/// [`signal_claim_fee_v1`] could not be quoted at all.  The padding costs a few
/// computrons and buys back "the fee is a constant of the shape".
pub const SIGNAL_CLAIM_EVENT_LANES: usize = 2 + 3 * SIGNAL_MAX_TRANSCRIPT_ROUNDS;

/// A bounded Signal Triangulation code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignalCode {
    low: u8,
    mid: u8,
    high: u8,
}

impl SignalCode {
    /// The all-zero code.  It is a LEGAL guess, and it is also the padding an
    /// unplayed transcript lane must carry; `rounds` is what tells the two apart,
    /// which is why the decoder reads the count before the bands.
    pub const ZERO: Self = Self {
        low: 0,
        mid: 0,
        high: 0,
    };

    /// Construct a code, refusing rather than truncating any non-base-six band.
    pub fn new(low: u64, mid: u64, high: u64) -> Result<Self, SignalClaimError> {
        for (name, value) in [("low", low), ("mid", mid), ("high", high)] {
            if value > SIGNAL_BAND_MAX {
                return Err(SignalClaimError::BandOutOfRange { name, value });
            }
        }
        Ok(Self {
            low: low as u8,
            mid: mid as u8,
            high: high as u8,
        })
    }

    pub fn low(self) -> u8 {
        self.low
    }

    pub fn mid(self) -> u8 {
        self.mid
    }

    pub fn high(self) -> u8 {
        self.high
    }
}

/// The complete public Signal claim.  It intentionally has no authority fields.
///
/// ⚠ `transcript` is a FIXED array with `rounds` live entries and exact zeros
/// after; that is the wire layout, held in the same shape in memory so an encoder
/// and a decoder cannot disagree about where the padding starts.  Read it through
/// [`SignalClaimV1::transcript`], never directly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignalClaimV1 {
    mission_id: u32,
    rounds: u8,
    transcript: [SignalCode; SIGNAL_MAX_TRANSCRIPT_ROUNDS],
}

impl SignalClaimV1 {
    /// Construct a claim without narrowing or wrapping its mission id, and
    /// without admitting a transcript the judge's `replay` could not score.
    pub fn new(mission_id: u64, transcript: &[SignalCode]) -> Result<Self, SignalClaimError> {
        if mission_id > SIGNAL_MISSION_ID_MAX {
            return Err(SignalClaimError::MissionIdOutOfRange(mission_id));
        }
        if transcript.is_empty() || transcript.len() > SIGNAL_MAX_TRANSCRIPT_ROUNDS {
            return Err(SignalClaimError::TranscriptOutOfRange(transcript.len()));
        }
        let mut rounds = [SignalCode::ZERO; SIGNAL_MAX_TRANSCRIPT_ROUNDS];
        rounds[..transcript.len()].copy_from_slice(transcript);
        Ok(Self {
            mission_id: mission_id as u32,
            rounds: transcript.len() as u8,
            transcript: rounds,
        })
    }

    pub fn mission_id(self) -> u32 {
        self.mission_id
    }

    /// The played rounds, in submission order.  Never empty.
    pub fn transcript(&self) -> &[SignalCode] {
        &self.transcript[..self.rounds as usize]
    }

    /// The last round — the one that must LOCK all three bands for the judge to
    /// accept, because `SignalTriangulation.step` refuses every action after a
    /// solved state and `terminalOutput` refuses an unsolved one.
    pub fn final_code(self) -> SignalCode {
        self.transcript[self.rounds as usize - 1]
    }
}

/// Classification result for an event at the reserved ingress seam.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SignalEventRoute {
    /// The event does not use the reserved Signal topic.
    Ordinary,
    /// An exact version-1 Signal claim.
    Signal(SignalClaimV1),
}

/// Construction/classification refusal.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum SignalClaimError {
    #[error("Signal band {name}={value} exceeds the base-six bound")]
    BandOutOfRange { name: &'static str, value: u64 },
    #[error("Signal mission id {0} exceeds the 32-bit wire bound")]
    MissionIdOutOfRange(u64),
    #[error(
        "a Signal claim carries the transcript that was played; {0} rounds is outside 1..={SIGNAL_MAX_TRANSCRIPT_ROUNDS}"
    )]
    TranscriptOutOfRange(usize),
    #[error("reserved Signal claim marker is malformed: {0}")]
    MalformedReserved(&'static str),
}

/// Refusal from the exact Signal carrier boundary.
///
/// This is intentionally stricter than merely finding a reserved event in a
/// forest: a player claim cannot smuggle a second action, child, effect, memo,
/// proof, dependency, or state mutation beside the public Signal code.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum SignalCarrierError {
    #[error("invalid Signal claim carrier: {0}")]
    InvalidShape(&'static str),
    #[error(transparent)]
    Claim(#[from] SignalClaimError),
}

/// Construct the exact reserved event.
///
/// The [`SIGNAL_CLAIM_EVENT_LANES`] canonical field lanes are `mission_id`,
/// `rounds`, then five `(low, mid, high)` triples — the played rounds followed by
/// exact zeros.  The emitting cell and the outer turn signature identify the
/// actor; duplicating either here would turn authority into caller-authored
/// payload.
pub fn signal_claim_event(claim: SignalClaimV1) -> Event {
    let mut data = Vec::with_capacity(SIGNAL_CLAIM_EVENT_LANES);
    data.push(field_from_u64(u64::from(claim.mission_id)));
    data.push(field_from_u64(u64::from(claim.rounds)));
    // ALL FIVE triples, padding included: the width is what makes the fee a
    // constant of the shape.
    for code in claim.transcript.iter() {
        data.push(field_from_u64(u64::from(code.low)));
        data.push(field_from_u64(u64::from(code.mid)));
        data.push(field_from_u64(u64::from(code.high)));
    }
    debug_assert_eq!(data.len(), SIGNAL_CLAIM_EVENT_LANES);
    Event::new(symbol(SIGNAL_CLAIM_TOPIC_V1), data)
}

/// Derive the player cell used by the node's signed-turn perimeter.
pub fn signal_player_cell(signer_public_key: &[u8; 32]) -> CellId {
    CellId::derive_raw(signer_public_key, blake3::hash(b"default").as_bytes())
}

/// Construct the only player-authored turn shape accepted by the PoA Signal
/// client: one root, no children, one `EmitEvent`, and no unrelated turn data.
///
/// The action is deliberately `Unchecked`: this is the canonical zero-auth
/// scaffold consumed immediately by the signing flow.  Its fee is nevertheless
/// estimated as the hybrid authorization it will become, so the signed turn is
/// not underfunded after Ed25519 + ML-DSA authorization is attached.
pub fn signal_claim_turn(
    signer_public_key: &[u8; 32],
    nonce: u64,
    previous_receipt_hash: Option<[u8; 32]>,
    claim: SignalClaimV1,
) -> dregg_turn::Turn {
    let agent = signal_player_cell(signer_public_key);
    let effect = dregg_turn::Effect::EmitEvent {
        cell: agent,
        event: signal_claim_event(claim),
    };
    let action = crate::raw::unsigned_action_named(agent, SIGNAL_CLAIM_METHOD_V1, vec![effect]);
    let mut builder = crate::raw::RawTurnBuilder::new(agent, nonce);
    if let Some(hash) = previous_receipt_hash {
        builder.set_previous_receipt_hash(hash);
    }
    builder.add_action(action);
    let mut turn = builder.build();
    turn.fee = signal_claim_hybrid_fee(&turn);
    turn
}

/// The exact fee every canonical version-1 Signal claim turn carries.
///
/// It is a constant of the claim SHAPE, not of its contents. `estimate_cost`
/// prices `action_base + 2×signature_verify` for the hybrid carrier plus one
/// `EmitEvent` whose reserved topic and [`SIGNAL_CLAIM_EVENT_LANES`] field lanes
/// are the same width for every mission id, every transcript, and every player key
/// — so this number does not depend on who claims or what they claim.
/// `signal_claim_fee_is_a_constant_of_the_shape` pins that, and it is a real
/// check rather than a restatement: it recomputes the fee across several keys,
/// missions, codes AND transcript lengths and requires one value.
///
/// ⚑ IT MOVED ON 2026-08-07 and every genesis grant priced off it must be
/// re-emitted. The event went from four lanes to seventeen when the claim started
/// carrying the played transcript. The fixed width is exactly what keeps this
/// function quotable: a variable-length event would price a three-round solver
/// differently from a five-round one, and a genesis descriptor is written before
/// anybody has played.
///
/// ⚑ WHY IT IS PUBLIC. Genesis has to fund a player with this number. Until
/// 2026-08-07 the live Path of Angels chain held no value at all — two
/// zero-balance wells and no genesis moves — so no player could pay this fee and
/// `latest_height` could not move off 0. The genesis grant that fixes it is only
/// meaningful against the fee it must cover, and the one place worth refusing an
/// underfunded grant is where the operator types the amount, before a chain
/// exists. A caller that hardcodes a number instead of calling this will silently
/// desynchronize from `ComputronCosts::default()`.
pub fn signal_claim_fee_v1() -> u64 {
    let claim =
        SignalClaimV1::new(0, &[SignalCode::ZERO]).expect("a one-round mission-0 claim is legal");
    signal_claim_turn(&[0u8; 32], 0, None, claim).fee
}

/// Compute the fee for the post-signing hybrid carrier without manufacturing a
/// credential. `estimate_cost` keys on authorization kind, not signature bytes.
fn signal_claim_hybrid_fee(turn: &dregg_turn::Turn) -> u64 {
    let mut priced = turn.clone();
    if let Some(root) = priced.call_forest.roots.first_mut() {
        root.action.authorization = Authorization::HybridSignature {
            ed25519: [0; 64],
            ml_dsa: Vec::new(),
            ml_dsa_pk: Vec::new(),
        };
        root.hash = [0; 32];
    }
    priced.call_forest.forest_hash = [0; 32];
    TurnExecutor::new(ComputronCosts::default()).estimate_cost(&priced)
}

/// Decode an exact Signal carrier, refusing every opportunity to piggyback an
/// unrelated mutation or caller-authored authority field.
///
/// Both the pre-signing `Unchecked` scaffold and the post-signing classical or
/// hybrid signature are recognized. Other authorization modes are not part of
/// this player flow.
pub fn claim_from_exact_signal_turn(
    turn: &dregg_turn::Turn,
) -> Result<SignalClaimV1, SignalCarrierError> {
    if turn.memo.is_some()
        || turn.valid_until.is_some()
        || !turn.depends_on.is_empty()
        || turn.conservation_proof.is_some()
        || !turn.sovereign_witnesses.is_empty()
        || turn.execution_proof.is_some()
        || turn.execution_proof_cell.is_some()
        || turn.execution_proof_new_commitment.is_some()
        || turn.custom_program_proofs.is_some()
        || !turn.effect_binding_proofs.is_empty()
        || !turn.cross_effect_dependencies.is_empty()
        || !turn.effect_witness_index_map.is_empty()
    {
        return Err(SignalCarrierError::InvalidShape(
            "unrelated turn metadata or proof material is present",
        ));
    }
    if turn.call_forest.roots.len() != 1 {
        return Err(SignalCarrierError::InvalidShape(
            "expected exactly one root action",
        ));
    }
    let root = &turn.call_forest.roots[0];
    if !root.children.is_empty() {
        return Err(SignalCarrierError::InvalidShape(
            "Signal action cannot have children",
        ));
    }
    let action = &root.action;
    if action.target != turn.agent
        || action.method != symbol(SIGNAL_CLAIM_METHOD_V1)
        || !action.args.is_empty()
        || action.preconditions != Preconditions::default()
        || action.may_delegate != dregg_turn::DelegationMode::None
        || action.commitment_mode != CommitmentMode::Full
        || action.balance_change.is_some()
        || !action.witness_blobs.is_empty()
    {
        return Err(SignalCarrierError::InvalidShape(
            "action is not the canonical Signal action",
        ));
    }
    if !matches!(
        action.authorization,
        Authorization::Unchecked
            | Authorization::Signature(_, _)
            | Authorization::HybridSignature { .. }
    ) {
        return Err(SignalCarrierError::InvalidShape(
            "unsupported Signal action authorization",
        ));
    }
    if action.effects.len() != 1 {
        return Err(SignalCarrierError::InvalidShape(
            "expected exactly one Signal event effect",
        ));
    }
    let dregg_turn::Effect::EmitEvent { cell, event } = &action.effects[0] else {
        return Err(SignalCarrierError::InvalidShape(
            "Signal carrier effect is not EmitEvent",
        ));
    };
    if *cell != turn.agent {
        return Err(SignalCarrierError::InvalidShape(
            "Signal event emitter is not the player agent",
        ));
    }
    if turn.fee != signal_claim_hybrid_fee(turn) {
        return Err(SignalCarrierError::InvalidShape(
            "fee does not match the canonical hybrid carrier cost",
        ));
    }
    match classify_signal_event(event)? {
        SignalEventRoute::Signal(claim) => Ok(claim),
        SignalEventRoute::Ordinary => Err(SignalCarrierError::InvalidShape(
            "event does not use the reserved Signal topic",
        )),
    }
}

/// Classify an event without permitting malformed reserved events to fall
/// through to an ordinary-event consumer.
pub fn classify_signal_event(event: &Event) -> Result<SignalEventRoute, SignalClaimError> {
    if event.topic != symbol(SIGNAL_CLAIM_TOPIC_V1) {
        return Ok(SignalEventRoute::Ordinary);
    }
    // ⚑ THE FLAG DAY LANDS HERE. A pre-2026-08-07 carrier has FOUR lanes and is
    // refused by this line, by name, rather than being read as a claim that means
    // something else. `an_old_single_code_carrier_refuses_to_decode` pins it.
    if event.data.len() != SIGNAL_CLAIM_EVENT_LANES {
        return Err(SignalClaimError::MalformedReserved(
            "expected exactly seventeen data fields: mission id, round count, and five band triples",
        ));
    }

    let mission_id = exact_u64_lane(&event.data[0])?;
    let rounds = exact_u64_lane(&event.data[1])?;
    if rounds == 0 || rounds > SIGNAL_MAX_TRANSCRIPT_ROUNDS as u64 {
        return Err(SignalClaimError::TranscriptOutOfRange(rounds as usize));
    }
    let mut transcript = [SignalCode::ZERO; SIGNAL_MAX_TRANSCRIPT_ROUNDS];
    for (index, slot) in transcript.iter_mut().enumerate() {
        let base = 2 + 3 * index;
        *slot = SignalCode::new(
            exact_u64_lane(&event.data[base])?,
            exact_u64_lane(&event.data[base + 1])?,
            exact_u64_lane(&event.data[base + 2])?,
        )?;
    }
    // The padding is EXACTLY zero, or the encoding is not injective: two carriers
    // spelling one transcript are two turn hashes for one game, and the shorter
    // one's spare lanes are a free side channel through the receipt's
    // `transcriptDigest`.
    if transcript[rounds as usize..]
        .iter()
        .any(|code| *code != SignalCode::ZERO)
    {
        return Err(SignalClaimError::MalformedReserved(
            "unplayed transcript lanes must be exactly zero",
        ));
    }
    let claim = SignalClaimV1::new(mission_id, &transcript[..rounds as usize])?;
    Ok(SignalEventRoute::Signal(claim))
}

fn exact_u64_lane(field: &FieldElement) -> Result<u64, SignalClaimError> {
    let value = field_to_u64(field);
    if *field != field_from_u64(value) {
        return Err(SignalClaimError::MalformedReserved(
            "data field is not a canonical unsigned-64 lane",
        ));
    }
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn code(low: u64, mid: u64, high: u64) -> SignalCode {
        SignalCode::new(low, mid, high).expect("a base-six code")
    }

    /// A three-round transcript: two losing bursts and the solving one.
    fn claim() -> SignalClaimV1 {
        SignalClaimV1::new(7, &[code(0, 0, 0), code(3, 3, 3), code(2, 4, 1)]).unwrap()
    }

    #[test]
    fn constructor_and_classifier_are_exact_inverses() {
        let expected = claim();
        let event = signal_claim_event(expected);
        assert_eq!(event.topic, symbol(SIGNAL_CLAIM_TOPIC_V1));
        assert_eq!(
            event.data.len(),
            SIGNAL_CLAIM_EVENT_LANES,
            "no authority field fits in the claim, and the width never varies"
        );
        assert_eq!(
            classify_signal_event(&event),
            Ok(SignalEventRoute::Signal(expected))
        );
        assert_eq!(expected.transcript().len(), 3);
        assert_eq!(expected.final_code(), code(2, 4, 1));
    }

    /// ⚑ THE FLAG DAY, ASSERTED ON THE EXACT OLD BYTES.
    ///
    /// A pre-2026-08-07 carrier is `[mission_id, low, mid, high]` under the same
    /// reserved topic. It must REFUSE — not decode to something else, and above all
    /// not fall through as an ordinary event, which is what a topic bump would have
    /// produced. This is constructed here rather than described, so the refusal is
    /// measured against the bytes that actually existed.
    #[test]
    fn an_old_single_code_carrier_refuses_to_decode() {
        let legacy = Event::new(
            symbol(SIGNAL_CLAIM_TOPIC_V1),
            vec![
                field_from_u64(1),
                field_from_u64(5),
                field_from_u64(0),
                field_from_u64(5),
            ],
        );
        assert_eq!(legacy.data.len(), 4, "the old carrier had four lanes");
        assert!(
            matches!(
                classify_signal_event(&legacy),
                Err(SignalClaimError::MalformedReserved(_))
            ),
            "an old one-code carrier must refuse to decode, by name"
        );
    }

    #[test]
    fn ordinary_event_is_not_captured() {
        let event = Event::new(symbol("ordinary"), vec![field_from_u64(7)]);
        assert_eq!(
            classify_signal_event(&event),
            Ok(SignalEventRoute::Ordinary)
        );
    }

    #[test]
    fn malformed_reserved_marker_never_falls_through() {
        let reserved = symbol(SIGNAL_CLAIM_TOPIC_V1);
        for data in [
            vec![],
            vec![field_from_u64(1)],
            vec![field_from_u64(1); 4],
            vec![field_from_u64(1); SIGNAL_CLAIM_EVENT_LANES - 1],
            vec![field_from_u64(1); SIGNAL_CLAIM_EVENT_LANES + 1],
        ] {
            assert!(matches!(
                classify_signal_event(&Event::new(reserved, data)),
                Err(SignalClaimError::MalformedReserved(_))
            ));
        }
    }

    /// The round count is bounded at both ends, and the lanes past it must be
    /// exactly zero — otherwise one played transcript has many spellings, each a
    /// different turn hash and a free channel through the receipt digest.
    #[test]
    fn the_round_count_and_its_padding_are_canonical() {
        let mut zero_rounds = signal_claim_event(claim());
        zero_rounds.data[1] = field_from_u64(0);
        assert!(matches!(
            classify_signal_event(&zero_rounds),
            Err(SignalClaimError::TranscriptOutOfRange(0))
        ));

        let mut too_many = signal_claim_event(claim());
        too_many.data[1] = field_from_u64(SIGNAL_MAX_TRANSCRIPT_ROUNDS as u64 + 1);
        assert!(matches!(
            classify_signal_event(&too_many),
            Err(SignalClaimError::TranscriptOutOfRange(6))
        ));

        // Round 3 is padding on a three-round claim; a non-zero band there refuses.
        let mut dirty_padding = signal_claim_event(claim());
        dirty_padding.data[2 + 3 * 3] = field_from_u64(1);
        assert!(matches!(
            classify_signal_event(&dirty_padding),
            Err(SignalClaimError::MalformedReserved(
                "unplayed transcript lanes must be exactly zero"
            ))
        ));

        // …and a FIVE-round claim has no padding at all, so every lane is live.
        let full = SignalClaimV1::new(
            1,
            &[
                code(0, 0, 0),
                code(1, 1, 1),
                code(2, 2, 2),
                code(3, 3, 3),
                code(4, 4, 4),
            ],
        )
        .unwrap();
        assert_eq!(
            classify_signal_event(&signal_claim_event(full)),
            Ok(SignalEventRoute::Signal(full))
        );
        assert!(
            SignalClaimV1::new(1, &[code(0, 0, 0); 6]).is_err(),
            "a sixth round is outside SignalTriangulation.MAX_TURNS"
        );
        assert!(
            SignalClaimV1::new(1, &[]).is_err(),
            "a claim with no transcript names no game"
        );
    }

    #[test]
    fn noncanonical_and_out_of_range_reserved_fields_refuse() {
        let mut noncanonical = signal_claim_event(claim());
        noncanonical.data[0][0] = 1;
        assert!(matches!(
            classify_signal_event(&noncanonical),
            Err(SignalClaimError::MalformedReserved(_))
        ));

        let mut bad_band = signal_claim_event(claim());
        bad_band.data[4] = field_from_u64(6);
        assert!(matches!(
            classify_signal_event(&bad_band),
            Err(SignalClaimError::BandOutOfRange { .. })
        ));

        let mut bad_mission = signal_claim_event(claim());
        bad_mission.data[0] = field_from_u64(SIGNAL_MISSION_ID_MAX + 1);
        assert!(matches!(
            classify_signal_event(&bad_mission),
            Err(SignalClaimError::MissionIdOutOfRange(_))
        ));
    }

    #[test]
    fn exact_carrier_builder_has_one_public_event_and_no_authority_payload() {
        let signer = [0x51; 32];
        let previous = [0xA7; 32];
        let turn = signal_claim_turn(&signer, 9, Some(previous), claim());

        assert_eq!(turn.agent, signal_player_cell(&signer));
        assert_eq!(turn.nonce, 9);
        assert_eq!(turn.previous_receipt_hash, Some(previous));
        assert_eq!(turn.call_forest.action_count(), 1);
        assert_eq!(claim_from_exact_signal_turn(&turn), Ok(claim()));

        let action = &turn.call_forest.roots[0].action;
        assert_eq!(action.effects.len(), 1);
        let dregg_turn::Effect::EmitEvent { cell, event } = &action.effects[0] else {
            panic!("exact carrier must emit one event")
        };
        assert_eq!(*cell, turn.agent);
        assert_eq!(
            event.data.len(),
            SIGNAL_CLAIM_EVENT_LANES,
            "claim has no authority field"
        );
    }

    #[test]
    fn exact_carrier_refuses_piggyback_effects_and_turn_metadata() {
        let signer = [0x52; 32];
        let mut extra_effect = signal_claim_turn(&signer, 0, None, claim());
        extra_effect.call_forest.roots[0]
            .action
            .effects
            .push(dregg_turn::Effect::IncrementNonce {
                cell: extra_effect.agent,
            });
        assert!(matches!(
            claim_from_exact_signal_turn(&extra_effect),
            Err(SignalCarrierError::InvalidShape(
                "expected exactly one Signal event effect"
            ))
        ));

        let mut memo = signal_claim_turn(&signer, 0, None, claim());
        memo.memo = Some("caller-authored authority".into());
        assert!(matches!(
            claim_from_exact_signal_turn(&memo),
            Err(SignalCarrierError::InvalidShape(_))
        ));
    }

    #[test]
    fn a_substituted_transcript_is_not_the_carried_claim() {
        let signer = [0x54; 32];
        let honest = claim();
        let turn = signal_claim_turn(&signer, 0, None, honest);
        // Same solving code, one fewer round played — a DIFFERENT claim, because the
        // transcript is what the judge scores and what the node checks it issued.
        let shortened = SignalClaimV1::new(7, &[code(3, 3, 3), code(2, 4, 1)]).unwrap();
        assert_ne!(honest, shortened);
        assert_ne!(
            signal_claim_event(honest).data,
            signal_claim_event(shortened).data,
            "two transcripts ending in the same code must not share a carrier"
        );
        assert_eq!(claim_from_exact_signal_turn(&turn), Ok(honest));
    }

    #[test]
    fn exact_carrier_fee_is_for_the_signed_hybrid_shape() {
        let signer = [0x53; 32];
        let mut turn = signal_claim_turn(&signer, 3, None, claim());
        turn.call_forest.roots[0].action.authorization = Authorization::HybridSignature {
            ed25519: [0x11; 64],
            ml_dsa: vec![0x22; 8],
            ml_dsa_pk: vec![0x33; 8],
        };
        assert_eq!(claim_from_exact_signal_turn(&turn), Ok(claim()));
        assert_eq!(
            turn.fee,
            TurnExecutor::new(ComputronCosts::default()).estimate_cost(&turn)
        );
    }

    /// [`signal_claim_fee_v1`] is quotable as THE Signal claim fee only if the
    /// fee genuinely does not vary with the player, the mission, the code — or,
    /// since the flag day, HOW MANY ROUNDS THE PLAYER NEEDED. Genesis funds a
    /// grant against this number without knowing any of them, so if it varied the
    /// grant would be right for one player and wrong for the next, and right for a
    /// lucky solver and wrong for a careful one.
    #[test]
    fn signal_claim_fee_is_a_constant_of_the_shape() {
        let quoted = signal_claim_fee_v1();
        assert!(
            quoted > 0,
            "a free Signal claim would need no funding at all"
        );
        let played = [
            code(0, 0, 0),
            code(5, 4, 3),
            code(1, 1, 1),
            code(2, 0, 4),
            code(3, 5, 2),
        ];
        for signer in [[0x00u8; 32], [0xff; 32], [0x5a; 32]] {
            for nonce in [0u64, 1, u64::MAX] {
                for mission in [0u64, 7, u32::MAX as u64] {
                    for rounds in 1..=SIGNAL_MAX_TRANSCRIPT_ROUNDS {
                        let claim = SignalClaimV1::new(mission, &played[..rounds]).unwrap();
                        for previous in [None, Some([0x9du8; 32])] {
                            assert_eq!(
                                signal_claim_turn(&signer, nonce, previous, claim).fee,
                                quoted,
                                "the Signal claim fee must not depend on \
                                 signer/nonce/mission/transcript/receipt",
                            );
                        }
                    }
                }
            }
        }
    }
}
