//! Path of Angels Signal claim transport.
//!
//! A public claim deliberately contains only a mission id and one bounded
//! Signal code.  Identity and state authority ride outside the event in the
//! signed/finalized turn; there is no slot here for a signer key, actor root,
//! Canon/config, or a replay counter.

use dregg_cell::{CellId, FieldElement, Preconditions, field_from_u64, field_to_u64};
use dregg_turn::action::{Authorization, CommitmentMode, Event, symbol};
use dregg_turn::{ComputronCosts, TurnExecutor};

/// Exact reserved event topic for a version-1 Signal claim.
pub const SIGNAL_CLAIM_TOPIC_V1: &str = "pathofangels.network/signal-claim/v1";

/// Exact method carried by the one-action Signal claim turn.
pub const SIGNAL_CLAIM_METHOD_V1: &str = "poa-signal";

/// Signal codes use three base-six bands.
pub const SIGNAL_BAND_MAX: u64 = 5;

/// The public mission-id wire is the same bounded id lane as the Lean judge.
pub const SIGNAL_MISSION_ID_MAX: u64 = u32::MAX as u64;

/// A bounded Signal Triangulation code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignalCode {
    low: u8,
    mid: u8,
    high: u8,
}

impl SignalCode {
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignalClaimV1 {
    mission_id: u32,
    code: SignalCode,
}

impl SignalClaimV1 {
    /// Construct a claim without narrowing or wrapping its mission id.
    pub fn new(mission_id: u64, code: SignalCode) -> Result<Self, SignalClaimError> {
        if mission_id > SIGNAL_MISSION_ID_MAX {
            return Err(SignalClaimError::MissionIdOutOfRange(mission_id));
        }
        Ok(Self {
            mission_id: mission_id as u32,
            code,
        })
    }

    pub fn mission_id(self) -> u32 {
        self.mission_id
    }

    pub fn code(self) -> SignalCode {
        self.code
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
/// The four canonical field lanes are `(mission_id, low, mid, high)`.  The
/// emitting cell and the outer turn signature identify the actor; duplicating
/// either here would turn authority into caller-authored payload.
pub fn signal_claim_event(claim: SignalClaimV1) -> Event {
    Event::new(
        symbol(SIGNAL_CLAIM_TOPIC_V1),
        vec![
            field_from_u64(u64::from(claim.mission_id)),
            field_from_u64(u64::from(claim.code.low)),
            field_from_u64(u64::from(claim.code.mid)),
            field_from_u64(u64::from(claim.code.high)),
        ],
    )
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
    if event.data.len() != 4 {
        return Err(SignalClaimError::MalformedReserved(
            "expected exactly four data fields",
        ));
    }

    let mission_id = exact_u64_lane(&event.data[0])?;
    let low = exact_u64_lane(&event.data[1])?;
    let mid = exact_u64_lane(&event.data[2])?;
    let high = exact_u64_lane(&event.data[3])?;
    let code = SignalCode::new(low, mid, high)?;
    let claim = SignalClaimV1::new(mission_id, code)?;
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

    fn claim() -> SignalClaimV1 {
        SignalClaimV1::new(7, SignalCode::new(2, 4, 1).unwrap()).unwrap()
    }

    #[test]
    fn constructor_and_classifier_are_exact_inverses() {
        let expected = claim();
        let event = signal_claim_event(expected);
        assert_eq!(event.topic, symbol(SIGNAL_CLAIM_TOPIC_V1));
        assert_eq!(event.data.len(), 4, "no authority field fits in the claim");
        assert_eq!(
            classify_signal_event(&event),
            Ok(SignalEventRoute::Signal(expected))
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
        for data in [vec![], vec![field_from_u64(1)], vec![field_from_u64(1); 5]] {
            assert!(matches!(
                classify_signal_event(&Event::new(reserved, data)),
                Err(SignalClaimError::MalformedReserved(_))
            ));
        }
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
        bad_band.data[3] = field_from_u64(6);
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
        assert_eq!(event.data.len(), 4, "claim has no authority field");
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
}
