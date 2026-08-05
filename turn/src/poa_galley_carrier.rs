//! Canonical Path of Angels Galley player-command carrier.
//!
//! This is the lowest shared wire/shape authority for Galley commands.  It is
//! deliberately below the SDK so persistence and finality code can classify a
//! submitted [`SignedTurn`] without acquiring a dependency on client builders.
//! The carrier authenticates signed intent and exact structure only: action
//! tokens, holder receipts, PQ admission policy, and atomic consumption remain
//! node/finality responsibilities.

use core::fmt;

use dregg_cell::{CellId, FieldElement, Preconditions, field_from_u64, field_to_u64};

use crate::action::{Authorization, CommitmentMode, Event, symbol};
use crate::{
    Action, ComputronCosts, DelegationMode, Effect, SignedTurn, Turn, TurnBuilder, TurnExecutor,
};

/// Exact reserved event topic for a version-1 Galley player command.
pub const GALLEY_COMMAND_TOPIC_V1: &str = "pathofangels.network/galley-command/v1";

/// Exact method carried by the one-action Galley player turn.
pub const GALLEY_COMMAND_METHOD_V1: &str = "poa-galley";

pub const PUBLIC_VOTE_TAG_V1: u64 = 0;
pub const OPEN_MAINTENANCE_TAG_V1: u64 = 1;
pub const PERFORM_TAG_V1: u64 = 2;
pub const VISIT_COMMONS_TAG_V1: u64 = 3;
pub const HOLDER_SPONSORSHIP_TAG_V1: u64 = 4;

/// Server-issued, short-lived authority for one exact action at one exact head.
///
/// These bytes are an opaque lookup/verification id, not a client-decoded state
/// or policy object.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GalleyActionToken([u8; 32]);

impl GalleyActionToken {
    pub const fn from_bytes(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    pub const fn to_bytes(self) -> [u8; 32] {
        self.0
    }
}

/// Server-issued reference to a currently active holder admission receipt.
///
/// The node resolves this id during finalized-turn evaluation, checks its
/// wallet/player binding and expiry, and consumes its successor atomically with
/// the Galley event. It intentionally reveals no raw balance or voting weight.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HolderCapabilityReceiptId([u8; 32]);

impl HolderCapabilityReceiptId {
    pub const fn from_bytes(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    pub const fn to_bytes(self) -> [u8; 32] {
        self.0
    }
}

/// Exact public-ballot intent. Player and activated rules are server-derived.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PublicVoteChoice {
    No,
    Yes,
}

impl PublicVoteChoice {
    const fn tag(self) -> u64 {
        match self {
            Self::No => 0,
            Self::Yes => 1,
        }
    }

    fn from_tag(tag: u64) -> Result<Self, GalleyCommandError> {
        match tag {
            0 => Ok(Self::No),
            1 => Ok(Self::Yes),
            _ => Err(GalleyCommandError::MalformedReserved(
                "public vote choice must be exactly zero or one",
            )),
        }
    }
}

/// The complete player-authorable Galley command vocabulary.
///
/// Identity and hidden state authority are deliberately absent. Content and
/// choice ids are exact signed intent; the opaque token constrains them against
/// server/Lean-authored state before execution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GalleyPlayerCommandV1 {
    PublicVote {
        action_token: GalleyActionToken,
        choice: PublicVoteChoice,
    },
    Perform {
        action_token: GalleyActionToken,
        action_content_id: [u8; 32],
    },
    VisitCommons {
        action_token: GalleyActionToken,
        choice_id: [u8; 32],
    },
    HolderSponsorship {
        action_token: GalleyActionToken,
        holder_receipt_id: HolderCapabilityReceiptId,
        beneficiary_player_id: [u8; 32],
    },
}

impl GalleyPlayerCommandV1 {
    pub const fn action_token(self) -> GalleyActionToken {
        match self {
            Self::PublicVote { action_token, .. }
            | Self::Perform { action_token, .. }
            | Self::VisitCommons { action_token, .. }
            | Self::HolderSponsorship { action_token, .. } => action_token,
        }
    }
}

/// Classification result at the reserved Galley ingress seam.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GalleyEventRoute {
    /// The event does not use the reserved Galley topic.
    Ordinary,
    /// An exact player-authorable version-1 Galley command.
    PlayerCommand(GalleyPlayerCommandV1),
}

/// Construction/classification refusal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GalleyCommandError {
    MalformedReserved(&'static str),
    OperatorOnlyOpenMaintenance,
    UnknownReservedTag(u64),
}

impl fmt::Display for GalleyCommandError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MalformedReserved(reason) => {
                write!(f, "reserved Galley command marker is malformed: {reason}")
            }
            Self::OperatorOnlyOpenMaintenance => f.write_str(
                "Galley open-maintenance is operator-only and cannot be player-authored",
            ),
            Self::UnknownReservedTag(tag) => {
                write!(f, "unknown reserved Galley command tag {tag}")
            }
        }
    }
}

impl std::error::Error for GalleyCommandError {}

/// Refusal from the exact one-root/one-event player carrier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GalleyCarrierError {
    InvalidShape(&'static str),
    Command(GalleyCommandError),
}

impl fmt::Display for GalleyCarrierError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidShape(reason) => write!(f, "invalid Galley player carrier: {reason}"),
            Self::Command(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for GalleyCarrierError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidShape(_) => None,
            Self::Command(error) => Some(error),
        }
    }
}

impl From<GalleyCommandError> for GalleyCarrierError {
    fn from(error: GalleyCommandError) -> Self {
        Self::Command(error)
    }
}

/// Construct the exact reserved event for a player intent.
///
/// Scalar lanes are canonical unsigned-64 fields; ids and opaque tokens are
/// exact 32-byte lanes. No variant has a player-id, state-root, sequence,
/// holder balance, weight, or policy lane.
pub fn galley_command_event(command: GalleyPlayerCommandV1) -> Event {
    let data = match command {
        GalleyPlayerCommandV1::PublicVote {
            action_token,
            choice,
        } => vec![
            field_from_u64(PUBLIC_VOTE_TAG_V1),
            action_token.to_bytes(),
            field_from_u64(choice.tag()),
        ],
        GalleyPlayerCommandV1::Perform {
            action_token,
            action_content_id,
        } => vec![
            field_from_u64(PERFORM_TAG_V1),
            action_token.to_bytes(),
            action_content_id,
        ],
        GalleyPlayerCommandV1::VisitCommons {
            action_token,
            choice_id,
        } => vec![
            field_from_u64(VISIT_COMMONS_TAG_V1),
            action_token.to_bytes(),
            choice_id,
        ],
        GalleyPlayerCommandV1::HolderSponsorship {
            action_token,
            holder_receipt_id,
            beneficiary_player_id,
        } => vec![
            field_from_u64(HOLDER_SPONSORSHIP_TAG_V1),
            action_token.to_bytes(),
            holder_receipt_id.to_bytes(),
            beneficiary_player_id,
        ],
    };
    Event::new(symbol(GALLEY_COMMAND_TOPIC_V1), data)
}

/// Derive the player cell from the exact public key used by the signing flow.
///
/// This is the deployed PoA/default-agent derivation, not a new Galley-specific
/// identity domain.
pub fn galley_player_cell(signer_public_key: &[u8; 32]) -> CellId {
    CellId::derive_raw(signer_public_key, blake3::hash(b"default").as_bytes())
}

/// Construct the only player-authored turn shape accepted by this carrier.
///
/// `Unchecked` is the canonical pre-signing scaffold. The fee is precomputed
/// for the hybrid authorization that the signing flow will attach.
pub fn galley_player_command_turn(
    signer_public_key: &[u8; 32],
    nonce: u64,
    previous_receipt_hash: Option<[u8; 32]>,
    command: GalleyPlayerCommandV1,
) -> Turn {
    let agent = galley_player_cell(signer_public_key);
    let action = Action {
        target: agent,
        method: symbol(GALLEY_COMMAND_METHOD_V1),
        args: Vec::new(),
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![Effect::EmitEvent {
            cell: agent,
            event: galley_command_event(command),
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: Vec::new(),
    };
    let mut builder = TurnBuilder::new(agent, nonce);
    if let Some(hash) = previous_receipt_hash {
        builder.set_previous_receipt_hash(hash);
    }
    builder.add_action(action);
    let mut turn = builder.build();
    turn.fee = galley_command_hybrid_fee(&turn);
    turn
}

fn galley_command_hybrid_fee(turn: &Turn) -> u64 {
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

/// Decode an exact Galley player carrier.
///
/// This checks the inner turn's structural carrier shape. Use
/// [`command_from_exact_galley_signed_turn`] at an external signed ingress;
/// action authorization bytes do not identify the player.
pub fn command_from_exact_galley_turn(
    turn: &Turn,
) -> Result<GalleyPlayerCommandV1, GalleyCarrierError> {
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
        return Err(GalleyCarrierError::InvalidShape(
            "unrelated turn metadata or proof material is present",
        ));
    }
    if turn.call_forest.roots.len() != 1 {
        return Err(GalleyCarrierError::InvalidShape(
            "expected exactly one root action",
        ));
    }
    let root = &turn.call_forest.roots[0];
    if !root.children.is_empty() {
        return Err(GalleyCarrierError::InvalidShape(
            "Galley player action cannot have children",
        ));
    }
    let action = &root.action;
    if action.target != turn.agent
        || action.method != symbol(GALLEY_COMMAND_METHOD_V1)
        || !action.args.is_empty()
        || action.preconditions != Preconditions::default()
        || action.may_delegate != DelegationMode::None
        || action.commitment_mode != CommitmentMode::Full
        || action.balance_change.is_some()
        || !action.witness_blobs.is_empty()
    {
        return Err(GalleyCarrierError::InvalidShape(
            "action is not the canonical Galley player action",
        ));
    }
    if !matches!(
        action.authorization,
        Authorization::Unchecked
            | Authorization::Signature(_, _)
            | Authorization::HybridSignature { .. }
    ) {
        return Err(GalleyCarrierError::InvalidShape(
            "unsupported Galley player authorization",
        ));
    }
    if action.effects.len() != 1 {
        return Err(GalleyCarrierError::InvalidShape(
            "expected exactly one Galley event effect",
        ));
    }
    let Effect::EmitEvent { cell, event } = &action.effects[0] else {
        return Err(GalleyCarrierError::InvalidShape(
            "Galley carrier effect is not EmitEvent",
        ));
    };
    if *cell != turn.agent {
        return Err(GalleyCarrierError::InvalidShape(
            "Galley event emitter is not the turn agent",
        ));
    }
    if turn.fee != galley_command_hybrid_fee(turn) {
        return Err(GalleyCarrierError::InvalidShape(
            "fee does not match the canonical hybrid carrier cost",
        ));
    }
    match classify_galley_event(event)? {
        GalleyEventRoute::PlayerCommand(command) => Ok(command),
        GalleyEventRoute::Ordinary => Err(GalleyCarrierError::InvalidShape(
            "event does not use the reserved Galley topic",
        )),
    }
}

/// Decode the exact carrier at a signed ingress and derive player identity only
/// from the verified outer envelope.
///
/// The node still owns PQ-policy enforcement, action-token admission,
/// holder-receipt admission, and atomic event/receipt/token consumption.
pub fn command_from_exact_galley_signed_turn(
    signed: &SignedTurn,
) -> Result<GalleyPlayerCommandV1, GalleyCarrierError> {
    let command = command_from_exact_galley_turn(&signed.turn)?;
    let turn_hash = signed.turn.hash();
    if !signed.signer.verify(&turn_hash, &signed.signature) {
        return Err(GalleyCarrierError::InvalidShape(
            "outer Galley turn signature is invalid",
        ));
    }
    if galley_player_cell(&signed.signer.0) != signed.turn.agent {
        return Err(GalleyCarrierError::InvalidShape(
            "outer signer does not derive the Galley player agent",
        ));
    }
    Ok(command)
}

/// Classify an event while ensuring every malformed reserved marker refuses.
pub fn classify_galley_event(event: &Event) -> Result<GalleyEventRoute, GalleyCommandError> {
    if event.topic != symbol(GALLEY_COMMAND_TOPIC_V1) {
        return Ok(GalleyEventRoute::Ordinary);
    }
    let Some(tag_field) = event.data.first() else {
        return Err(GalleyCommandError::MalformedReserved("missing command tag"));
    };
    let tag = exact_u64_lane(tag_field)?;
    match tag {
        PUBLIC_VOTE_TAG_V1 => {
            require_lane_count(&event.data, 3, "public vote")?;
            let choice = PublicVoteChoice::from_tag(exact_u64_lane(&event.data[2])?)?;
            Ok(GalleyEventRoute::PlayerCommand(
                GalleyPlayerCommandV1::PublicVote {
                    action_token: GalleyActionToken::from_bytes(event.data[1]),
                    choice,
                },
            ))
        }
        OPEN_MAINTENANCE_TAG_V1 => Err(GalleyCommandError::OperatorOnlyOpenMaintenance),
        PERFORM_TAG_V1 => {
            require_lane_count(&event.data, 3, "perform")?;
            Ok(GalleyEventRoute::PlayerCommand(
                GalleyPlayerCommandV1::Perform {
                    action_token: GalleyActionToken::from_bytes(event.data[1]),
                    action_content_id: event.data[2],
                },
            ))
        }
        VISIT_COMMONS_TAG_V1 => {
            require_lane_count(&event.data, 3, "visit commons")?;
            Ok(GalleyEventRoute::PlayerCommand(
                GalleyPlayerCommandV1::VisitCommons {
                    action_token: GalleyActionToken::from_bytes(event.data[1]),
                    choice_id: event.data[2],
                },
            ))
        }
        HOLDER_SPONSORSHIP_TAG_V1 => {
            require_lane_count(&event.data, 4, "holder sponsorship")?;
            Ok(GalleyEventRoute::PlayerCommand(
                GalleyPlayerCommandV1::HolderSponsorship {
                    action_token: GalleyActionToken::from_bytes(event.data[1]),
                    holder_receipt_id: HolderCapabilityReceiptId::from_bytes(event.data[2]),
                    beneficiary_player_id: event.data[3],
                },
            ))
        }
        other => Err(GalleyCommandError::UnknownReservedTag(other)),
    }
}

fn require_lane_count(
    data: &[FieldElement],
    expected: usize,
    command: &'static str,
) -> Result<(), GalleyCommandError> {
    if data.len() == expected {
        Ok(())
    } else {
        Err(GalleyCommandError::MalformedReserved(match command {
            "public vote" => "public vote requires exactly three lanes",
            "perform" => "perform requires exactly three lanes",
            "visit commons" => "visit commons requires exactly three lanes",
            "holder sponsorship" => "holder sponsorship requires exactly four lanes",
            _ => "command has the wrong lane count",
        }))
    }
}

fn exact_u64_lane(field: &FieldElement) -> Result<u64, GalleyCommandError> {
    let value = field_to_u64(field);
    if *field != field_from_u64(value) {
        return Err(GalleyCommandError::MalformedReserved(
            "scalar field is not a canonical unsigned-64 lane",
        ));
    }
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_types::{Signature, SigningKey, sign};

    const SIGNER: [u8; 32] = [0x51; 32];

    fn action_token() -> GalleyActionToken {
        GalleyActionToken::from_bytes([0xA1; 32])
    }

    fn holder_receipt_id() -> HolderCapabilityReceiptId {
        HolderCapabilityReceiptId::from_bytes([0xB2; 32])
    }

    fn commands() -> [GalleyPlayerCommandV1; 4] {
        [
            GalleyPlayerCommandV1::PublicVote {
                action_token: action_token(),
                choice: PublicVoteChoice::Yes,
            },
            GalleyPlayerCommandV1::Perform {
                action_token: action_token(),
                action_content_id: [0xC3; 32],
            },
            GalleyPlayerCommandV1::VisitCommons {
                action_token: action_token(),
                choice_id: [0xD4; 32],
            },
            GalleyPlayerCommandV1::HolderSponsorship {
                action_token: action_token(),
                holder_receipt_id: holder_receipt_id(),
                beneficiary_player_id: [0xE5; 32],
            },
        ]
    }

    #[test]
    fn constructors_and_classifier_are_exact_inverses() {
        for command in commands() {
            let event = galley_command_event(command);
            assert_eq!(event.topic, symbol(GALLEY_COMMAND_TOPIC_V1));
            assert_eq!(
                classify_galley_event(&event),
                Ok(GalleyEventRoute::PlayerCommand(command))
            );
        }
    }

    #[test]
    fn public_intents_have_no_player_or_hidden_state_lanes() {
        let [vote, perform, visit, sponsor] = commands();
        assert_eq!(galley_command_event(vote).data.len(), 3);
        assert_eq!(galley_command_event(perform).data.len(), 3);
        assert_eq!(galley_command_event(visit).data.len(), 3);
        assert_eq!(galley_command_event(sponsor).data.len(), 4);
        assert_eq!(galley_command_event(sponsor).data[2], [0xB2; 32]);
        assert_eq!(galley_command_event(sponsor).data[3], [0xE5; 32]);
    }

    #[test]
    fn ordinary_event_is_not_captured() {
        let event = Event::new(symbol("ordinary"), vec![field_from_u64(0)]);
        assert_eq!(
            classify_galley_event(&event),
            Ok(GalleyEventRoute::Ordinary)
        );
    }

    #[test]
    fn reserved_marker_failures_refuse_instead_of_falling_through() {
        let reserved = symbol(GALLEY_COMMAND_TOPIC_V1);
        assert!(matches!(
            classify_galley_event(&Event::new(reserved, vec![])),
            Err(GalleyCommandError::MalformedReserved(_))
        ));
        assert_eq!(
            classify_galley_event(&Event::new(
                reserved,
                vec![field_from_u64(OPEN_MAINTENANCE_TAG_V1)]
            )),
            Err(GalleyCommandError::OperatorOnlyOpenMaintenance)
        );
        assert_eq!(
            classify_galley_event(&Event::new(reserved, vec![field_from_u64(99)])),
            Err(GalleyCommandError::UnknownReservedTag(99))
        );
    }

    #[test]
    fn noncanonical_scalars_and_wrong_lane_counts_refuse() {
        let mut noncanonical_tag = galley_command_event(commands()[0]);
        noncanonical_tag.data[0][8] = 1;
        assert!(matches!(
            classify_galley_event(&noncanonical_tag),
            Err(GalleyCommandError::MalformedReserved(_))
        ));

        let mut bad_choice = galley_command_event(commands()[0]);
        bad_choice.data[2] = field_from_u64(2);
        assert!(matches!(
            classify_galley_event(&bad_choice),
            Err(GalleyCommandError::MalformedReserved(_))
        ));

        let mut two_receipts = galley_command_event(commands()[3]);
        two_receipts.data.push([0xB3; 32]);
        assert!(matches!(
            classify_galley_event(&two_receipts),
            Err(GalleyCommandError::MalformedReserved(_))
        ));
    }

    #[test]
    fn exact_carrier_roundtrips_every_command() {
        for command in commands() {
            let turn = galley_player_command_turn(&SIGNER, 9, Some([0x77; 32]), command);
            assert_eq!(turn.agent, galley_player_cell(&SIGNER));
            assert_eq!(turn.nonce, 9);
            assert_eq!(turn.previous_receipt_hash, Some([0x77; 32]));
            assert_eq!(turn.call_forest.action_count(), 1);
            assert_eq!(command_from_exact_galley_turn(&turn), Ok(command));
        }
    }

    #[test]
    fn carrier_refuses_piggyback_shape_and_metadata() {
        let command = commands()[2];
        let mut extra_effect = galley_player_command_turn(&SIGNER, 0, None, command);
        extra_effect.call_forest.roots[0]
            .action
            .effects
            .push(Effect::IncrementNonce {
                cell: extra_effect.agent,
            });
        assert!(matches!(
            command_from_exact_galley_turn(&extra_effect),
            Err(GalleyCarrierError::InvalidShape(
                "expected exactly one Galley event effect"
            ))
        ));

        let mut extra_root = galley_player_command_turn(&SIGNER, 0, None, command);
        let duplicate = extra_root.call_forest.roots[0].clone();
        extra_root.call_forest.roots.push(duplicate);
        assert!(matches!(
            command_from_exact_galley_turn(&extra_root),
            Err(GalleyCarrierError::InvalidShape(
                "expected exactly one root action"
            ))
        ));

        let mut memo = galley_player_command_turn(&SIGNER, 0, None, command);
        memo.memo = Some("caller-authored state authority".into());
        assert!(matches!(
            command_from_exact_galley_turn(&memo),
            Err(GalleyCarrierError::InvalidShape(_))
        ));
    }

    #[test]
    fn carrier_refuses_emitter_substitution() {
        let command = commands()[0];
        let mut wrong_emitter = galley_player_command_turn(&SIGNER, 0, None, command);
        let other = galley_player_cell(&[0x98; 32]);
        let Effect::EmitEvent { cell, .. } =
            &mut wrong_emitter.call_forest.roots[0].action.effects[0]
        else {
            panic!("fixture is EmitEvent")
        };
        *cell = other;
        assert!(matches!(
            command_from_exact_galley_turn(&wrong_emitter),
            Err(GalleyCarrierError::InvalidShape(
                "Galley event emitter is not the turn agent"
            ))
        ));
    }

    #[test]
    fn signed_envelope_is_the_only_player_identity_source() {
        let command = commands()[0];
        let signing_key = SigningKey::from_bytes(&[0x71; 32]);
        let signer = signing_key.public_key();
        let turn = galley_player_command_turn(&signer.0, 4, None, command);
        let signature = sign(&signing_key, &turn.hash());
        let signed = SignedTurn {
            turn,
            signature,
            signer,
            pq_signature: vec![],
            pq_signer: vec![],
        };
        assert_eq!(command_from_exact_galley_signed_turn(&signed), Ok(command));

        let wrong_turn = galley_player_command_turn(&[0x72; 32], 4, None, command);
        let wrong = SignedTurn {
            signature: sign(&signing_key, &wrong_turn.hash()),
            turn: wrong_turn,
            signer,
            pq_signature: vec![],
            pq_signer: vec![],
        };
        assert!(matches!(
            command_from_exact_galley_signed_turn(&wrong),
            Err(GalleyCarrierError::InvalidShape(
                "outer signer does not derive the Galley player agent"
            ))
        ));

        let mut invalid_signature = signed;
        invalid_signature.signature = Signature([0; 64]);
        assert!(matches!(
            command_from_exact_galley_signed_turn(&invalid_signature),
            Err(GalleyCarrierError::InvalidShape(
                "outer Galley turn signature is invalid"
            ))
        ));
    }

    #[test]
    fn action_authorization_bytes_are_not_an_identity_source() {
        let command = commands()[1];
        let mut classical = galley_player_command_turn(&SIGNER, 3, None, command);
        classical.call_forest.roots[0].action.authorization =
            Authorization::Signature([0x99; 32], [0x44; 32]);
        assert_eq!(command_from_exact_galley_turn(&classical), Ok(command));

        let mut hybrid = galley_player_command_turn(&SIGNER, 3, None, command);
        hybrid.call_forest.roots[0].action.authorization = Authorization::HybridSignature {
            ed25519: [0x11; 64],
            ml_dsa: vec![0x22; 8],
            ml_dsa_pk: vec![0x33; 8],
        };
        assert_eq!(command_from_exact_galley_turn(&hybrid), Ok(command));
        assert_eq!(
            hybrid.fee,
            TurnExecutor::new(ComputronCosts::default()).estimate_cost(&hybrid)
        );
    }

    #[test]
    fn operator_open_maintenance_cannot_hide_in_carrier() {
        let mut turn = galley_player_command_turn(&SIGNER, 0, None, commands()[0]);
        let Effect::EmitEvent { event, .. } = &mut turn.call_forest.roots[0].action.effects[0]
        else {
            panic!("fixture is EmitEvent")
        };
        *event = Event::new(
            symbol(GALLEY_COMMAND_TOPIC_V1),
            vec![field_from_u64(OPEN_MAINTENANCE_TAG_V1)],
        );
        turn.fee = galley_command_hybrid_fee(&turn);
        assert_eq!(
            command_from_exact_galley_turn(&turn),
            Err(GalleyCarrierError::Command(
                GalleyCommandError::OperatorOnlyOpenMaintenance
            ))
        );
    }
}
