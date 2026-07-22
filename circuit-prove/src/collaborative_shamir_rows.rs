//! Witness-owner Shamir rows for the Dregg-native collaborative BaseFold seam.
//!
//! This module closes one specific privacy gap in [`crate::collaborative_basefold`]:
//! independent witness owners turn disjoint coefficient blocks into receiver-local
//! party rows. Assuming each owner assignment is instantiated in a distinct custody
//! domain, no production API constructs the complete witness. Rust labels cannot
//! enforce process isolation; the session does enforce at least two non-empty,
//! disjoint owner assignments so no accepted block spans the whole witness.
//!
//! For each owned coefficient `s`, an owner samples
//! `p(X) = s + r_1 X + ... + r_t X^t` and sends only `p(x_i)` to prover `i`.
//! Prover `i` consumes the exact, canonically ordered set of messages addressed to
//! it and assembles a [`SessionPartyShareInput`] locally. The Shamir points are the same
//! non-zero two-adic row domain used by the collaborative tensor encoder. Each
//! receiver locally encodes, blinds, commits, and folds its own row through the
//! bound handoff in this module; the coordinator receives only commitments.
//!
//! # Security boundary
//!
//! This is an independently written CPU reference inspired by the collaborative
//! tensor-code construction of ePrint 2026/729. It supplies randomized Shamir
//! observations, not the deterministic support rows produced by
//! `column_encode_party_shares`. At most `t` observations have standard
//! information-theoretic Shamir privacy when owner randomness is uniform and
//! secret. Tests provide algebraic, exhaustive-small-field, differential, and
//! statistical implementation evidence; this file is not a complete ZK theorem.
//!
//! The BLAKE3 values below identify the typed public session and frozen deal set;
//! they are **not sender authentication or polynomial commitments**. Fresh deal
//! IDs prevent honest typed-path replay/mixing, but do not prove that a malicious
//! owner sent evaluations of one polynomial. [`OwnerShareMessage::seal`] and
//! [`SealedOwnerShareMessage::open`] provide a receiver- and round-bound
//! ChaCha20-Poly1305 wire codec for external transports; key establishment and
//! replay storage remain deployment obligations. Production also still requires
//! roster admission, reliable broadcast where required, and
//! a malicious-secure consistency compiler/PCS. There is no dropout recovery,
//! complaint protocol, MMCS opening proof, Fiat--Shamir theorem, or proof of
//! honest owner input formation. The blinded row commitments and exact manifest
//! below are a binding fold handoff, not a complete MMCS.
//!
//! Witness coefficients, random polynomial coefficients, and sparse payloads are
//! retained as canonical `u32` values in `Zeroizing` buffers through local encoding
//! and folding. Field arithmetic necessarily creates short-lived register copies;
//! those are an explicit memory-hygiene boundary, not a claim that every
//! compiler-generated copy is wiped.

use core::fmt;

use chacha20poly1305::{
    ChaCha20Poly1305, KeyInit,
    aead::{Aead, Payload},
};
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32, PrimeField64, TwoAdicField};
use rand::CryptoRng;
use zeroize::Zeroizing;

use crate::collaborative_basefold::{PartyIndex, TensorCodeShape};

/// Domain separator for a complete sharing-session context.
pub const SHAMIR_SESSION_DOMAIN_V1: &[u8] = b"dregg.native.collaborative-shamir.session.v1\0";

/// Domain separator for the common, exact owner-deal set of one round.
pub const SHAMIR_FROZEN_ROUND_DOMAIN_V1: &[u8] =
    b"dregg.native.collaborative-shamir.frozen-round.v1\0";

/// Domain separator for receiver-bound encrypted share messages.
pub const SHAMIR_SEALED_SHARE_DOMAIN_V1: &[u8] =
    b"dregg.native.collaborative-shamir.sealed-share.v1\0";

/// Domain separator for blinded, receiver-local row commitments.
pub const SHAMIR_ROW_COMMITMENT_DOMAIN_V1: &[u8] =
    b"dregg.native.collaborative-shamir.row-commitment.v1\0";

/// Domain separator for an exact all-receiver commitment manifest.
pub const SHAMIR_COMMITMENT_MANIFEST_DOMAIN_V1: &[u8] =
    b"dregg.native.collaborative-shamir.commitment-manifest.v1\0";

/// Domain separator for bound fold challenges.
pub const SHAMIR_FOLD_TRANSCRIPT_DOMAIN_V1: &[u8] =
    b"dregg.native.collaborative-shamir.fold-transcript.v1\0";

const SEALED_SHARE_WIRE_MAGIC_V1: &[u8; 8] = b"DGRSHR01";
const ANNOUNCEMENT_WIRE_MAGIC_V1: &[u8; 8] = b"DGRANN01";
const SEALED_SHARE_NONCE_BYTES: usize = 12;
const SEALED_SHARE_TAG_BYTES: usize = 16;
/// Absolute parser/decrypt allocation ceiling for one sealed sparse owner share.
pub const MAX_SEALED_SHARE_CIPHERTEXT_BYTES: usize = 1024 * 1024;
const MINIMUM_OWNER_CUSTODY_DOMAINS: usize = 2;

/// One-time sharing-round identity.
///
/// The protocol allocates a fresh value for every dealing attempt. This module
/// binds it everywhere but cannot durably enforce global uniqueness; replay
/// tracking belongs to the transport/session authority.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SharingEpoch([u8; 32]);

impl SharingEpoch {
    pub const fn new(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    pub const fn as_bytes(self) -> [u8; 32] {
        self.0
    }
}

/// Canonical Lean-authored relation identity selected for this sharing round.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SharingRelationId([u8; 32]);

impl SharingRelationId {
    pub const fn new(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    pub const fn as_bytes(self) -> [u8; 32] {
        self.0
    }
}

/// Unpredictable one-shot identifier for one owner's prepared polynomial set.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OwnerDealId([u8; 32]);

impl OwnerDealId {
    pub const fn as_bytes(self) -> [u8; 32] {
        self.0
    }
}

/// Stable, protocol-level witness-owner label.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OwnerLabel([u8; 32]);

impl OwnerLabel {
    /// Construct a label from the roster's canonical identity digest.
    pub const fn new(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    /// Canonical label bytes.
    pub const fn as_bytes(self) -> [u8; 32] {
        self.0
    }
}

/// Stable, protocol-level prover label.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProverLabel([u8; 32]);

impl ProverLabel {
    /// Construct a label from the roster's canonical identity digest.
    pub const fn new(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    /// Canonical label bytes.
    pub const fn as_bytes(self) -> [u8; 32] {
        self.0
    }
}

/// Strong global coefficient-column position.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CoefficientPosition(usize);

impl CoefficientPosition {
    /// Construct a global coefficient position.
    pub const fn new(position: usize) -> Self {
        Self(position)
    }

    /// Canonical zero-based position.
    pub const fn get(self) -> usize {
        self.0
    }
}

/// One roster member's exact, public coefficient-position assignment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OwnerAssignment {
    owner: OwnerLabel,
    positions: Vec<CoefficientPosition>,
}

impl OwnerAssignment {
    /// Declare an owner's positions. Session construction validates that all
    /// assignments are non-empty, sorted, unique, and jointly exhaustive.
    pub fn new(owner: OwnerLabel, positions: Vec<CoefficientPosition>) -> Self {
        Self { owner, positions }
    }

    /// Owner label.
    pub const fn owner(&self) -> OwnerLabel {
        self.owner
    }

    /// Canonically ordered global coefficient positions.
    pub fn positions(&self) -> &[CoefficientPosition] {
        &self.positions
    }
}

/// Fail-closed sharing/session errors.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CollaborativeShamirError {
    ZeroPrivacyThreshold,
    ThresholdNotBelowProverCount {
        threshold: usize,
        prover_count: usize,
    },
    SharingRowMismatch {
        expected: usize,
        actual: usize,
    },
    WrongProverCount {
        expected: usize,
        actual: usize,
    },
    InsufficientOwnerCustodyDomains {
        minimum: usize,
        actual: usize,
    },
    EmptyOwnerAssignment {
        owner_index: usize,
    },
    DuplicateOwnerLabel {
        first: usize,
        second: usize,
    },
    DuplicateProverLabel {
        first: usize,
        second: usize,
    },
    PositionOutOfRange {
        owner_index: usize,
        position: usize,
        coefficient_count: usize,
    },
    NonCanonicalOwnerPositions {
        owner_index: usize,
        previous: usize,
        actual: usize,
    },
    DuplicateCoefficientPosition {
        position: usize,
        first_owner: usize,
        second_owner: usize,
    },
    MissingCoefficientPosition {
        position: usize,
    },
    UnknownOwner,
    OwnerBlockPositionsMismatch {
        owner_index: usize,
    },
    OwnerBlockWidthMismatch {
        owner_index: usize,
        expected: usize,
        actual: usize,
    },
    NonCanonicalSecretCoefficient {
        owner_position: usize,
        value: u32,
    },
    WrongAnnouncementCount {
        expected: usize,
        actual: usize,
    },
    AnnouncementOwnerOutOfRange {
        owner_index: usize,
        owner_count: usize,
    },
    DuplicateOwnerAnnouncement {
        owner_index: usize,
    },
    ReorderedOwnerAnnouncement {
        position: usize,
        expected_owner: usize,
        actual_owner: usize,
    },
    AnnouncementSessionMismatch {
        owner_index: usize,
    },
    AnnouncementOwnerLabelMismatch {
        owner_index: usize,
    },
    PreparedDealRoundMismatch {
        owner_index: usize,
    },
    TransportRejected {
        receiver: usize,
    },
    ReceiverOutOfRange {
        receiver: usize,
        prover_count: usize,
    },
    WrongMessageCount {
        expected: usize,
        actual: usize,
    },
    MessageOwnerOutOfRange {
        owner_index: usize,
        owner_count: usize,
    },
    DuplicateOwnerMessage {
        owner_index: usize,
    },
    ReorderedOwnerMessage {
        position: usize,
        expected_owner: usize,
        actual_owner: usize,
    },
    SessionBindingMismatch {
        owner_index: usize,
    },
    OwnerLabelMismatch {
        owner_index: usize,
    },
    MessageDealIdMismatch {
        owner_index: usize,
    },
    ReceiverSubstitution {
        owner_index: usize,
        expected_receiver: usize,
        actual_receiver: usize,
    },
    ReceiverLabelMismatch {
        owner_index: usize,
    },
    MessagePositionsMismatch {
        owner_index: usize,
    },
    MessageWidthMismatch {
        owner_index: usize,
        expected: usize,
        actual: usize,
    },
    BoundRowContextMismatch,
    BoundRowShapeMismatch,
    BoundRowReceiverMismatch,
    MalformedAnnouncement,
    MalformedSealedShare,
    SealedShareContextMismatch,
    SealedShareReceiverMismatch,
    SealedShareAuthenticationFailed,
    WrongCommitmentCount {
        expected: usize,
        actual: usize,
    },
    ReorderedCommitment {
        position: usize,
        actual_receiver: usize,
    },
    CommitmentContextMismatch {
        receiver: usize,
    },
    CommitmentDigestMismatch {
        receiver: usize,
    },
    FoldTranscriptMismatch,
    FinalBoundRowCannotFold,
}

impl fmt::Display for CollaborativeShamirError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroPrivacyThreshold => {
                f.write_str("collaborative Shamir privacy threshold must be non-zero")
            }
            Self::ThresholdNotBelowProverCount {
                threshold,
                prover_count,
            } => write!(
                f,
                "Shamir threshold {threshold} must be below prover count {prover_count}"
            ),
            Self::SharingRowMismatch { expected, actual } => write!(
                f,
                "tensor has {actual} sharing rows, expected secret plus masks = {expected}"
            ),
            Self::WrongProverCount { expected, actual } => write!(
                f,
                "prover roster has {actual} labels, expected {expected} tensor rows"
            ),
            Self::InsufficientOwnerCustodyDomains { minimum, actual } => write!(
                f,
                "collaborative witness custody requires at least {minimum} distinct owners, received {actual}"
            ),
            Self::EmptyOwnerAssignment { owner_index } => {
                write!(f, "owner {owner_index} has an empty coefficient assignment")
            }
            Self::DuplicateOwnerLabel { first, second } => write!(
                f,
                "owner labels at roster positions {first} and {second} are identical"
            ),
            Self::DuplicateProverLabel { first, second } => write!(
                f,
                "prover labels at roster positions {first} and {second} are identical"
            ),
            Self::PositionOutOfRange {
                owner_index,
                position,
                coefficient_count,
            } => write!(
                f,
                "owner {owner_index} position {position} is outside 0..{coefficient_count}"
            ),
            Self::NonCanonicalOwnerPositions {
                owner_index,
                previous,
                actual,
            } => write!(
                f,
                "owner {owner_index} positions are not increasing: {previous} then {actual}"
            ),
            Self::DuplicateCoefficientPosition {
                position,
                first_owner,
                second_owner,
            } => write!(
                f,
                "coefficient {position} is assigned to owners {first_owner} and {second_owner}"
            ),
            Self::MissingCoefficientPosition { position } => {
                write!(f, "coefficient {position} has no witness owner")
            }
            Self::UnknownOwner => f.write_str("private witness block owner is not in the session"),
            Self::OwnerBlockPositionsMismatch { owner_index } => write!(
                f,
                "private block positions do not match owner {owner_index}'s public assignment"
            ),
            Self::OwnerBlockWidthMismatch {
                owner_index,
                expected,
                actual,
            } => write!(
                f,
                "owner {owner_index} block has {actual} coefficients, expected {expected}"
            ),
            Self::NonCanonicalSecretCoefficient {
                owner_position,
                value,
            } => write!(
                f,
                "private coefficient {owner_position} has non-canonical BabyBear word {value}"
            ),
            Self::WrongAnnouncementCount { expected, actual } => write!(
                f,
                "round has {actual} owner-deal announcements, expected exact set of {expected}"
            ),
            Self::AnnouncementOwnerOutOfRange {
                owner_index,
                owner_count,
            } => write!(
                f,
                "deal announcement owner {owner_index} is outside 0..{owner_count}"
            ),
            Self::DuplicateOwnerAnnouncement { owner_index } => {
                write!(
                    f,
                    "owner {owner_index} supplied more than one deal announcement"
                )
            }
            Self::ReorderedOwnerAnnouncement {
                position,
                expected_owner,
                actual_owner,
            } => write!(
                f,
                "deal announcement position {position} carries owner {actual_owner}, expected {expected_owner}"
            ),
            Self::AnnouncementSessionMismatch { owner_index } => write!(
                f,
                "owner {owner_index} deal announcement belongs to another session"
            ),
            Self::AnnouncementOwnerLabelMismatch { owner_index } => write!(
                f,
                "owner {owner_index} deal announcement carries the wrong label"
            ),
            Self::PreparedDealRoundMismatch { owner_index } => write!(
                f,
                "prepared deal for owner {owner_index} is not selected by the frozen round"
            ),
            Self::TransportRejected { receiver } => {
                write!(
                    f,
                    "confidential receiver transport rejected receiver {receiver}"
                )
            }
            Self::ReceiverOutOfRange {
                receiver,
                prover_count,
            } => {
                write!(f, "receiver {receiver} is outside 0..{prover_count}")
            }
            Self::WrongMessageCount { expected, actual } => write!(
                f,
                "receiver got {actual} owner messages, expected exact set of {expected}"
            ),
            Self::MessageOwnerOutOfRange {
                owner_index,
                owner_count,
            } => {
                write!(f, "message owner {owner_index} is outside 0..{owner_count}")
            }
            Self::DuplicateOwnerMessage { owner_index } => {
                write!(f, "owner {owner_index} supplied more than one message")
            }
            Self::ReorderedOwnerMessage {
                position,
                expected_owner,
                actual_owner,
            } => write!(
                f,
                "message position {position} carries owner {actual_owner}, expected {expected_owner}"
            ),
            Self::SessionBindingMismatch { owner_index } => {
                write!(
                    f,
                    "owner {owner_index} message belongs to another sharing session"
                )
            }
            Self::OwnerLabelMismatch { owner_index } => {
                write!(
                    f,
                    "owner {owner_index} message carries the wrong owner label"
                )
            }
            Self::MessageDealIdMismatch { owner_index } => write!(
                f,
                "owner {owner_index} message belongs to another prepared deal"
            ),
            Self::ReceiverSubstitution {
                owner_index,
                expected_receiver,
                actual_receiver,
            } => write!(
                f,
                "owner {owner_index} message targets receiver {actual_receiver}, expected {expected_receiver}"
            ),
            Self::ReceiverLabelMismatch { owner_index } => {
                write!(
                    f,
                    "owner {owner_index} message carries the wrong receiver label"
                )
            }
            Self::MessagePositionsMismatch { owner_index } => write!(
                f,
                "owner {owner_index} message positions differ from the session assignment"
            ),
            Self::MessageWidthMismatch {
                owner_index,
                expected,
                actual,
            } => write!(
                f,
                "owner {owner_index} message carries {actual} shares, expected {expected}"
            ),
            Self::BoundRowContextMismatch => {
                f.write_str("receiver row belongs to another sharing epoch/relation/roster")
            }
            Self::BoundRowShapeMismatch => {
                f.write_str("receiver row tensor geometry differs from the sharing session")
            }
            Self::BoundRowReceiverMismatch => {
                f.write_str("receiver row identity differs from the sharing session roster")
            }
            Self::MalformedAnnouncement => {
                f.write_str("owner-deal announcement wire image is malformed or non-canonical")
            }
            Self::MalformedSealedShare => {
                f.write_str("sealed owner-share wire image is malformed or non-canonical")
            }
            Self::SealedShareContextMismatch => {
                f.write_str("sealed owner share belongs to another frozen sharing round")
            }
            Self::SealedShareReceiverMismatch => {
                f.write_str("sealed owner share targets another receiver")
            }
            Self::SealedShareAuthenticationFailed => {
                f.write_str("sealed owner-share authentication failed")
            }
            Self::WrongCommitmentCount { expected, actual } => write!(
                f,
                "commitment manifest has {actual} receiver commitments, expected {expected}"
            ),
            Self::ReorderedCommitment {
                position,
                actual_receiver,
            } => write!(
                f,
                "commitment position {position} carries receiver {actual_receiver}"
            ),
            Self::CommitmentContextMismatch { receiver } => write!(
                f,
                "receiver {receiver} commitment belongs to another round, relation, roster, shape, or fold round"
            ),
            Self::CommitmentDigestMismatch { receiver } => write!(
                f,
                "receiver {receiver} local row does not match the published commitment manifest"
            ),
            Self::FoldTranscriptMismatch => {
                f.write_str("fold challenge is not bound to this exact Shamir commitment manifest")
            }
            Self::FinalBoundRowCannotFold => {
                f.write_str("a one-column bound Shamir row cannot be folded further")
            }
        }
    }
}

impl std::error::Error for CollaborativeShamirError {}

/// Immutable public context for one witness-sharing round.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ShamirSharingSession {
    epoch: SharingEpoch,
    relation_id: SharingRelationId,
    shape: TensorCodeShape,
    privacy_threshold: usize,
    owners: Vec<OwnerAssignment>,
    provers: Vec<ProverLabel>,
    context_binding: [u8; 32],
}

impl ShamirSharingSession {
    /// Validate and bind session, relation, threshold, tensor geometry, exact
    /// rosters, and the complete coefficient-position partition.
    pub fn new(
        epoch: SharingEpoch,
        relation_id: SharingRelationId,
        shape: TensorCodeShape,
        privacy_threshold: usize,
        owners: Vec<OwnerAssignment>,
        provers: Vec<ProverLabel>,
    ) -> Result<Self, CollaborativeShamirError> {
        if privacy_threshold == 0 {
            return Err(CollaborativeShamirError::ZeroPrivacyThreshold);
        }
        if privacy_threshold >= shape.party_count() {
            return Err(CollaborativeShamirError::ThresholdNotBelowProverCount {
                threshold: privacy_threshold,
                prover_count: shape.party_count(),
            });
        }
        let expected_rows = privacy_threshold + 1;
        if shape.message_rows() != expected_rows {
            return Err(CollaborativeShamirError::SharingRowMismatch {
                expected: expected_rows,
                actual: shape.message_rows(),
            });
        }
        if provers.len() != shape.party_count() {
            return Err(CollaborativeShamirError::WrongProverCount {
                expected: shape.party_count(),
                actual: provers.len(),
            });
        }
        if owners.len() < MINIMUM_OWNER_CUSTODY_DOMAINS {
            return Err(CollaborativeShamirError::InsufficientOwnerCustodyDomains {
                minimum: MINIMUM_OWNER_CUSTODY_DOMAINS,
                actual: owners.len(),
            });
        }
        for second in 0..owners.len() {
            if let Some(first) = owners[..second]
                .iter()
                .position(|assignment| assignment.owner == owners[second].owner)
            {
                return Err(CollaborativeShamirError::DuplicateOwnerLabel { first, second });
            }
        }
        for second in 0..provers.len() {
            if let Some(first) = provers[..second]
                .iter()
                .position(|label| *label == provers[second])
            {
                return Err(CollaborativeShamirError::DuplicateProverLabel { first, second });
            }
        }

        let coefficient_count = shape.message_columns();
        let mut position_owner = vec![None; coefficient_count];
        for (owner_index, assignment) in owners.iter().enumerate() {
            if assignment.positions.is_empty() {
                return Err(CollaborativeShamirError::EmptyOwnerAssignment { owner_index });
            }
            for pair in assignment.positions.windows(2) {
                if pair[0].get() >= pair[1].get() {
                    return Err(CollaborativeShamirError::NonCanonicalOwnerPositions {
                        owner_index,
                        previous: pair[0].get(),
                        actual: pair[1].get(),
                    });
                }
            }
            for position in &assignment.positions {
                let position = position.get();
                if position >= coefficient_count {
                    return Err(CollaborativeShamirError::PositionOutOfRange {
                        owner_index,
                        position,
                        coefficient_count,
                    });
                }
                if let Some(first_owner) = position_owner[position].replace(owner_index) {
                    return Err(CollaborativeShamirError::DuplicateCoefficientPosition {
                        position,
                        first_owner,
                        second_owner: owner_index,
                    });
                }
            }
        }
        if let Some(position) = position_owner.iter().position(Option::is_none) {
            return Err(CollaborativeShamirError::MissingCoefficientPosition { position });
        }

        let context_binding = hash_session_context(
            epoch,
            relation_id,
            shape,
            privacy_threshold,
            &owners,
            &provers,
        );
        Ok(Self {
            epoch,
            relation_id,
            shape,
            privacy_threshold,
            owners,
            provers,
            context_binding,
        })
    }

    /// One-time dealing epoch. Protocol callers must never reuse it.
    pub const fn epoch(&self) -> SharingEpoch {
        self.epoch
    }

    pub const fn relation_id(&self) -> SharingRelationId {
        self.relation_id
    }

    pub const fn shape(&self) -> TensorCodeShape {
        self.shape
    }

    /// Shamir polynomial degree and maximum private observed-share count.
    pub const fn privacy_threshold(&self) -> usize {
        self.privacy_threshold
    }

    pub fn owners(&self) -> &[OwnerAssignment] {
        &self.owners
    }

    pub fn provers(&self) -> &[ProverLabel] {
        &self.provers
    }

    /// Digest of every public session parameter; not a signature.
    pub const fn context_binding(&self) -> [u8; 32] {
        self.context_binding
    }
}

/// Public one-shot selection ID for one owner's prepared polynomial set.
///
/// This announcement prevents replay across frozen rounds. It is not a
/// cryptographic commitment to the polynomial coefficients.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OwnerDealAnnouncement {
    session_binding: [u8; 32],
    owner_index: usize,
    owner_label: OwnerLabel,
    deal_id: OwnerDealId,
}

impl OwnerDealAnnouncement {
    pub const fn owner_index(self) -> usize {
        self.owner_index
    }

    pub const fn owner_label(self) -> OwnerLabel {
        self.owner_label
    }

    pub const fn deal_id(self) -> OwnerDealId {
        self.deal_id
    }

    /// Canonical public wire image for authenticated broadcast transports.
    ///
    /// The announcement is public and this encoding is not a signature. The
    /// surrounding roster/broadcast layer authenticates the sender; `FrozenShamirRound`
    /// then checks the exact session, label, ordering, and one-shot deal ID.
    pub fn to_wire_bytes(self) -> Vec<u8> {
        let mut out = Vec::with_capacity(112);
        out.extend_from_slice(ANNOUNCEMENT_WIRE_MAGIC_V1);
        out.extend_from_slice(&self.session_binding);
        out.extend_from_slice(&(self.owner_index as u64).to_le_bytes());
        out.extend_from_slice(&self.owner_label.0);
        out.extend_from_slice(&self.deal_id.0);
        out
    }

    /// Decode one exact canonical public announcement wire image.
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, CollaborativeShamirError> {
        if bytes.len() != 112 || &bytes[..8] != ANNOUNCEMENT_WIRE_MAGIC_V1 {
            return Err(CollaborativeShamirError::MalformedAnnouncement);
        }
        let session_binding = bytes[8..40]
            .try_into()
            .map_err(|_| CollaborativeShamirError::MalformedAnnouncement)?;
        let owner_u64 = u64::from_le_bytes(
            bytes[40..48]
                .try_into()
                .map_err(|_| CollaborativeShamirError::MalformedAnnouncement)?,
        );
        let owner_index = usize::try_from(owner_u64)
            .map_err(|_| CollaborativeShamirError::MalformedAnnouncement)?;
        let owner_label = OwnerLabel(
            bytes[48..80]
                .try_into()
                .map_err(|_| CollaborativeShamirError::MalformedAnnouncement)?,
        );
        let deal_id = OwnerDealId(
            bytes[80..112]
                .try_into()
                .map_err(|_| CollaborativeShamirError::MalformedAnnouncement)?,
        );
        Ok(Self {
            session_binding,
            owner_index,
            owner_label,
            deal_id,
        })
    }
}

/// Exact common owner-deal set selected before any receiver accepts shares.
///
/// Freezing is the replay/mixing boundary: every receiver validates the same
/// ordered deal IDs, and a prepared owner deal is consumed exactly once when it
/// delivers its messages.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FrozenShamirRound {
    session: ShamirSharingSession,
    deal_ids: Vec<OwnerDealId>,
    round_binding: [u8; 32],
}

impl FrozenShamirRound {
    pub fn new(
        session: &ShamirSharingSession,
        announcements: Vec<OwnerDealAnnouncement>,
    ) -> Result<Self, CollaborativeShamirError> {
        if announcements.len() != session.owners.len() {
            return Err(CollaborativeShamirError::WrongAnnouncementCount {
                expected: session.owners.len(),
                actual: announcements.len(),
            });
        }
        let mut seen = vec![false; session.owners.len()];
        for announcement in &announcements {
            if announcement.owner_index >= session.owners.len() {
                return Err(CollaborativeShamirError::AnnouncementOwnerOutOfRange {
                    owner_index: announcement.owner_index,
                    owner_count: session.owners.len(),
                });
            }
            if core::mem::replace(&mut seen[announcement.owner_index], true) {
                return Err(CollaborativeShamirError::DuplicateOwnerAnnouncement {
                    owner_index: announcement.owner_index,
                });
            }
        }
        let mut deal_ids = Vec::with_capacity(announcements.len());
        for (position, announcement) in announcements.into_iter().enumerate() {
            if announcement.owner_index != position {
                return Err(CollaborativeShamirError::ReorderedOwnerAnnouncement {
                    position,
                    expected_owner: position,
                    actual_owner: announcement.owner_index,
                });
            }
            if announcement.session_binding != session.context_binding {
                return Err(CollaborativeShamirError::AnnouncementSessionMismatch {
                    owner_index: position,
                });
            }
            if announcement.owner_label != session.owners[position].owner {
                return Err(CollaborativeShamirError::AnnouncementOwnerLabelMismatch {
                    owner_index: position,
                });
            }
            deal_ids.push(announcement.deal_id);
        }
        let round_binding = hash_frozen_round(session.context_binding, &deal_ids);
        Ok(Self {
            session: session.clone(),
            deal_ids,
            round_binding,
        })
    }

    pub const fn session(&self) -> &ShamirSharingSession {
        &self.session
    }

    pub fn deal_ids(&self) -> &[OwnerDealId] {
        &self.deal_ids
    }

    pub const fn round_binding(&self) -> [u8; 32] {
        self.round_binding
    }
}

/// One owner's private witness block.
///
/// The constructor consumes and overwrites its `BabyBear` vector after
/// canonicalizing it. Retained canonical words are wiped on drop.
pub struct OwnerWitnessBlock {
    owner: OwnerLabel,
    positions: Vec<CoefficientPosition>,
    coefficients: Zeroizing<Vec<u32>>,
}

impl OwnerWitnessBlock {
    /// Consume a zeroizing vector of canonical BabyBear words.
    pub fn new(
        owner: OwnerLabel,
        positions: Vec<CoefficientPosition>,
        coefficients: Zeroizing<Vec<u32>>,
    ) -> Result<Self, CollaborativeShamirError> {
        if let Some((owner_position, value)) = coefficients
            .iter()
            .copied()
            .enumerate()
            .find(|(_, value)| (*value as u64) >= BabyBear::ORDER_U64)
        {
            return Err(CollaborativeShamirError::NonCanonicalSecretCoefficient {
                owner_position,
                value,
            });
        }
        Ok(Self {
            owner,
            positions,
            coefficients,
        })
    }

    pub const fn owner(&self) -> OwnerLabel {
        self.owner
    }

    pub fn coefficient_count(&self) -> usize {
        self.coefficients.len()
    }
}

impl fmt::Debug for OwnerWitnessBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OwnerWitnessBlock")
            .field("owner", &self.owner)
            .field("positions", &self.positions)
            .field("coefficient_count", &self.coefficients.len())
            .field("coefficients", &"<redacted>")
            .finish()
    }
}

/// A confidential point-to-point delivery capability.
///
/// Implementations run inside the owner custody domain. They can call
/// [`OwnerShareMessage::seal`] with a receiver channel key, transmit only the
/// resulting [`SealedOwnerShareMessage`], and open it in the named receiver
/// domain. The callback consumes the opaque plaintext message; this module exposes
/// no production all-receiver plaintext return or raw plaintext codec.
pub trait ReceiverShareTransport {
    fn deliver_confidential(
        &mut self,
        round: &FrozenShamirRound,
        receiver: PartyIndex,
        receiver_label: ProverLabel,
        message: OwnerShareMessage,
    ) -> Result<(), ()>;
}

/// A pre-established symmetric channel key for one owner-to-receiver transport.
///
/// Key establishment and peer authentication are deliberately outside this
/// module. The key is non-cloneable, never exposed by a getter, and wiped on drop.
pub struct ReceiverTransportKey(Zeroizing<[u8; 32]>);

impl ReceiverTransportKey {
    pub fn new(key: Zeroizing<[u8; 32]>) -> Result<Self, CollaborativeShamirError> {
        if key.iter().all(|byte| *byte == 0) {
            return Err(CollaborativeShamirError::SealedShareAuthenticationFailed);
        }
        Ok(Self(key))
    }
}

impl fmt::Debug for ReceiverTransportKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ReceiverTransportKey(<redacted>)")
    }
}

/// Receiver-bound authenticated ciphertext suitable for an external transport.
///
/// All fields are public metadata or ciphertext. Plaintext shares are available
/// only by consuming this object through [`Self::open`] in the expected receiver
/// and frozen-round context.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SealedOwnerShareMessage {
    round_binding: [u8; 32],
    owner_index: usize,
    receiver: PartyIndex,
    receiver_label: ProverLabel,
    nonce: [u8; SEALED_SHARE_NONCE_BYTES],
    ciphertext: Vec<u8>,
}

impl SealedOwnerShareMessage {
    pub const fn owner_index(&self) -> usize {
        self.owner_index
    }

    pub const fn receiver(&self) -> PartyIndex {
        self.receiver
    }

    pub const fn receiver_label(&self) -> ProverLabel {
        self.receiver_label
    }

    /// Canonical ciphertext-only wire image.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(108 + self.ciphertext.len());
        out.extend_from_slice(SEALED_SHARE_WIRE_MAGIC_V1);
        out.extend_from_slice(&self.round_binding);
        out.extend_from_slice(&(self.owner_index as u64).to_le_bytes());
        out.extend_from_slice(&(self.receiver.get() as u64).to_le_bytes());
        out.extend_from_slice(&self.receiver_label.0);
        out.extend_from_slice(&self.nonce);
        out.extend_from_slice(&(self.ciphertext.len() as u64).to_le_bytes());
        out.extend_from_slice(&self.ciphertext);
        out
    }

    /// Decode the exact ciphertext envelope without opening its secret payload.
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, CollaborativeShamirError> {
        const HEADER: usize = 8 + 32 + 8 + 8 + 32 + SEALED_SHARE_NONCE_BYTES + 8;
        if bytes.len() < HEADER || &bytes[..8] != SEALED_SHARE_WIRE_MAGIC_V1 {
            return Err(CollaborativeShamirError::MalformedSealedShare);
        }
        let round_binding = bytes[8..40]
            .try_into()
            .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?;
        let owner_u64 = u64::from_le_bytes(
            bytes[40..48]
                .try_into()
                .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?,
        );
        let owner_index = usize::try_from(owner_u64)
            .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?;
        let receiver_u64 = u64::from_le_bytes(
            bytes[48..56]
                .try_into()
                .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?,
        );
        let receiver = PartyIndex::new(
            usize::try_from(receiver_u64)
                .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?,
        );
        let receiver_label = ProverLabel(
            bytes[56..88]
                .try_into()
                .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?,
        );
        let nonce_end = 88 + SEALED_SHARE_NONCE_BYTES;
        let nonce = bytes[88..nonce_end]
            .try_into()
            .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?;
        let ciphertext_len = u64::from_le_bytes(
            bytes[nonce_end..nonce_end + 8]
                .try_into()
                .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?,
        );
        let ciphertext_len = usize::try_from(ciphertext_len)
            .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?;
        if ciphertext_len < SEALED_SHARE_TAG_BYTES
            || ciphertext_len > MAX_SEALED_SHARE_CIPHERTEXT_BYTES
            || HEADER.checked_add(ciphertext_len) != Some(bytes.len())
        {
            return Err(CollaborativeShamirError::MalformedSealedShare);
        }
        Ok(Self {
            round_binding,
            owner_index,
            receiver,
            receiver_label,
            nonce,
            ciphertext: bytes[HEADER..].to_vec(),
        })
    }

    /// Authenticate, decrypt, and fully validate one receiver's sparse share.
    pub fn open(
        self,
        round: &FrozenShamirRound,
        expected_receiver: PartyIndex,
        key: &ReceiverTransportKey,
    ) -> Result<OwnerShareMessage, CollaborativeShamirError> {
        let receiver_index = expected_receiver.get();
        if self.round_binding != round.round_binding {
            return Err(CollaborativeShamirError::SealedShareContextMismatch);
        }
        if self.receiver != expected_receiver
            || receiver_index >= round.session.provers.len()
            || self.receiver_label != round.session.provers[receiver_index]
        {
            return Err(CollaborativeShamirError::SealedShareReceiverMismatch);
        }
        let assignment = round
            .session
            .owners
            .get(self.owner_index)
            .ok_or(CollaborativeShamirError::MalformedSealedShare)?;
        let expected_ciphertext_len = 88usize
            .checked_add(
                12usize
                    .checked_mul(assignment.positions.len())
                    .ok_or(CollaborativeShamirError::MalformedSealedShare)?,
            )
            .and_then(|plaintext| plaintext.checked_add(SEALED_SHARE_TAG_BYTES))
            .ok_or(CollaborativeShamirError::MalformedSealedShare)?;
        if self.ciphertext.len() != expected_ciphertext_len
            || expected_ciphertext_len > MAX_SEALED_SHARE_CIPHERTEXT_BYTES
        {
            return Err(CollaborativeShamirError::MalformedSealedShare);
        }
        let aad = sealed_share_aad(
            round,
            self.owner_index,
            expected_receiver,
            self.receiver_label,
        );
        let cipher = ChaCha20Poly1305::new((&*key.0).into());
        let plaintext = cipher
            .decrypt(
                (&self.nonce).into(),
                Payload {
                    msg: &self.ciphertext,
                    aad: &aad,
                },
            )
            .map_err(|_| CollaborativeShamirError::SealedShareAuthenticationFailed)?;
        decode_owner_share_plaintext(
            round,
            self.owner_index,
            expected_receiver,
            self.receiver_label,
            Zeroizing::new(plaintext),
        )
    }
}

/// One owner's sampled polynomial set, consumed on delivery.
pub struct PreparedOwnerDeal {
    session_binding: [u8; 32],
    owner_index: usize,
    owner_label: OwnerLabel,
    positions: Vec<CoefficientPosition>,
    privacy_threshold: usize,
    prover_count: usize,
    polynomial_coefficients: Zeroizing<Vec<u32>>,
    deal_id: OwnerDealId,
}

impl PreparedOwnerDeal {
    pub const fn announcement(&self) -> OwnerDealAnnouncement {
        OwnerDealAnnouncement {
            session_binding: self.session_binding,
            owner_index: self.owner_index,
            owner_label: self.owner_label,
            deal_id: self.deal_id,
        }
    }

    /// Consume this one-shot deal and send one opaque share message directly to
    /// each confidential receiver capability.
    pub fn deliver<T: ReceiverShareTransport>(
        self,
        round: &FrozenShamirRound,
        transport: &mut T,
    ) -> Result<(), CollaborativeShamirError> {
        if self.session_binding != round.session.context_binding
            || self.owner_index >= round.deal_ids.len()
            || self.deal_id != round.deal_ids[self.owner_index]
        {
            return Err(CollaborativeShamirError::PreparedDealRoundMismatch {
                owner_index: self.owner_index,
            });
        }
        let points = two_adic_prover_points(self.prover_count);
        let width = self.positions.len();
        for (receiver, point) in points.into_iter().enumerate() {
            let mut shares = Zeroizing::new(Vec::with_capacity(width));
            for column in 0..width {
                let mut power = BabyBear::ONE;
                let mut evaluation = BabyBear::new(self.polynomial_coefficients[column]);
                for degree in 1..=self.privacy_threshold {
                    power *= point;
                    evaluation +=
                        BabyBear::new(self.polynomial_coefficients[degree * width + column])
                            * power;
                }
                shares.push(evaluation.as_canonical_u32());
            }
            let receiver_index = PartyIndex::new(receiver);
            let receiver_label = round.session.provers[receiver];
            let message = OwnerShareMessage {
                session_binding: round.round_binding,
                owner_index: self.owner_index,
                owner_label: self.owner_label,
                deal_id: self.deal_id,
                receiver: receiver_index,
                receiver_label,
                positions: self.positions.clone(),
                shares,
            };
            transport
                .deliver_confidential(round, receiver_index, receiver_label, message)
                .map_err(|()| CollaborativeShamirError::TransportRejected { receiver })?;
        }
        Ok(())
    }
}

impl fmt::Debug for PreparedOwnerDeal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PreparedOwnerDeal")
            .field("owner_index", &self.owner_index)
            .field("owner_label", &self.owner_label)
            .field("positions", &self.positions)
            .field("privacy_threshold", &self.privacy_threshold)
            .field("prover_count", &self.prover_count)
            .field("polynomial_coefficients", &"<redacted>")
            .field("deal_id", &self.deal_id)
            .finish()
    }
}

/// One move-only owner-to-prover sparse Shamir message.
///
/// The payload cannot be cloned through the public API and is wiped when consumed
/// or dropped. Metadata getters deliberately do not expose shares.
pub struct OwnerShareMessage {
    session_binding: [u8; 32],
    owner_index: usize,
    owner_label: OwnerLabel,
    deal_id: OwnerDealId,
    receiver: PartyIndex,
    receiver_label: ProverLabel,
    positions: Vec<CoefficientPosition>,
    shares: Zeroizing<Vec<u32>>,
}

impl OwnerShareMessage {
    pub const fn owner_index(&self) -> usize {
        self.owner_index
    }

    pub const fn receiver(&self) -> PartyIndex {
        self.receiver
    }

    pub fn positions(&self) -> &[CoefficientPosition] {
        &self.positions
    }

    pub fn share_count(&self) -> usize {
        self.shares.len()
    }

    /// Consume and seal this message for its exact frozen-round receiver.
    ///
    /// The plaintext serialization remains module-private. External transports
    /// receive only [`SealedOwnerShareMessage::to_wire_bytes`]. A fresh random
    /// nonce is sampled for every call; the channel key must not be reused by a
    /// deployment whose RNG cannot provide nonce uniqueness with overwhelming
    /// probability.
    pub fn seal<R: CryptoRng + ?Sized>(
        self,
        round: &FrozenShamirRound,
        key: &ReceiverTransportKey,
        rng: &mut R,
    ) -> Result<SealedOwnerShareMessage, CollaborativeShamirError> {
        validate_owner_share_message(round, self.receiver, &self)?;
        let mut nonce = [0u8; SEALED_SHARE_NONCE_BYTES];
        while nonce.iter().all(|byte| *byte == 0) {
            rng.fill_bytes(&mut nonce);
        }
        let aad = sealed_share_aad(round, self.owner_index, self.receiver, self.receiver_label);
        let plaintext = encode_owner_share_plaintext(&self);
        if plaintext
            .len()
            .checked_add(SEALED_SHARE_TAG_BYTES)
            .is_none_or(|length| length > MAX_SEALED_SHARE_CIPHERTEXT_BYTES)
        {
            return Err(CollaborativeShamirError::MalformedSealedShare);
        }
        let cipher = ChaCha20Poly1305::new((&*key.0).into());
        let ciphertext = cipher
            .encrypt(
                (&nonce).into(),
                Payload {
                    msg: &plaintext,
                    aad: &aad,
                },
            )
            .map_err(|_| CollaborativeShamirError::SealedShareAuthenticationFailed)?;
        Ok(SealedOwnerShareMessage {
            round_binding: round.round_binding,
            owner_index: self.owner_index,
            receiver: self.receiver,
            receiver_label: self.receiver_label,
            nonce,
            ciphertext,
        })
    }
}

impl fmt::Debug for OwnerShareMessage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OwnerShareMessage")
            .field("session_binding", &self.session_binding)
            .field("owner_index", &self.owner_index)
            .field("owner_label", &self.owner_label)
            .field("deal_id", &self.deal_id)
            .field("receiver", &self.receiver)
            .field("receiver_label", &self.receiver_label)
            .field("positions", &self.positions)
            .field("share_count", &self.shares.len())
            .field("shares", &"<redacted>")
            .finish()
    }
}

/// One receiver-local Shamir row, branded by the complete sharing context.
///
/// It is deliberately non-`Clone`, redacts its values, and exposes no raw share
/// getter. The only public consumption path is the context-checking local
/// BaseFold encoder below.
pub struct SessionPartyShareInput {
    context_binding: [u8; 32],
    shape: TensorCodeShape,
    receiver: PartyIndex,
    receiver_label: ProverLabel,
    row_words: Zeroizing<Vec<u32>>,
}

impl SessionPartyShareInput {
    pub const fn context_binding(&self) -> [u8; 32] {
        self.context_binding
    }

    pub const fn shape(&self) -> TensorCodeShape {
        self.shape
    }

    pub const fn receiver(&self) -> PartyIndex {
        self.receiver
    }

    pub const fn receiver_label(&self) -> ProverLabel {
        self.receiver_label
    }

    /// Consume and locally encode the branded share after revalidating the exact
    /// session context. Session provenance remains on the encoded row.
    pub fn encode_local(
        self,
        round: &FrozenShamirRound,
    ) -> Result<SessionPartyEncodedRow, CollaborativeShamirError> {
        let session = &round.session;
        if self.context_binding != round.round_binding {
            return Err(CollaborativeShamirError::BoundRowContextMismatch);
        }
        if self.shape != session.shape {
            return Err(CollaborativeShamirError::BoundRowShapeMismatch);
        }
        let receiver = self.receiver.get();
        if receiver >= session.provers.len() || self.receiver_label != session.provers[receiver] {
            return Err(CollaborativeShamirError::BoundRowReceiverMismatch);
        }
        if self.row_words.len() != session.shape.message_columns() {
            return Err(CollaborativeShamirError::BoundRowShapeMismatch);
        }
        let domain_size = session.shape.encoded_columns();
        let generator = BabyBear::two_adic_generator(domain_size.ilog2() as usize);
        let mut point = BabyBear::ONE;
        let mut values = Zeroizing::new(Vec::with_capacity(domain_size));
        for _ in 0..domain_size {
            let evaluation = self
                .row_words
                .iter()
                .rev()
                .fold(BabyBear::ZERO, |acc, coefficient| {
                    acc * point + BabyBear::new(*coefficient)
                });
            values.push(evaluation.as_canonical_u32());
            point *= generator;
        }
        Ok(SessionPartyEncodedRow {
            context_binding: self.context_binding,
            shape: self.shape,
            receiver: self.receiver,
            receiver_label: self.receiver_label,
            values,
        })
    }
}

impl fmt::Debug for SessionPartyShareInput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SessionPartyShareInput")
            .field("context_binding", &self.context_binding)
            .field("shape", &self.shape)
            .field("receiver", &self.receiver)
            .field("receiver_label", &self.receiver_label)
            .field("coefficient_count", &self.row_words.len())
            .field("row_coefficients", &"<redacted>")
            .finish()
    }
}

/// Locally encoded BaseFold row that retains its sharing-session provenance.
///
/// The underlying row remains opaque pending the distributed MMCS transport
/// adapter; exposing it here would recreate the all-row reconstruction footgun.
pub struct SessionPartyEncodedRow {
    context_binding: [u8; 32],
    shape: TensorCodeShape,
    receiver: PartyIndex,
    receiver_label: ProverLabel,
    values: Zeroizing<Vec<u32>>,
}

impl SessionPartyEncodedRow {
    pub const fn context_binding(&self) -> [u8; 32] {
        self.context_binding
    }

    pub const fn shape(&self) -> TensorCodeShape {
        self.shape
    }

    pub const fn receiver(&self) -> PartyIndex {
        self.receiver
    }

    pub const fn receiver_label(&self) -> ProverLabel {
        self.receiver_label
    }

    /// Consume this receiver-local row into the blinded commitment/fold handoff.
    ///
    /// The public commitment absorbs the exact sharing epoch, relation, session,
    /// frozen deal set, tensor geometry, receiver index/label, fold round, and row
    /// values. A fresh 256-bit local blinding value prevents the commitment from
    /// becoming an offline oracle for low-entropy witness rows.
    pub fn commit_local<R: CryptoRng + ?Sized>(
        self,
        round: &FrozenShamirRound,
        rng: &mut R,
    ) -> Result<SessionPartyCommittedRow, CollaborativeShamirError> {
        validate_bound_row_context(
            round,
            self.context_binding,
            self.shape,
            self.receiver,
            self.receiver_label,
        )?;
        if self.values.len() != self.shape.encoded_columns() {
            return Err(CollaborativeShamirError::BoundRowShapeMismatch);
        }
        SessionPartyCommittedRow::from_local_values(
            round,
            self.receiver,
            self.receiver_label,
            0,
            self.values,
            rng,
        )
    }
}

impl fmt::Debug for SessionPartyEncodedRow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SessionPartyEncodedRow")
            .field("context_binding", &self.context_binding)
            .field("shape", &self.shape)
            .field("receiver", &self.receiver)
            .field("receiver_label", &self.receiver_label)
            .field("value_count", &self.values.len())
            .field("values", &"<redacted>")
            .finish()
    }
}

/// Public, blinded commitment to one exact receiver-local encoded/folded row.
///
/// This is a binding transcript handoff, not an MMCS opening proof. It is safe to
/// publish because the digest includes a fresh secret 256-bit blinding value held
/// only by [`SessionPartyCommittedRow`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SessionPartyRowCommitment {
    round_binding: [u8; 32],
    session_binding: [u8; 32],
    epoch: SharingEpoch,
    relation_id: SharingRelationId,
    shape: TensorCodeShape,
    fold_round: usize,
    columns: usize,
    receiver: PartyIndex,
    receiver_label: ProverLabel,
    digest: [u8; 32],
}

impl SessionPartyRowCommitment {
    pub const fn receiver(&self) -> PartyIndex {
        self.receiver
    }

    pub const fn receiver_label(&self) -> ProverLabel {
        self.receiver_label
    }

    pub const fn fold_round(&self) -> usize {
        self.fold_round
    }

    pub const fn columns(&self) -> usize {
        self.columns
    }

    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }
}

/// Receiver-local committed row whose values and blinding remain zeroizing.
///
/// The only state transition is [`Self::fold_local`], which consumes the old row,
/// verifies its exact place in the public commitment manifest, re-derives the
/// manifest-bound challenge, and returns a freshly blinded next-round row.
pub struct SessionPartyCommittedRow {
    round_binding: [u8; 32],
    session_binding: [u8; 32],
    epoch: SharingEpoch,
    relation_id: SharingRelationId,
    shape: TensorCodeShape,
    fold_round: usize,
    columns: usize,
    receiver: PartyIndex,
    receiver_label: ProverLabel,
    values: Zeroizing<Vec<u32>>,
    blinding: Zeroizing<[u8; 32]>,
    digest: [u8; 32],
}

impl SessionPartyCommittedRow {
    fn from_local_values<R: CryptoRng + ?Sized>(
        round: &FrozenShamirRound,
        receiver: PartyIndex,
        receiver_label: ProverLabel,
        fold_round: usize,
        values: Zeroizing<Vec<u32>>,
        rng: &mut R,
    ) -> Result<Self, CollaborativeShamirError> {
        validate_bound_row_context(
            round,
            round.round_binding,
            round.session.shape,
            receiver,
            receiver_label,
        )?;
        let columns = expected_fold_columns(round.session.shape, fold_round)
            .ok_or(CollaborativeShamirError::BoundRowShapeMismatch)?;
        if values.len() != columns
            || values
                .iter()
                .any(|value| (*value as u64) >= BabyBear::ORDER_U64)
        {
            return Err(CollaborativeShamirError::BoundRowShapeMismatch);
        }
        let mut blinding = Zeroizing::new([0u8; 32]);
        while blinding.iter().all(|byte| *byte == 0) {
            rng.fill_bytes(&mut *blinding);
        }
        let digest = hash_party_row_commitment(
            round,
            fold_round,
            columns,
            receiver,
            receiver_label,
            &blinding,
            &values,
        );
        Ok(Self {
            round_binding: round.round_binding,
            session_binding: round.session.context_binding,
            epoch: round.session.epoch,
            relation_id: round.session.relation_id,
            shape: round.session.shape,
            fold_round,
            columns,
            receiver,
            receiver_label,
            values,
            blinding,
            digest,
        })
    }

    pub const fn commitment(&self) -> SessionPartyRowCommitment {
        SessionPartyRowCommitment {
            round_binding: self.round_binding,
            session_binding: self.session_binding,
            epoch: self.epoch,
            relation_id: self.relation_id,
            shape: self.shape,
            fold_round: self.fold_round,
            columns: self.columns,
            receiver: self.receiver,
            receiver_label: self.receiver_label,
            digest: self.digest,
        }
    }

    pub const fn receiver(&self) -> PartyIndex {
        self.receiver
    }

    pub const fn fold_round(&self) -> usize {
        self.fold_round
    }

    pub const fn columns(&self) -> usize {
        self.columns
    }

    /// Consume and fold this exact local row under the published all-receiver
    /// commitment manifest and challenge.
    pub fn fold_local<R: CryptoRng + ?Sized>(
        self,
        round: &FrozenShamirRound,
        manifest: &SessionCommitmentManifest,
        transcript: &SessionFoldTranscript,
        supplied: &SessionFoldChallenge,
        rng: &mut R,
    ) -> Result<Self, CollaborativeShamirError> {
        validate_bound_row_context(
            round,
            self.round_binding,
            self.shape,
            self.receiver,
            self.receiver_label,
        )?;
        manifest.validate_for_round(round)?;
        if manifest.fold_round != self.fold_round || manifest.columns != self.columns {
            return Err(CollaborativeShamirError::CommitmentContextMismatch {
                receiver: self.receiver.get(),
            });
        }
        let recomputed_digest = hash_party_row_commitment(
            round,
            self.fold_round,
            self.columns,
            self.receiver,
            self.receiver_label,
            &self.blinding,
            &self.values,
        );
        if recomputed_digest != self.digest {
            return Err(CollaborativeShamirError::CommitmentDigestMismatch {
                receiver: self.receiver.get(),
            });
        }
        let published = manifest.commitments.get(self.receiver.get()).ok_or(
            CollaborativeShamirError::CommitmentDigestMismatch {
                receiver: self.receiver.get(),
            },
        )?;
        if published != &self.commitment() {
            return Err(CollaborativeShamirError::CommitmentDigestMismatch {
                receiver: self.receiver.get(),
            });
        }
        let expected = transcript.challenge(round, manifest)?;
        if &expected != supplied {
            return Err(CollaborativeShamirError::FoldTranscriptMismatch);
        }
        if self.columns == 1 {
            return Err(CollaborativeShamirError::FinalBoundRowCannotFold);
        }
        let values = fold_zeroizing_row(&self.values, supplied.value);
        Self::from_local_values(
            round,
            self.receiver,
            self.receiver_label,
            self.fold_round + 1,
            values,
            rng,
        )
    }
}

impl fmt::Debug for SessionPartyCommittedRow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SessionPartyCommittedRow")
            .field("commitment", &self.commitment())
            .field("values", &"<redacted>")
            .field("blinding", &"<redacted>")
            .finish()
    }
}

/// Exact all-receiver commitment manifest for one fold round.
///
/// A coordinator can assemble this object from public commitments without
/// receiving any row. Every party checks its own commitment at its canonical
/// receiver position before accepting a challenge derived from the manifest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SessionCommitmentManifest {
    round_binding: [u8; 32],
    session_binding: [u8; 32],
    epoch: SharingEpoch,
    relation_id: SharingRelationId,
    shape: TensorCodeShape,
    fold_round: usize,
    columns: usize,
    commitments: Vec<SessionPartyRowCommitment>,
    digest: [u8; 32],
}

impl SessionCommitmentManifest {
    pub fn new(
        round: &FrozenShamirRound,
        fold_round: usize,
        commitments: Vec<SessionPartyRowCommitment>,
    ) -> Result<Self, CollaborativeShamirError> {
        let session = &round.session;
        let columns = expected_fold_columns(session.shape, fold_round)
            .ok_or(CollaborativeShamirError::BoundRowShapeMismatch)?;
        if commitments.len() != session.shape.party_count() {
            return Err(CollaborativeShamirError::WrongCommitmentCount {
                expected: session.shape.party_count(),
                actual: commitments.len(),
            });
        }
        for (position, commitment) in commitments.iter().enumerate() {
            if commitment.receiver.get() != position {
                return Err(CollaborativeShamirError::ReorderedCommitment {
                    position,
                    actual_receiver: commitment.receiver.get(),
                });
            }
            if commitment.round_binding != round.round_binding
                || commitment.session_binding != session.context_binding
                || commitment.epoch != session.epoch
                || commitment.relation_id != session.relation_id
                || commitment.shape != session.shape
                || commitment.fold_round != fold_round
                || commitment.columns != columns
                || commitment.receiver_label != session.provers[position]
            {
                return Err(CollaborativeShamirError::CommitmentContextMismatch {
                    receiver: position,
                });
            }
        }
        let digest = hash_commitment_manifest(round, fold_round, columns, &commitments);
        Ok(Self {
            round_binding: round.round_binding,
            session_binding: session.context_binding,
            epoch: session.epoch,
            relation_id: session.relation_id,
            shape: session.shape,
            fold_round,
            columns,
            commitments,
            digest,
        })
    }

    fn validate_for_round(
        &self,
        round: &FrozenShamirRound,
    ) -> Result<(), CollaborativeShamirError> {
        if self.round_binding != round.round_binding
            || self.session_binding != round.session.context_binding
            || self.epoch != round.session.epoch
            || self.relation_id != round.session.relation_id
            || self.shape != round.session.shape
            || self.digest
                != hash_commitment_manifest(round, self.fold_round, self.columns, &self.commitments)
        {
            return Err(CollaborativeShamirError::BoundRowContextMismatch);
        }
        Ok(())
    }

    pub const fn fold_round(&self) -> usize {
        self.fold_round
    }

    pub const fn columns(&self) -> usize {
        self.columns
    }

    pub fn commitments(&self) -> &[SessionPartyRowCommitment] {
        &self.commitments
    }

    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }
}

/// Public statement/context used to derive exact manifest-bound fold challenges.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SessionFoldTranscript {
    statement_digest: [u8; 32],
    protocol_context_digest: [u8; 32],
}

impl SessionFoldTranscript {
    pub fn new(statement_digest: [u8; 32], protocol_context: &[u8]) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(SHAMIR_FOLD_TRANSCRIPT_DOMAIN_V1);
        hasher.update(b"protocol-context\0");
        hasher.update(&(protocol_context.len() as u64).to_le_bytes());
        hasher.update(protocol_context);
        Self {
            statement_digest,
            protocol_context_digest: *hasher.finalize().as_bytes(),
        }
    }

    pub fn challenge(
        &self,
        round: &FrozenShamirRound,
        manifest: &SessionCommitmentManifest,
    ) -> Result<SessionFoldChallenge, CollaborativeShamirError> {
        manifest.validate_for_round(round)?;
        let mut hasher = blake3::Hasher::new();
        hasher.update(SHAMIR_FOLD_TRANSCRIPT_DOMAIN_V1);
        hasher.update(b"fold-challenge\0");
        hasher.update(&self.statement_digest);
        hasher.update(&self.protocol_context_digest);
        absorb_round_hasher(&mut hasher, round);
        hasher.update(&(manifest.fold_round as u64).to_le_bytes());
        hasher.update(&(manifest.columns as u64).to_le_bytes());
        hasher.update(&manifest.digest);
        let binding = *hasher.finalize().as_bytes();
        Ok(SessionFoldChallenge {
            round_binding: round.round_binding,
            manifest_digest: manifest.digest,
            fold_round: manifest.fold_round,
            binding,
            value: hash_to_babybear(binding),
        })
    }
}

/// Base-field fold challenge bound to one exact session commitment manifest.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SessionFoldChallenge {
    round_binding: [u8; 32],
    manifest_digest: [u8; 32],
    fold_round: usize,
    binding: [u8; 32],
    value: BabyBear,
}

impl SessionFoldChallenge {
    pub const fn fold_round(self) -> usize {
        self.fold_round
    }

    pub const fn binding(self) -> [u8; 32] {
        self.binding
    }

    pub const fn value(self) -> BabyBear {
        self.value
    }
}

/// Prepare one owner's one-shot polynomial set and public deal announcement.
///
/// This returns no receiver messages. The consumed [`PreparedOwnerDeal`] later
/// delivers them directly through a confidential receiver transport after the
/// exact common announcement set has been frozen.
pub fn prepare_owner_deal<R: CryptoRng + ?Sized>(
    session: &ShamirSharingSession,
    block: OwnerWitnessBlock,
    rng: &mut R,
) -> Result<PreparedOwnerDeal, CollaborativeShamirError> {
    let owner_index = session
        .owners
        .iter()
        .position(|assignment| assignment.owner == block.owner)
        .ok_or(CollaborativeShamirError::UnknownOwner)?;
    let assignment = &session.owners[owner_index];
    if block.positions != assignment.positions {
        return Err(CollaborativeShamirError::OwnerBlockPositionsMismatch { owner_index });
    }
    if block.coefficients.len() != assignment.positions.len() {
        return Err(CollaborativeShamirError::OwnerBlockWidthMismatch {
            owner_index,
            expected: assignment.positions.len(),
            actual: block.coefficients.len(),
        });
    }

    let width = assignment.positions.len();
    let mut polynomial_coefficients =
        Zeroizing::new(Vec::with_capacity((session.privacy_threshold + 1) * width));
    polynomial_coefficients.extend(block.coefficients.iter().copied());
    for _degree in 1..=session.privacy_threshold {
        for _column in 0..width {
            polynomial_coefficients.push(sample_uniform_babybear(rng).as_canonical_u32());
        }
    }
    let mut deal_id_bytes = Zeroizing::new([0u8; 32]);
    while deal_id_bytes.iter().all(|byte| *byte == 0) {
        rng.fill_bytes(&mut *deal_id_bytes);
    }
    let deal_id = OwnerDealId(*deal_id_bytes);
    Ok(PreparedOwnerDeal {
        session_binding: session.context_binding,
        owner_index,
        owner_label: assignment.owner,
        positions: assignment.positions.clone(),
        privacy_threshold: session.privacy_threshold,
        prover_count: session.shape.party_count(),
        polynomial_coefficients,
        deal_id,
    })
}

/// Consume one prover's exact owner-message set and construct its BaseFold row.
///
/// This function sees neither owner secrets nor messages for other provers. It
/// refuses to sort: omission, duplication, append, and reordering fail closed.
pub fn aggregate_receiver_row(
    round: &FrozenShamirRound,
    receiver: PartyIndex,
    messages: Vec<OwnerShareMessage>,
) -> Result<SessionPartyShareInput, CollaborativeShamirError> {
    let session = &round.session;
    let receiver_index = receiver.get();
    if receiver_index >= session.shape.party_count() {
        return Err(CollaborativeShamirError::ReceiverOutOfRange {
            receiver: receiver_index,
            prover_count: session.shape.party_count(),
        });
    }
    if messages.len() != session.owners.len() {
        return Err(CollaborativeShamirError::WrongMessageCount {
            expected: session.owners.len(),
            actual: messages.len(),
        });
    }

    let mut seen = vec![false; session.owners.len()];
    for message in &messages {
        if message.owner_index >= session.owners.len() {
            return Err(CollaborativeShamirError::MessageOwnerOutOfRange {
                owner_index: message.owner_index,
                owner_count: session.owners.len(),
            });
        }
        if core::mem::replace(&mut seen[message.owner_index], true) {
            return Err(CollaborativeShamirError::DuplicateOwnerMessage {
                owner_index: message.owner_index,
            });
        }
    }

    let mut row = Zeroizing::new(vec![0u32; session.shape.message_columns()]);
    for (position, message) in messages.iter().enumerate() {
        if message.owner_index != position {
            return Err(CollaborativeShamirError::ReorderedOwnerMessage {
                position,
                expected_owner: position,
                actual_owner: message.owner_index,
            });
        }
        let assignment = &session.owners[position];
        if message.session_binding != round.round_binding {
            return Err(CollaborativeShamirError::SessionBindingMismatch {
                owner_index: position,
            });
        }
        if message.owner_label != assignment.owner {
            return Err(CollaborativeShamirError::OwnerLabelMismatch {
                owner_index: position,
            });
        }
        if message.deal_id != round.deal_ids[position] {
            return Err(CollaborativeShamirError::MessageDealIdMismatch {
                owner_index: position,
            });
        }
        if message.receiver != receiver {
            return Err(CollaborativeShamirError::ReceiverSubstitution {
                owner_index: position,
                expected_receiver: receiver_index,
                actual_receiver: message.receiver.get(),
            });
        }
        if message.receiver_label != session.provers[receiver_index] {
            return Err(CollaborativeShamirError::ReceiverLabelMismatch {
                owner_index: position,
            });
        }
        if message.positions != assignment.positions {
            return Err(CollaborativeShamirError::MessagePositionsMismatch {
                owner_index: position,
            });
        }
        if message.shares.len() != assignment.positions.len() {
            return Err(CollaborativeShamirError::MessageWidthMismatch {
                owner_index: position,
                expected: assignment.positions.len(),
                actual: message.shares.len(),
            });
        }
        for (coefficient_position, share) in assignment
            .positions
            .iter()
            .zip(message.shares.iter().copied())
        {
            row[coefficient_position.get()] = share;
        }
    }

    Ok(SessionPartyShareInput {
        context_binding: round.round_binding,
        shape: session.shape,
        receiver,
        receiver_label: session.provers[receiver_index],
        row_words: row,
    })
}

fn validate_owner_share_message(
    round: &FrozenShamirRound,
    receiver: PartyIndex,
    message: &OwnerShareMessage,
) -> Result<(), CollaborativeShamirError> {
    let session = &round.session;
    let receiver_index = receiver.get();
    if receiver_index >= session.provers.len() {
        return Err(CollaborativeShamirError::ReceiverOutOfRange {
            receiver: receiver_index,
            prover_count: session.provers.len(),
        });
    }
    if message.owner_index >= session.owners.len() {
        return Err(CollaborativeShamirError::MessageOwnerOutOfRange {
            owner_index: message.owner_index,
            owner_count: session.owners.len(),
        });
    }
    let owner_index = message.owner_index;
    let assignment = &session.owners[owner_index];
    if message.session_binding != round.round_binding {
        return Err(CollaborativeShamirError::SessionBindingMismatch { owner_index });
    }
    if message.owner_label != assignment.owner {
        return Err(CollaborativeShamirError::OwnerLabelMismatch { owner_index });
    }
    if message.deal_id != round.deal_ids[owner_index] {
        return Err(CollaborativeShamirError::MessageDealIdMismatch { owner_index });
    }
    if message.receiver != receiver {
        return Err(CollaborativeShamirError::ReceiverSubstitution {
            owner_index,
            expected_receiver: receiver_index,
            actual_receiver: message.receiver.get(),
        });
    }
    if message.receiver_label != session.provers[receiver_index] {
        return Err(CollaborativeShamirError::ReceiverLabelMismatch { owner_index });
    }
    if message.positions != assignment.positions {
        return Err(CollaborativeShamirError::MessagePositionsMismatch { owner_index });
    }
    if message.shares.len() != assignment.positions.len() {
        return Err(CollaborativeShamirError::MessageWidthMismatch {
            owner_index,
            expected: assignment.positions.len(),
            actual: message.shares.len(),
        });
    }
    if message
        .shares
        .iter()
        .any(|share| (*share as u64) >= BabyBear::ORDER_U64)
    {
        return Err(CollaborativeShamirError::MalformedSealedShare);
    }
    Ok(())
}

fn sealed_share_aad(
    round: &FrozenShamirRound,
    owner_index: usize,
    receiver: PartyIndex,
    receiver_label: ProverLabel,
) -> Vec<u8> {
    let session = &round.session;
    let mut aad = Vec::with_capacity(256);
    aad.extend_from_slice(SHAMIR_SEALED_SHARE_DOMAIN_V1);
    aad.extend_from_slice(&session.epoch.0);
    aad.extend_from_slice(&session.relation_id.0);
    aad.extend_from_slice(&session.context_binding);
    aad.extend_from_slice(&round.round_binding);
    absorb_shape_bytes(&mut aad, session.shape);
    aad.extend_from_slice(&(session.privacy_threshold as u64).to_le_bytes());
    aad.extend_from_slice(&(owner_index as u64).to_le_bytes());
    aad.extend_from_slice(&(receiver.get() as u64).to_le_bytes());
    aad.extend_from_slice(&receiver_label.0);
    aad
}

fn encode_owner_share_plaintext(message: &OwnerShareMessage) -> Zeroizing<Vec<u8>> {
    let mut out = Zeroizing::new(Vec::with_capacity(
        88 + message.positions.len() * 8 + message.shares.len() * 4,
    ));
    out.extend_from_slice(&(message.owner_index as u64).to_le_bytes());
    out.extend_from_slice(&message.owner_label.0);
    out.extend_from_slice(&message.deal_id.0);
    out.extend_from_slice(&(message.positions.len() as u64).to_le_bytes());
    for position in &message.positions {
        out.extend_from_slice(&(position.get() as u64).to_le_bytes());
    }
    out.extend_from_slice(&(message.shares.len() as u64).to_le_bytes());
    for share in message.shares.iter() {
        out.extend_from_slice(&share.to_le_bytes());
    }
    out
}

fn decode_owner_share_plaintext(
    round: &FrozenShamirRound,
    expected_owner_index: usize,
    receiver: PartyIndex,
    receiver_label: ProverLabel,
    plaintext: Zeroizing<Vec<u8>>,
) -> Result<OwnerShareMessage, CollaborativeShamirError> {
    let mut cursor = SecretCursor::new(&plaintext);
    let owner_index = usize::try_from(cursor.take_u64()?)
        .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?;
    if owner_index != expected_owner_index || owner_index >= round.session.owners.len() {
        return Err(CollaborativeShamirError::MalformedSealedShare);
    }
    let owner_label = OwnerLabel(cursor.take_array_32()?);
    let deal_id = OwnerDealId(cursor.take_array_32()?);
    let expected_width = round.session.owners[owner_index].positions.len();
    let position_count = usize::try_from(cursor.take_u64()?)
        .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?;
    if position_count != expected_width {
        return Err(CollaborativeShamirError::MalformedSealedShare);
    }
    let mut positions = Vec::with_capacity(position_count);
    for _ in 0..position_count {
        let position = usize::try_from(cursor.take_u64()?)
            .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?;
        positions.push(CoefficientPosition::new(position));
    }
    let share_count = usize::try_from(cursor.take_u64()?)
        .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?;
    if share_count != expected_width {
        return Err(CollaborativeShamirError::MalformedSealedShare);
    }
    let mut shares = Zeroizing::new(Vec::with_capacity(share_count));
    for _ in 0..share_count {
        let share = cursor.take_u32()?;
        if (share as u64) >= BabyBear::ORDER_U64 {
            return Err(CollaborativeShamirError::MalformedSealedShare);
        }
        shares.push(share);
    }
    if !cursor.is_finished() {
        return Err(CollaborativeShamirError::MalformedSealedShare);
    }
    let message = OwnerShareMessage {
        session_binding: round.round_binding,
        owner_index,
        owner_label,
        deal_id,
        receiver,
        receiver_label,
        positions,
        shares,
    };
    validate_owner_share_message(round, receiver, &message)?;
    Ok(message)
}

struct SecretCursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> SecretCursor<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], CollaborativeShamirError> {
        let end = self
            .offset
            .checked_add(N)
            .ok_or(CollaborativeShamirError::MalformedSealedShare)?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(CollaborativeShamirError::MalformedSealedShare)?
            .try_into()
            .map_err(|_| CollaborativeShamirError::MalformedSealedShare)?;
        self.offset = end;
        Ok(value)
    }

    fn take_u64(&mut self) -> Result<u64, CollaborativeShamirError> {
        Ok(u64::from_le_bytes(self.take()?))
    }

    fn take_u32(&mut self) -> Result<u32, CollaborativeShamirError> {
        Ok(u32::from_le_bytes(self.take()?))
    }

    fn take_array_32(&mut self) -> Result<[u8; 32], CollaborativeShamirError> {
        self.take()
    }

    fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}

fn absorb_shape_bytes(out: &mut Vec<u8>, shape: TensorCodeShape) {
    for value in [
        shape.message_rows(),
        shape.message_columns(),
        shape.party_count(),
        shape.encoded_columns(),
    ] {
        out.extend_from_slice(&(value as u64).to_le_bytes());
    }
}

fn validate_bound_row_context(
    round: &FrozenShamirRound,
    round_binding: [u8; 32],
    shape: TensorCodeShape,
    receiver: PartyIndex,
    receiver_label: ProverLabel,
) -> Result<(), CollaborativeShamirError> {
    if round_binding != round.round_binding {
        return Err(CollaborativeShamirError::BoundRowContextMismatch);
    }
    if shape != round.session.shape {
        return Err(CollaborativeShamirError::BoundRowShapeMismatch);
    }
    let receiver_index = receiver.get();
    if receiver_index >= round.session.provers.len()
        || receiver_label != round.session.provers[receiver_index]
    {
        return Err(CollaborativeShamirError::BoundRowReceiverMismatch);
    }
    Ok(())
}

fn expected_fold_columns(shape: TensorCodeShape, fold_round: usize) -> Option<usize> {
    if fold_round > shape.encoded_columns().ilog2() as usize {
        return None;
    }
    let columns = shape.encoded_columns() >> fold_round;
    (columns != 0).then_some(columns)
}

fn absorb_shape_hasher(hasher: &mut blake3::Hasher, shape: TensorCodeShape) {
    for value in [
        shape.message_rows(),
        shape.message_columns(),
        shape.party_count(),
        shape.encoded_columns(),
    ] {
        hasher.update(&(value as u64).to_le_bytes());
    }
}

fn absorb_round_hasher(hasher: &mut blake3::Hasher, round: &FrozenShamirRound) {
    let session = &round.session;
    hasher.update(&session.epoch.0);
    hasher.update(&session.relation_id.0);
    hasher.update(&session.context_binding);
    hasher.update(&round.round_binding);
    absorb_shape_hasher(hasher, session.shape);
    hasher.update(&(session.privacy_threshold as u64).to_le_bytes());
    hasher.update(&(session.owners.len() as u64).to_le_bytes());
    for assignment in &session.owners {
        hasher.update(&assignment.owner.0);
        hasher.update(&(assignment.positions.len() as u64).to_le_bytes());
        for position in &assignment.positions {
            hasher.update(&(position.get() as u64).to_le_bytes());
        }
    }
    hasher.update(&(session.provers.len() as u64).to_le_bytes());
    for prover in &session.provers {
        hasher.update(&prover.0);
    }
    hasher.update(&(round.deal_ids.len() as u64).to_le_bytes());
    for deal_id in &round.deal_ids {
        hasher.update(&deal_id.0);
    }
}

fn hash_party_row_commitment(
    round: &FrozenShamirRound,
    fold_round: usize,
    columns: usize,
    receiver: PartyIndex,
    receiver_label: ProverLabel,
    blinding: &[u8; 32],
    values: &[u32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(SHAMIR_ROW_COMMITMENT_DOMAIN_V1);
    absorb_round_hasher(&mut hasher, round);
    hasher.update(&(fold_round as u64).to_le_bytes());
    hasher.update(&(columns as u64).to_le_bytes());
    hasher.update(&(receiver.get() as u64).to_le_bytes());
    hasher.update(&receiver_label.0);
    hasher.update(blinding);
    hasher.update(&(values.len() as u64).to_le_bytes());
    for value in values {
        hasher.update(&value.to_le_bytes());
    }
    *hasher.finalize().as_bytes()
}

fn hash_commitment_manifest(
    round: &FrozenShamirRound,
    fold_round: usize,
    columns: usize,
    commitments: &[SessionPartyRowCommitment],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(SHAMIR_COMMITMENT_MANIFEST_DOMAIN_V1);
    absorb_round_hasher(&mut hasher, round);
    hasher.update(&(fold_round as u64).to_le_bytes());
    hasher.update(&(columns as u64).to_le_bytes());
    hasher.update(&(commitments.len() as u64).to_le_bytes());
    for commitment in commitments {
        hasher.update(&(commitment.receiver.get() as u64).to_le_bytes());
        hasher.update(&commitment.receiver_label.0);
        hasher.update(&commitment.digest);
    }
    *hasher.finalize().as_bytes()
}

fn fold_zeroizing_row(row: &[u32], beta: BabyBear) -> Zeroizing<Vec<u32>> {
    debug_assert!(row.len().is_power_of_two() && row.len() > 1);
    let half = row.len() / 2;
    let generator = BabyBear::two_adic_generator(row.len().ilog2() as usize);
    let inverse_two = (BabyBear::ONE + BabyBear::ONE).inverse();
    let mut point = BabyBear::ONE;
    let mut folded = Zeroizing::new(Vec::with_capacity(half));
    for index in 0..half {
        let lower = BabyBear::new(row[index]);
        let upper = BabyBear::new(row[index + half]);
        let even = (lower + upper) * inverse_two;
        let odd = (lower - upper) * inverse_two * point.inverse();
        folded.push((even + beta * odd).as_canonical_u32());
        point *= generator;
    }
    folded
}

fn hash_to_babybear(binding: [u8; 32]) -> BabyBear {
    let modulus = BabyBear::ORDER_U64 as u128;
    let bound = ((u64::MAX as u128 + 1) / modulus) * modulus;
    let mut counter = 0u64;
    loop {
        let mut hasher = blake3::Hasher::new();
        hasher.update(SHAMIR_FOLD_TRANSCRIPT_DOMAIN_V1);
        hasher.update(b"field-challenge\0");
        hasher.update(&binding);
        hasher.update(&counter.to_le_bytes());
        let digest = hasher.finalize();
        let candidate = u64::from_le_bytes(
            digest.as_bytes()[..8]
                .try_into()
                .expect("BLAKE3 output has eight bytes"),
        );
        if (candidate as u128) < bound {
            return BabyBear::new((candidate % BabyBear::ORDER_U64) as u32);
        }
        counter = counter.wrapping_add(1);
    }
}

fn hash_session_context(
    epoch: SharingEpoch,
    relation_id: SharingRelationId,
    shape: TensorCodeShape,
    privacy_threshold: usize,
    owners: &[OwnerAssignment],
    provers: &[ProverLabel],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(SHAMIR_SESSION_DOMAIN_V1);
    hasher.update(&epoch.0);
    hasher.update(&relation_id.0);
    for value in [
        shape.message_rows(),
        shape.message_columns(),
        shape.party_count(),
        shape.encoded_columns(),
        privacy_threshold,
    ] {
        hasher.update(&(value as u64).to_le_bytes());
    }
    hasher.update(&(owners.len() as u64).to_le_bytes());
    for assignment in owners {
        hasher.update(&assignment.owner.0);
        hasher.update(&(assignment.positions.len() as u64).to_le_bytes());
        for position in &assignment.positions {
            hasher.update(&(position.get() as u64).to_le_bytes());
        }
    }
    hasher.update(&(provers.len() as u64).to_le_bytes());
    for prover in provers {
        hasher.update(&prover.0);
    }
    *hasher.finalize().as_bytes()
}

fn hash_frozen_round(session_binding: [u8; 32], deal_ids: &[OwnerDealId]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(SHAMIR_FROZEN_ROUND_DOMAIN_V1);
    hasher.update(&session_binding);
    hasher.update(&(deal_ids.len() as u64).to_le_bytes());
    for deal_id in deal_ids {
        hasher.update(&deal_id.0);
    }
    *hasher.finalize().as_bytes()
}

fn two_adic_prover_points(prover_count: usize) -> Vec<BabyBear> {
    let generator = BabyBear::two_adic_generator(prover_count.ilog2() as usize);
    let mut point = BabyBear::ONE;
    let mut points = Vec::with_capacity(prover_count);
    for _ in 0..prover_count {
        points.push(point);
        point *= generator;
    }
    points
}

/// Uniform BabyBear sampling by 64-bit rejection from a caller-supplied CSPRNG.
fn sample_uniform_babybear<R: CryptoRng + ?Sized>(rng: &mut R) -> BabyBear {
    let modulus = BabyBear::ORDER_U64 as u128;
    let bound = ((u64::MAX as u128 + 1) / modulus) * modulus;
    loop {
        let candidate = rng.next_u64();
        if (candidate as u128) < bound {
            return BabyBear::new((candidate % BabyBear::ORDER_U64) as u32);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::collaborative_basefold::{
        PartyShareInput, centralized_tensor_encode, collaborative_tensor_encode,
    };
    use core::convert::Infallible;
    use p3_field::Field;
    use rand::rngs::StdRng;
    use rand::{SeedableRng, TryCryptoRng, TryRng};

    fn owner(value: u8) -> OwnerLabel {
        OwnerLabel::new([value; 32])
    }

    fn prover(value: u8) -> ProverLabel {
        ProverLabel::new([value; 32])
    }

    fn positions(values: &[usize]) -> Vec<CoefficientPosition> {
        values
            .iter()
            .copied()
            .map(CoefficientPosition::new)
            .collect()
    }

    fn epoch(value: u8) -> SharingEpoch {
        SharingEpoch::new([value; 32])
    }

    fn relation(value: u8) -> SharingRelationId {
        SharingRelationId::new([value; 32])
    }

    fn transport_key(value: u8) -> ReceiverTransportKey {
        ReceiverTransportKey::new(Zeroizing::new([value; 32])).unwrap()
    }

    fn fixture_session() -> ShamirSharingSession {
        ShamirSharingSession::new(
            epoch(0x51),
            relation(0x72),
            TensorCodeShape::new(3, 4, 4, 8).unwrap(),
            2,
            vec![
                OwnerAssignment::new(owner(10), positions(&[0, 2])),
                OwnerAssignment::new(owner(11), positions(&[1, 3])),
            ],
            vec![prover(20), prover(21), prover(22), prover(23)],
        )
        .unwrap()
    }

    struct AuditTransport {
        expected_labels: Vec<ProverLabel>,
        inboxes: Vec<Vec<OwnerShareMessage>>,
    }

    impl AuditTransport {
        fn new(session: &ShamirSharingSession) -> Self {
            Self {
                expected_labels: session.provers().to_vec(),
                inboxes: (0..session.shape().party_count())
                    .map(|_| Vec::new())
                    .collect(),
            }
        }
    }

    impl ReceiverShareTransport for AuditTransport {
        fn deliver_confidential(
            &mut self,
            _round: &FrozenShamirRound,
            receiver: PartyIndex,
            receiver_label: ProverLabel,
            message: OwnerShareMessage,
        ) -> Result<(), ()> {
            let index = receiver.get();
            if self.expected_labels.get(index).copied() != Some(receiver_label) {
                return Err(());
            }
            self.inboxes.get_mut(index).ok_or(())?.push(message);
            Ok(())
        }
    }

    fn deal_fixture(
        session: &ShamirSharingSession,
        seed: u64,
    ) -> (FrozenShamirRound, Vec<Vec<OwnerShareMessage>>) {
        let mut rng = StdRng::seed_from_u64(seed);
        let blocks = [
            OwnerWitnessBlock::new(owner(10), positions(&[0, 2]), Zeroizing::new(vec![17, 41]))
                .unwrap(),
            OwnerWitnessBlock::new(owner(11), positions(&[1, 3]), Zeroizing::new(vec![29, 53]))
                .unwrap(),
        ];
        let prepared: Vec<_> = blocks
            .into_iter()
            .map(|block| prepare_owner_deal(session, block, &mut rng).unwrap())
            .collect();
        let announcements = prepared
            .iter()
            .map(PreparedOwnerDeal::announcement)
            .collect();
        let round = FrozenShamirRound::new(session, announcements).unwrap();
        let mut transport = AuditTransport::new(session);
        for deal in prepared {
            deal.deliver(&round, &mut transport).unwrap();
        }
        (round, transport.inboxes)
    }

    fn aggregate_fixture(
        session: &ShamirSharingSession,
        seed: u64,
    ) -> (FrozenShamirRound, Vec<SessionPartyShareInput>) {
        // Deliberately test-only: production has no convenience that gathers more
        // than one receiver's private row in one process.
        let (round, inboxes) = deal_fixture(session, seed);
        let rows = inboxes
            .into_iter()
            .enumerate()
            .map(|(receiver, messages)| {
                aggregate_receiver_row(&round, PartyIndex::new(receiver), messages).unwrap()
            })
            .collect();
        (round, rows)
    }

    #[test]
    fn session_binds_relation_rosters_geometry_positions_and_order() {
        let base = fixture_session();
        assert_ne!(base.context_binding(), [0; 32]);

        let variants = [
            ShamirSharingSession::new(
                epoch(0x52),
                base.relation_id(),
                base.shape(),
                2,
                base.owners().to_vec(),
                base.provers().to_vec(),
            )
            .unwrap(),
            ShamirSharingSession::new(
                base.epoch(),
                relation(0x73),
                base.shape(),
                2,
                base.owners().to_vec(),
                base.provers().to_vec(),
            )
            .unwrap(),
            ShamirSharingSession::new(
                base.epoch(),
                base.relation_id(),
                TensorCodeShape::new(3, 4, 4, 16).unwrap(),
                2,
                base.owners().to_vec(),
                base.provers().to_vec(),
            )
            .unwrap(),
            ShamirSharingSession::new(
                base.epoch(),
                base.relation_id(),
                base.shape(),
                2,
                vec![
                    OwnerAssignment::new(owner(10), positions(&[0, 3])),
                    OwnerAssignment::new(owner(11), positions(&[1, 2])),
                ],
                base.provers().to_vec(),
            )
            .unwrap(),
            ShamirSharingSession::new(
                base.epoch(),
                base.relation_id(),
                base.shape(),
                2,
                base.owners().to_vec(),
                vec![prover(21), prover(20), prover(22), prover(23)],
            )
            .unwrap(),
        ];
        for variant in variants {
            assert_ne!(base.context_binding(), variant.context_binding());
        }
    }

    #[test]
    fn malformed_rosters_and_partitions_fail_closed() {
        let shape = TensorCodeShape::new(3, 4, 4, 8).unwrap();
        let provers = vec![prover(20), prover(21), prover(22), prover(23)];
        assert!(matches!(
            ShamirSharingSession::new(epoch(1), relation(2), shape, 0, vec![], provers.clone()),
            Err(CollaborativeShamirError::ZeroPrivacyThreshold)
        ));
        assert!(matches!(
            ShamirSharingSession::new(
                epoch(1),
                relation(2),
                shape,
                2,
                vec![OwnerAssignment::new(owner(10), positions(&[0, 1, 2, 3]))],
                provers.clone(),
            ),
            Err(CollaborativeShamirError::InsufficientOwnerCustodyDomains {
                minimum: 2,
                actual: 1
            })
        ));
        assert!(matches!(
            ShamirSharingSession::new(
                epoch(1),
                relation(2),
                shape,
                2,
                vec![
                    OwnerAssignment::new(owner(10), positions(&[0, 2])),
                    OwnerAssignment::new(owner(11), positions(&[3])),
                ],
                provers.clone(),
            ),
            Err(CollaborativeShamirError::MissingCoefficientPosition { position: 1 })
        ));
        assert!(matches!(
            ShamirSharingSession::new(
                epoch(1),
                relation(2),
                shape,
                2,
                vec![
                    OwnerAssignment::new(owner(10), positions(&[0, 2])),
                    OwnerAssignment::new(owner(11), positions(&[1, 2, 3])),
                ],
                provers.clone(),
            ),
            Err(CollaborativeShamirError::DuplicateCoefficientPosition {
                position: 2,
                first_owner: 0,
                second_owner: 1,
            })
        ));
        assert!(matches!(
            OwnerWitnessBlock::new(
                owner(10),
                positions(&[0]),
                Zeroizing::new(vec![BabyBear::ORDER_U64 as u32]),
            ),
            Err(CollaborativeShamirError::NonCanonicalSecretCoefficient {
                owner_position: 0,
                ..
            })
        ));
        assert!(matches!(
            ShamirSharingSession::new(
                epoch(1),
                relation(2),
                shape,
                2,
                vec![
                    OwnerAssignment::new(owner(10), positions(&[2, 0])),
                    OwnerAssignment::new(owner(11), positions(&[1, 3])),
                ],
                provers.clone(),
            ),
            Err(CollaborativeShamirError::NonCanonicalOwnerPositions {
                owner_index: 0,
                previous: 2,
                actual: 0,
            })
        ));
        assert!(matches!(
            ShamirSharingSession::new(
                epoch(1),
                relation(2),
                shape,
                2,
                vec![
                    OwnerAssignment::new(owner(10), positions(&[0, 2])),
                    OwnerAssignment::new(owner(10), positions(&[1, 3])),
                ],
                provers.clone(),
            ),
            Err(CollaborativeShamirError::DuplicateOwnerLabel {
                first: 0,
                second: 1
            })
        ));
        assert!(matches!(
            ShamirSharingSession::new(
                epoch(1),
                relation(2),
                TensorCodeShape::new(2, 4, 4, 8).unwrap(),
                2,
                vec![
                    OwnerAssignment::new(owner(10), positions(&[0, 2])),
                    OwnerAssignment::new(owner(11), positions(&[1, 3])),
                ],
                provers,
            ),
            Err(CollaborativeShamirError::SharingRowMismatch {
                expected: 3,
                actual: 2
            })
        ));
    }

    #[test]
    fn receiver_assembles_only_its_addressed_exact_owner_set() {
        let session = fixture_session();
        let (_round, rows) = aggregate_fixture(&session, 0x5eed);
        assert_eq!(rows.len(), 4);
        for (receiver, row) in rows.iter().enumerate() {
            assert_eq!(row.receiver(), PartyIndex::new(receiver));
            assert_eq!(row.row_words.len(), 4);
        }
        let plaintext = [17, 29, 41, 53];
        assert!(rows.iter().all(|row| row.row_words.as_slice() != plaintext));
        let audit_rows = audit_party_share_inputs(&rows);
        collaborative_tensor_encode(session.shape(), &audit_rows).unwrap();

        let (round, mut local_rows) = aggregate_fixture(&session, 0x6eed);
        let local = local_rows.remove(0);
        let encoded = local.encode_local(&round).unwrap();
        assert_eq!(encoded.receiver(), PartyIndex::new(0));
        assert_eq!(encoded.context_binding(), round.round_binding());
    }

    #[test]
    fn omission_duplicate_reorder_cross_session_and_receiver_substitution_refuse() {
        let session = fixture_session();

        let (round, mut inboxes) = deal_fixture(&session, 1);
        let mut omitted = inboxes.remove(0);
        omitted.pop();
        assert!(matches!(
            aggregate_receiver_row(&round, PartyIndex::new(0), omitted),
            Err(CollaborativeShamirError::WrongMessageCount {
                expected: 2,
                actual: 1
            })
        ));

        let (round, mut inboxes) = deal_fixture(&session, 2);
        let mut duplicate = inboxes.remove(0);
        let (_other_round, mut other_inboxes) = deal_fixture(&session, 3);
        duplicate[1] = other_inboxes.remove(0).remove(0);
        assert!(matches!(
            aggregate_receiver_row(&round, PartyIndex::new(0), duplicate),
            Err(CollaborativeShamirError::DuplicateOwnerMessage { owner_index: 0 })
        ));

        let (round, mut inboxes) = deal_fixture(&session, 4);
        let mut reordered = inboxes.remove(0);
        reordered.swap(0, 1);
        assert!(matches!(
            aggregate_receiver_row(&round, PartyIndex::new(0), reordered),
            Err(CollaborativeShamirError::ReorderedOwnerMessage {
                position: 0,
                expected_owner: 0,
                actual_owner: 1,
            })
        ));

        let different_session = ShamirSharingSession::new(
            epoch(0x99),
            session.relation_id(),
            session.shape(),
            2,
            session.owners().to_vec(),
            session.provers().to_vec(),
        )
        .unwrap();
        let (different_round, _different_inboxes) = deal_fixture(&different_session, 50);
        let (_original_round, mut original_inboxes) = deal_fixture(&session, 5);
        assert!(matches!(
            aggregate_receiver_row(
                &different_round,
                PartyIndex::new(0),
                original_inboxes.remove(0),
            ),
            Err(CollaborativeShamirError::SessionBindingMismatch { owner_index: 0 })
        ));

        let (round, mut inboxes) = deal_fixture(&session, 6);
        assert!(matches!(
            aggregate_receiver_row(&round, PartyIndex::new(1), inboxes.remove(0),),
            Err(CollaborativeShamirError::ReceiverSubstitution {
                owner_index: 0,
                expected_receiver: 1,
                actual_receiver: 0,
            })
        ));
    }

    #[test]
    fn position_and_label_mutations_refuse() {
        let session = fixture_session();

        let (round, mut inboxes) = deal_fixture(&session, 7);
        let mut wrong_positions = inboxes.remove(0);
        wrong_positions[0].positions.swap(0, 1);
        assert!(matches!(
            aggregate_receiver_row(&round, PartyIndex::new(0), wrong_positions),
            Err(CollaborativeShamirError::MessagePositionsMismatch { owner_index: 0 })
        ));

        let (round, mut inboxes) = deal_fixture(&session, 8);
        let mut wrong_label = inboxes.remove(0);
        wrong_label[0].receiver_label = prover(0xff);
        assert!(matches!(
            aggregate_receiver_row(&round, PartyIndex::new(0), wrong_label),
            Err(CollaborativeShamirError::ReceiverLabelMismatch { owner_index: 0 })
        ));
    }

    #[test]
    fn branded_row_refuses_post_aggregation_cross_epoch_handoff() {
        let session = fixture_session();
        let (_round, mut rows) = aggregate_fixture(&session, 9);
        let row = rows.remove(0);
        let different_epoch = ShamirSharingSession::new(
            epoch(0xa0),
            session.relation_id(),
            session.shape(),
            session.privacy_threshold(),
            session.owners().to_vec(),
            session.provers().to_vec(),
        )
        .unwrap();
        let (different_round, _inboxes) = deal_fixture(&different_epoch, 90);
        assert!(matches!(
            row.encode_local(&different_round),
            Err(CollaborativeShamirError::BoundRowContextMismatch)
        ));
    }

    #[test]
    fn frozen_deal_ids_refuse_same_session_redeal_mixing() {
        let session = fixture_session();
        let (old_round, mut old_inboxes) = deal_fixture(&session, 0x1111);
        let (new_round, mut new_inboxes) = deal_fixture(&session, 0x2222);
        assert_ne!(old_round.round_binding(), new_round.round_binding());
        assert_ne!(old_round.deal_ids(), new_round.deal_ids());

        let mut mixed = new_inboxes.remove(0);
        mixed[0] = old_inboxes.remove(0).remove(0);
        assert!(matches!(
            aggregate_receiver_row(&new_round, PartyIndex::new(0), mixed),
            Err(CollaborativeShamirError::SessionBindingMismatch { owner_index: 0 })
        ));
    }

    #[test]
    fn frozen_round_requires_exact_ordered_owner_announcement_set() {
        let session = fixture_session();
        let mut rng = StdRng::seed_from_u64(0x3333);
        let first = prepare_owner_deal(
            &session,
            OwnerWitnessBlock::new(owner(10), positions(&[0, 2]), Zeroizing::new(vec![17, 41]))
                .unwrap(),
            &mut rng,
        )
        .unwrap();
        let second = prepare_owner_deal(
            &session,
            OwnerWitnessBlock::new(owner(11), positions(&[1, 3]), Zeroizing::new(vec![29, 53]))
                .unwrap(),
            &mut rng,
        )
        .unwrap();
        let a = first.announcement();
        let b = second.announcement();
        assert_eq!(
            OwnerDealAnnouncement::from_wire_bytes(&a.to_wire_bytes()).unwrap(),
            a
        );
        let mut malformed_announcement = a.to_wire_bytes();
        malformed_announcement.push(0);
        assert!(matches!(
            OwnerDealAnnouncement::from_wire_bytes(&malformed_announcement),
            Err(CollaborativeShamirError::MalformedAnnouncement)
        ));
        assert!(matches!(
            FrozenShamirRound::new(&session, vec![a]),
            Err(CollaborativeShamirError::WrongAnnouncementCount {
                expected: 2,
                actual: 1
            })
        ));
        assert!(matches!(
            FrozenShamirRound::new(&session, vec![a, a]),
            Err(CollaborativeShamirError::DuplicateOwnerAnnouncement { owner_index: 0 })
        ));
        assert!(matches!(
            FrozenShamirRound::new(&session, vec![b, a]),
            Err(CollaborativeShamirError::ReorderedOwnerAnnouncement {
                position: 0,
                expected_owner: 0,
                actual_owner: 1
            })
        ));
    }

    #[test]
    fn sealed_external_transport_roundtrips_and_tampering_fails_closed() {
        let session = fixture_session();
        let key = transport_key(0x91);
        let wrong_key = transport_key(0x92);
        let (round, mut inboxes) = deal_fixture(&session, 0x5151);
        let messages = inboxes.remove(0);
        let mut rng = StdRng::seed_from_u64(0x6161);
        let mut opened = Vec::new();
        for message in messages {
            let sealed = message.seal(&round, &key, &mut rng).unwrap();
            assert!(sealed.owner_index() < session.owners().len());
            assert_eq!(sealed.receiver(), PartyIndex::new(0));
            assert_eq!(sealed.receiver_label(), session.provers()[0]);
            let wire = sealed.to_wire_bytes();
            let parsed = SealedOwnerShareMessage::from_wire_bytes(&wire).unwrap();
            opened.push(parsed.open(&round, PartyIndex::new(0), &key).unwrap());
        }
        aggregate_receiver_row(&round, PartyIndex::new(0), opened).unwrap();

        let (round, mut inboxes) = deal_fixture(&session, 0x7171);
        let message = inboxes.remove(0).remove(0);
        let sealed = message.seal(&round, &key, &mut rng).unwrap();
        assert!(matches!(
            sealed.clone().open(&round, PartyIndex::new(1), &key),
            Err(CollaborativeShamirError::SealedShareReceiverMismatch)
        ));
        assert!(matches!(
            sealed.clone().open(&round, PartyIndex::new(0), &wrong_key),
            Err(CollaborativeShamirError::SealedShareAuthenticationFailed)
        ));
        let (other_round, _other_inboxes) = deal_fixture(&session, 0x8181);
        assert!(matches!(
            sealed.clone().open(&other_round, PartyIndex::new(0), &key),
            Err(CollaborativeShamirError::SealedShareContextMismatch)
        ));

        let valid_wire = sealed.to_wire_bytes();
        let mut wrong_exact_length = valid_wire.clone();
        wrong_exact_length.push(0);
        let old_ciphertext_len = u64::from_le_bytes(valid_wire[100..108].try_into().unwrap());
        wrong_exact_length[100..108].copy_from_slice(&(old_ciphertext_len + 1).to_le_bytes());
        let wrong_exact_length =
            SealedOwnerShareMessage::from_wire_bytes(&wrong_exact_length).unwrap();
        assert!(matches!(
            wrong_exact_length.open(&round, PartyIndex::new(0), &key),
            Err(CollaborativeShamirError::MalformedSealedShare)
        ));

        let mut oversized = vec![0u8; 108 + MAX_SEALED_SHARE_CIPHERTEXT_BYTES + 1];
        oversized[..108].copy_from_slice(&valid_wire[..108]);
        oversized[100..108]
            .copy_from_slice(&((MAX_SEALED_SHARE_CIPHERTEXT_BYTES + 1) as u64).to_le_bytes());
        assert!(matches!(
            SealedOwnerShareMessage::from_wire_bytes(&oversized),
            Err(CollaborativeShamirError::MalformedSealedShare)
        ));

        let mut wire = valid_wire;
        *wire.last_mut().unwrap() ^= 0x80;
        let tampered = SealedOwnerShareMessage::from_wire_bytes(&wire).unwrap();
        assert!(matches!(
            tampered.open(&round, PartyIndex::new(0), &key),
            Err(CollaborativeShamirError::SealedShareAuthenticationFailed)
        ));
        wire.pop();
        assert!(matches!(
            SealedOwnerShareMessage::from_wire_bytes(&wire),
            Err(CollaborativeShamirError::MalformedSealedShare)
        ));
    }

    #[test]
    fn bound_commitment_manifest_drives_receiver_local_fold() {
        let session = fixture_session();
        let (round, rows) = aggregate_fixture(&session, 0x9191);
        let mut rng = StdRng::seed_from_u64(0xa1a1);
        let mut committed = Vec::new();
        for row in rows {
            committed.push(
                row.encode_local(&round)
                    .unwrap()
                    .commit_local(&round, &mut rng)
                    .unwrap(),
            );
        }
        let commitments = committed.iter().map(|row| row.commitment()).collect();
        let manifest = SessionCommitmentManifest::new(&round, 0, commitments).unwrap();
        assert_eq!(manifest.commitments().len(), session.shape().party_count());
        assert_eq!(manifest.columns(), session.shape().encoded_columns());
        let transcript = SessionFoldTranscript::new([0x33; 32], b"dark-bazaar/turn/7");
        let challenge = transcript.challenge(&round, &manifest).unwrap();
        assert_eq!(challenge.fold_round(), 0);
        assert_ne!(challenge.binding(), [0; 32]);

        let expected_first = fold_zeroizing_row(&committed[0].values, challenge.value());
        let mut folded = Vec::new();
        for row in committed {
            folded.push(
                row.fold_local(&round, &manifest, &transcript, &challenge, &mut rng)
                    .unwrap(),
            );
        }
        assert_eq!(folded[0].values.as_slice(), expected_first.as_slice());
        assert!(
            folded
                .iter()
                .all(|row| row.fold_round() == 1 && row.columns() == 4)
        );

        let next_commitments = folded.iter().map(|row| row.commitment()).collect();
        let next_manifest = SessionCommitmentManifest::new(&round, 1, next_commitments).unwrap();
        let next_challenge = transcript.challenge(&round, &next_manifest).unwrap();
        assert_ne!(manifest.digest(), next_manifest.digest());
        assert_ne!(challenge.binding(), next_challenge.binding());
    }

    #[test]
    fn bound_commitments_are_blinded_and_refuse_manifest_or_transcript_substitution() {
        let session = fixture_session();
        let (round_a, mut rows_a) = aggregate_fixture(&session, 0xb1b1);
        let (round_b, mut rows_b) = aggregate_fixture(&session, 0xb1b1);
        assert_eq!(round_a, round_b);
        let mut rng_a = StdRng::seed_from_u64(1);
        let mut rng_b = StdRng::seed_from_u64(2);
        let committed_a = rows_a
            .remove(0)
            .encode_local(&round_a)
            .unwrap()
            .commit_local(&round_a, &mut rng_a)
            .unwrap();
        let committed_b = rows_b
            .remove(0)
            .encode_local(&round_b)
            .unwrap()
            .commit_local(&round_b, &mut rng_b)
            .unwrap();
        assert_ne!(
            committed_a.commitment().digest(),
            committed_b.commitment().digest()
        );

        let (_same_round, rows) = aggregate_fixture(&session, 0xb1b1);
        let mut all_committed = Vec::new();
        for row in rows {
            all_committed.push(
                row.encode_local(&round_a)
                    .unwrap()
                    .commit_local(&round_a, &mut rng_a)
                    .unwrap(),
            );
        }
        let mut commitments: Vec<_> = all_committed.iter().map(|row| row.commitment()).collect();
        commitments.swap(0, 1);
        assert!(matches!(
            SessionCommitmentManifest::new(&round_a, 0, commitments),
            Err(CollaborativeShamirError::ReorderedCommitment {
                position: 0,
                actual_receiver: 1
            })
        ));

        let mut commitments: Vec<_> = all_committed.iter().map(|row| row.commitment()).collect();
        commitments[0].digest[0] ^= 1;
        let substituted = SessionCommitmentManifest::new(&round_a, 0, commitments).unwrap();
        let transcript = SessionFoldTranscript::new([0x44; 32], b"correct-context");
        let supplied = transcript.challenge(&round_a, &substituted).unwrap();
        let local = all_committed.remove(0);
        assert!(matches!(
            local.fold_local(&round_a, &substituted, &transcript, &supplied, &mut rng_a,),
            Err(CollaborativeShamirError::CommitmentDigestMismatch { receiver: 0 })
        ));

        let (round, rows) = aggregate_fixture(&session, 0xc1c1);
        let mut committed = Vec::new();
        for row in rows {
            committed.push(
                row.encode_local(&round)
                    .unwrap()
                    .commit_local(&round, &mut rng_a)
                    .unwrap(),
            );
        }
        let manifest = SessionCommitmentManifest::new(
            &round,
            0,
            committed.iter().map(|row| row.commitment()).collect(),
        )
        .unwrap();
        let correct = SessionFoldTranscript::new([0x55; 32], b"correct-context");
        let wrong = SessionFoldTranscript::new([0x55; 32], b"wrong-context");
        let wrong_challenge = wrong.challenge(&round, &manifest).unwrap();
        assert!(matches!(
            committed.remove(0).fold_local(
                &round,
                &manifest,
                &correct,
                &wrong_challenge,
                &mut rng_a,
            ),
            Err(CollaborativeShamirError::FoldTranscriptMismatch)
        ));
    }

    #[test]
    fn threshold_plus_one_rows_reconstruct_exact_owner_witness() {
        let session = fixture_session();
        let (_round, rows) = aggregate_fixture(&session, 0xabad1dea);
        let reconstructed = reconstruct_secret_row_for_audit(&session, &rows[..3]);
        assert_eq!(
            reconstructed,
            vec![
                BabyBear::new(17),
                BabyBear::new(29),
                BabyBear::new(41),
                BabyBear::new(53),
            ]
        );
        // Every t+1 subset, not merely the first rows, reconstructs the same row.
        for omitted in 0..rows.len() {
            let subset: Vec<_> = rows
                .iter()
                .enumerate()
                .filter(|(index, _)| *index != omitted)
                .map(|(_, row)| SessionPartyShareInput {
                    context_binding: row.context_binding,
                    shape: row.shape,
                    receiver: row.receiver,
                    receiver_label: row.receiver_label,
                    row_words: Zeroizing::new(row.row_words.to_vec()),
                })
                .collect();
            assert_eq!(
                reconstruct_secret_row_for_audit(&session, &subset),
                reconstructed
            );
        }
    }

    #[test]
    fn rows_differentially_match_central_tensor_encoder() {
        let session = fixture_session();
        let (_round, rows) = aggregate_fixture(&session, 0x1234_5678);
        let audit_rows = audit_party_share_inputs(&rows);
        let distributed = collaborative_tensor_encode(session.shape(), &audit_rows)
            .unwrap()
            .recombine()
            .unwrap();
        let coefficient_matrix = interpolate_sharing_matrix_for_audit(&session, &rows);
        let centralized = centralized_tensor_encode(session.shape(), &coefficient_matrix).unwrap();
        assert_eq!(distributed, centralized);
        let first_mask_row = &coefficient_matrix[4..8];
        let second_mask_row = &coefficient_matrix[8..12];
        assert_ne!(first_mask_row, second_mask_row);
        for left in 0..4 {
            for right in left + 1..4 {
                assert_ne!(
                    (first_mask_row[left], second_mask_row[left]),
                    (first_mask_row[right], second_mask_row[right]),
                    "independent coefficient columns reused both Shamir masks"
                );
            }
        }
    }

    struct ScriptedCryptoRng {
        words: Vec<u64>,
        next: usize,
    }

    impl ScriptedCryptoRng {
        fn new(words: Vec<u64>) -> Self {
            Self { words, next: 0 }
        }
    }

    impl TryRng for ScriptedCryptoRng {
        type Error = Infallible;

        fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
            Ok(self.try_next_u64()? as u32)
        }

        fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
            let word = self.words[self.next];
            self.next += 1;
            Ok(word)
        }

        fn try_fill_bytes(&mut self, destination: &mut [u8]) -> Result<(), Self::Error> {
            for chunk in destination.chunks_mut(8) {
                let word = self.try_next_u64()?.to_le_bytes();
                chunk.copy_from_slice(&word[..chunk.len()]);
            }
            Ok(())
        }
    }

    impl TryCryptoRng for ScriptedCryptoRng {}

    #[test]
    fn rejection_sampler_refuses_boundary_then_accepts_exact_residue() {
        let modulus = BabyBear::ORDER_U64 as u128;
        let bound = ((u64::MAX as u128 + 1) / modulus) * modulus;
        assert!(bound <= u64::MAX as u128);
        let accepted = BabyBear::ORDER_U64 * 3 + 7;
        let mut rng = ScriptedCryptoRng::new(vec![bound as u64, accepted]);
        assert_eq!(sample_uniform_babybear(&mut rng), BabyBear::new(7));
        assert_eq!(rng.next, 2, "the rejection boundary must consume one retry");
    }

    #[test]
    fn scripted_multicolumn_masks_produce_exact_distinct_horner_rows() {
        let session = ShamirSharingSession::new(
            epoch(0xd1),
            relation(0xd2),
            TensorCodeShape::new(3, 3, 4, 4).unwrap(),
            2,
            vec![
                OwnerAssignment::new(owner(1), positions(&[0, 1])),
                OwnerAssignment::new(owner(2), positions(&[2])),
            ],
            vec![prover(1), prover(2), prover(3), prover(4)],
        )
        .unwrap();
        // Layout after preparation is [secrets], [degree-1 masks], [degree-2 masks].
        let mut rng = ScriptedCryptoRng::new(vec![2, 3, 5, 7, 11, 12, 13, 14]);
        let block =
            OwnerWitnessBlock::new(owner(1), positions(&[0, 1]), Zeroizing::new(vec![11, 13]))
                .unwrap();
        let prepared = prepare_owner_deal(&session, block, &mut rng).unwrap();
        assert_eq!(&*prepared.polynomial_coefficients, &[11, 13, 2, 3, 5, 7]);
        let mut dummy_rng = StdRng::seed_from_u64(0xd00d);
        let dummy = prepare_owner_deal(
            &session,
            OwnerWitnessBlock::new(owner(2), positions(&[2]), Zeroizing::new(vec![17])).unwrap(),
            &mut dummy_rng,
        )
        .unwrap();
        let round = FrozenShamirRound::new(
            &session,
            vec![prepared.announcement(), dummy.announcement()],
        )
        .unwrap();
        let mut transport = AuditTransport::new(&session);
        prepared.deliver(&round, &mut transport).unwrap();
        dummy.deliver(&round, &mut transport).unwrap();

        // x_0=1. x_2=-1 on the order-four two-adic subgroup.
        assert_eq!(&*transport.inboxes[0][0].shares, &[18, 23]);
        assert_eq!(&*transport.inboxes[2][0].shares, &[14, 17]);
    }

    #[test]
    fn exhaustive_f5_one_observation_is_independent_of_secret() {
        // Complete p(X)=s+rX enumeration at non-zero x=2 in F5.
        let mut reference = None;
        for secret in 0..5usize {
            let mut counts = [0usize; 5];
            for mask in 0..5usize {
                counts[(secret + 2 * mask) % 5] += 1;
            }
            assert_eq!(counts, [1; 5]);
            if let Some(reference) = reference {
                assert_eq!(counts, reference);
            } else {
                reference = Some(counts);
            }
        }
    }

    #[test]
    fn implementation_observations_are_statistically_non_degenerate() {
        let session = ShamirSharingSession::new(
            epoch(0xa1),
            relation(0xb2),
            TensorCodeShape::new(2, 2, 2, 2).unwrap(),
            1,
            vec![
                OwnerAssignment::new(owner(1), positions(&[0])),
                OwnerAssignment::new(owner(2), positions(&[1])),
            ],
            vec![prover(1), prover(2)],
        )
        .unwrap();
        let mut rng = StdRng::seed_from_u64(0xdecafbad);
        let mut buckets = [0usize; 16];
        for _ in 0..4096 {
            let block =
                OwnerWitnessBlock::new(owner(1), positions(&[0]), Zeroizing::new(vec![0x1234]))
                    .unwrap();
            let prepared = prepare_owner_deal(&session, block, &mut rng).unwrap();
            let dummy = prepare_owner_deal(
                &session,
                OwnerWitnessBlock::new(owner(2), positions(&[1]), Zeroizing::new(vec![0x4321]))
                    .unwrap(),
                &mut rng,
            )
            .unwrap();
            let round = FrozenShamirRound::new(
                &session,
                vec![prepared.announcement(), dummy.announcement()],
            )
            .unwrap();
            let mut transport = AuditTransport::new(&session);
            prepared.deliver(&round, &mut transport).unwrap();
            dummy.deliver(&round, &mut transport).unwrap();
            buckets[transport.inboxes[0][0].shares[0] as usize & 15] += 1;
        }
        // Smoke evidence only, with a deliberately wide deterministic tolerance.
        assert!(buckets.iter().all(|count| (180..=340).contains(count)));
    }

    /// Test-only escape hatch into the older centralized algebraic oracle.
    fn audit_party_share_inputs(rows: &[SessionPartyShareInput]) -> Vec<PartyShareInput> {
        rows.iter()
            .map(|row| {
                PartyShareInput::from_untrusted(
                    row.receiver,
                    row.row_words.iter().copied().map(BabyBear::new).collect(),
                )
            })
            .collect()
    }

    /// Audit-only reconstruction: no production symbol can assemble the witness.
    fn reconstruct_secret_row_for_audit(
        session: &ShamirSharingSession,
        rows: &[SessionPartyShareInput],
    ) -> Vec<BabyBear> {
        assert_eq!(rows.len(), session.privacy_threshold + 1);
        let all_points = two_adic_prover_points(session.shape.party_count());
        let points: Vec<_> = rows
            .iter()
            .map(|row| all_points[row.receiver().get()])
            .collect();
        (0..session.shape.message_columns())
            .map(|column| {
                let evaluations: Vec<_> = rows
                    .iter()
                    .map(|row| BabyBear::new(row.row_words[column]))
                    .collect();
                interpolate_at_zero(&points, &evaluations)
            })
            .collect()
    }

    fn interpolate_sharing_matrix_for_audit(
        session: &ShamirSharingSession,
        rows: &[SessionPartyShareInput],
    ) -> Vec<BabyBear> {
        let count = session.shape.message_rows();
        let all_points = two_adic_prover_points(session.shape.party_count());
        let points = &all_points[..count];
        let mut matrix = vec![BabyBear::ZERO; count * session.shape.message_columns()];
        for column in 0..session.shape.message_columns() {
            let evaluations: Vec<_> = rows[..count]
                .iter()
                .map(|row| BabyBear::new(row.row_words[column]))
                .collect();
            let coefficients = interpolate_polynomial(points, &evaluations);
            for (row, coefficient) in coefficients.into_iter().enumerate() {
                matrix[row * session.shape.message_columns() + column] = coefficient;
            }
        }
        matrix
    }

    fn interpolate_at_zero(points: &[BabyBear], values: &[BabyBear]) -> BabyBear {
        assert_eq!(points.len(), values.len());
        points
            .iter()
            .enumerate()
            .map(|(i, x_i)| {
                let mut numerator = BabyBear::ONE;
                let mut denominator = BabyBear::ONE;
                for (j, x_j) in points.iter().enumerate() {
                    if i != j {
                        numerator *= -*x_j;
                        denominator *= *x_i - *x_j;
                    }
                }
                values[i] * numerator * denominator.inverse()
            })
            .sum()
    }

    fn interpolate_polynomial(points: &[BabyBear], values: &[BabyBear]) -> Vec<BabyBear> {
        assert_eq!(points.len(), values.len());
        let mut result = vec![BabyBear::ZERO; points.len()];
        for i in 0..points.len() {
            let mut basis = vec![BabyBear::ONE];
            let mut denominator = BabyBear::ONE;
            for (j, x_j) in points.iter().enumerate() {
                if i == j {
                    continue;
                }
                let mut next = vec![BabyBear::ZERO; basis.len() + 1];
                for (degree, coefficient) in basis.iter().copied().enumerate() {
                    next[degree] -= coefficient * *x_j;
                    next[degree + 1] += coefficient;
                }
                basis = next;
                denominator *= points[i] - *x_j;
            }
            let scale = values[i] * denominator.inverse();
            for (degree, coefficient) in basis.into_iter().enumerate() {
                result[degree] += coefficient * scale;
            }
        }
        result
    }
}
