//! Signer-independent exact-FNSP consensus cores and local validator envelopes.
//!
//! FNSP-v3 activation identity includes one node-local executor public key.  That format is useful
//! as solo-node recovery evidence, but it is not a deterministic federation consensus coordinate:
//! validators with distinct local keys hash distinct activation preimages.  V4 separates:
//!
//! * fixed-width [`ExactFnspV4ActivationCore`] and [`ExactFnspV4FrameCore`] records, whose IDs contain
//!   no local signer identity, signature, receipt encoding, or wall-clock field; and
//! * [`LocalExactFnspV4Envelope`], a classical Ed25519 observation of one already-fixed frame ID at
//!   one federation/committee epoch/commit ordinal.
//!
//! This module is additive substrate.  It does **not** implement committee collection, threshold
//! signing, finality selection, persistence, or the v3-to-v4 cutover.  In particular, a valid local
//! envelope is evidence from one validator; it is not a quorum certificate.

use core::fmt;

use dregg_circuit::exact_nullifier_aafi::Digest8;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use ed25519_dalek::{Signer, SigningKey, VerifyingKey};

use crate::ExactFnspV3StatePoint;

const ACTIVATION_MAGIC: [u8; 4] = *b"EXA4";
const FRAME_MAGIC: [u8; 4] = *b"EXF4";
const ENVELOPE_MAGIC: [u8; 4] = *b"EXE4";
const WIRE_VERSION: u16 = 1;

const ACTIVATION_ID_DOMAIN: &str = "dregg-exact-fnsp-v4-activation-core-v1";
const FRAME_ID_DOMAIN: &str = "dregg-exact-fnsp-v4-frame-core-v1";
const LOCAL_ENVELOPE_SIGNATURE_DOMAIN: &[u8] = b"dregg-exact-fnsp-v4-local-envelope-signature-v1:";

const PREFIX_LEN: usize = 8;
pub const EXACT_FNSP_V4_ACTIVATION_CORE_LEN: usize = 233;
pub const EXACT_FNSP_V4_FRAME_CORE_LEN: usize = 666;
pub const LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN: usize = 184;
const LOCAL_ENVELOPE_MESSAGE_LEN: usize = LOCAL_ENVELOPE_SIGNATURE_DOMAIN.len() + 80;

/// Typed signer-independent activation ID.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExactFnspV4ActivationId([u8; 32]);

impl ExactFnspV4ActivationId {
    pub const fn bytes(self) -> [u8; 32] {
        self.0
    }
}

/// Typed signer-independent frame ID.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExactFnspV4FrameId([u8; 32]);

impl ExactFnspV4FrameId {
    pub const fn bytes(self) -> [u8; 32] {
        self.0
    }
}

/// Signer-independent exact-v4 activation core.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactFnspV4ActivationCore {
    protocol_epoch: u64,
    federation_id: [u8; 32],
    committee_epoch: u64,
    receipt_cutover_next_index: u64,
    receipt_cutover_tail_hash: Option<[u8; 32]>,
    exact_initial: ExactFnspV3StatePoint,
    verifier_program_id: [u8; 32],
    transition_program_id: [u8; 32],
}

impl ExactFnspV4ActivationCore {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        protocol_epoch: u64,
        federation_id: [u8; 32],
        committee_epoch: u64,
        receipt_cutover_next_index: u64,
        receipt_cutover_tail_hash: Option<[u8; 32]>,
        exact_initial: ExactFnspV3StatePoint,
        verifier_program_id: [u8; 32],
        transition_program_id: [u8; 32],
    ) -> Result<Self, ExactFnspV4ConsensusError> {
        if protocol_epoch == 0 {
            return Err(ExactFnspV4ConsensusError::ZeroProtocolEpoch);
        }
        if (receipt_cutover_next_index == 0) != receipt_cutover_tail_hash.is_none() {
            return Err(ExactFnspV4ConsensusError::CutoverCoordinateMismatch);
        }
        Ok(Self {
            protocol_epoch,
            federation_id,
            committee_epoch,
            receipt_cutover_next_index,
            receipt_cutover_tail_hash,
            exact_initial,
            verifier_program_id,
            transition_program_id,
        })
    }

    pub const fn protocol_epoch(&self) -> u64 {
        self.protocol_epoch
    }

    pub const fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }

    pub const fn committee_epoch(&self) -> u64 {
        self.committee_epoch
    }

    pub const fn receipt_cutover_next_index(&self) -> u64 {
        self.receipt_cutover_next_index
    }

    pub const fn receipt_cutover_tail_hash(&self) -> Option<[u8; 32]> {
        self.receipt_cutover_tail_hash
    }

    pub const fn exact_initial(&self) -> ExactFnspV3StatePoint {
        self.exact_initial
    }

    pub const fn verifier_program_id(&self) -> [u8; 32] {
        self.verifier_program_id
    }

    pub const fn transition_program_id(&self) -> [u8; 32] {
        self.transition_program_id
    }

    pub fn id(&self) -> ExactFnspV4ActivationId {
        let bytes = self.to_canonical_bytes();
        let mut hasher = blake3::Hasher::new_derive_key(ACTIVATION_ID_DOMAIN);
        hasher.update(&bytes);
        ExactFnspV4ActivationId(*hasher.finalize().as_bytes())
    }

    pub fn to_canonical_bytes(&self) -> [u8; EXACT_FNSP_V4_ACTIVATION_CORE_LEN] {
        let mut out = [0u8; EXACT_FNSP_V4_ACTIVATION_CORE_LEN];
        write_prefix(&mut out, ACTIVATION_MAGIC);
        let mut cursor = PREFIX_LEN;
        write_u64(&mut out, &mut cursor, self.protocol_epoch);
        write_32(&mut out, &mut cursor, self.federation_id);
        write_u64(&mut out, &mut cursor, self.committee_epoch);
        write_u64(&mut out, &mut cursor, self.receipt_cutover_next_index);
        write_optional_32(&mut out, &mut cursor, self.receipt_cutover_tail_hash);
        write_state_point(&mut out, &mut cursor, self.exact_initial);
        write_32(&mut out, &mut cursor, self.verifier_program_id);
        write_32(&mut out, &mut cursor, self.transition_program_id);
        debug_assert_eq!(cursor, EXACT_FNSP_V4_ACTIVATION_CORE_LEN);
        out
    }

    pub fn decode_canonical(bytes: &[u8]) -> Result<Self, ExactFnspV4ConsensusError> {
        require_wire(bytes, EXACT_FNSP_V4_ACTIVATION_CORE_LEN, ACTIVATION_MAGIC)?;
        let mut cursor = PREFIX_LEN;
        let protocol_epoch = read_u64(bytes, &mut cursor);
        let federation_id = read_32(bytes, &mut cursor);
        let committee_epoch = read_u64(bytes, &mut cursor);
        let receipt_cutover_next_index = read_u64(bytes, &mut cursor);
        let receipt_cutover_tail_hash = read_optional_32(bytes, &mut cursor)?;
        let exact_initial = read_state_point(bytes, &mut cursor)?;
        let verifier_program_id = read_32(bytes, &mut cursor);
        let transition_program_id = read_32(bytes, &mut cursor);
        debug_assert_eq!(cursor, EXACT_FNSP_V4_ACTIVATION_CORE_LEN);
        Self::new(
            protocol_epoch,
            federation_id,
            committee_epoch,
            receipt_cutover_next_index,
            receipt_cutover_tail_hash,
            exact_initial,
            verifier_program_id,
            transition_program_id,
        )
    }
}

/// Typed predecessor.  An activation ID cannot be reinterpreted as a frame ID.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExactFnspV4FramePredecessor {
    Activation(ExactFnspV4ActivationId),
    Frame(ExactFnspV4FrameId),
}

impl ExactFnspV4FramePredecessor {
    const fn tag(self) -> u8 {
        match self {
            Self::Activation(_) => 1,
            Self::Frame(_) => 2,
        }
    }

    const fn bytes(self) -> [u8; 32] {
        match self {
            Self::Activation(id) => id.bytes(),
            Self::Frame(id) => id.bytes(),
        }
    }
}

/// Paired per-actor durable-receipt predecessor coordinate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactFnspV4ReceiptPredecessor {
    pub index: u64,
    pub hash: [u8; 32],
}

/// Caller-carried fields used to construct a validated fixed-width frame core.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactFnspV4FrameCoreFields {
    pub activation_id: ExactFnspV4ActivationId,
    pub sequence: u64,
    pub predecessor: ExactFnspV4FramePredecessor,
    pub receipt_index: u64,
    pub receipt_hash: [u8; 32],
    pub full_predecessor: Option<ExactFnspV4ReceiptPredecessor>,
    pub block_id: [u8; 32],
    pub commit_ordinal: u64,
    pub turn_hash: [u8; 32],
    pub forest_hash: [u8; 32],
    pub actor: [u8; 32],
    pub federation_id: [u8; 32],
    pub full_pre_state: [u8; 32],
    pub full_post_state: [u8; 32],
    pub exact_before: ExactFnspV3StatePoint,
    pub exact_after: ExactFnspV3StatePoint,
    pub accepted_statement_digest: [u8; 32],
    pub accepted_proof_digest: [u8; 32],
    pub consequence_commitment: [u8; 32],
    pub output_notes_commitment: [u8; 32],
}

/// Signer-independent exact-v4 frame core.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactFnspV4FrameCore(ExactFnspV4FrameCoreFields);

impl ExactFnspV4FrameCore {
    pub fn new(
        activation: &ExactFnspV4ActivationCore,
        fields: ExactFnspV4FrameCoreFields,
    ) -> Result<Self, ExactFnspV4ConsensusError> {
        if fields.activation_id != activation.id() {
            return Err(ExactFnspV4ConsensusError::ActivationIdentityMismatch);
        }
        if fields.federation_id != activation.federation_id {
            return Err(ExactFnspV4ConsensusError::FederationMismatch);
        }
        if fields.sequence == 0 {
            return Err(ExactFnspV4ConsensusError::ZeroFrameSequence);
        }
        match (fields.sequence, fields.predecessor) {
            (1, ExactFnspV4FramePredecessor::Activation(id)) if id == activation.id() => {
                if fields.exact_before != activation.exact_initial {
                    return Err(ExactFnspV4ConsensusError::ActivationStateMismatch);
                }
            }
            (1, _) => return Err(ExactFnspV4ConsensusError::FirstFramePredecessorMismatch),
            (_, ExactFnspV4FramePredecessor::Frame(_)) => {}
            (_, ExactFnspV4FramePredecessor::Activation(_)) => {
                return Err(ExactFnspV4ConsensusError::ContinuationPredecessorMismatch);
            }
        }
        if fields
            .full_predecessor
            .is_some_and(|previous| previous.index >= fields.receipt_index)
        {
            return Err(ExactFnspV4ConsensusError::ReceiptPredecessorOrder);
        }
        if fields.exact_after.count()
            != fields
                .exact_before
                .count()
                .checked_add(1)
                .ok_or(ExactFnspV4ConsensusError::ExactCountOverflow)?
        {
            return Err(ExactFnspV4ConsensusError::ExactCountStepMismatch);
        }
        Ok(Self(fields))
    }

    pub const fn fields(&self) -> &ExactFnspV4FrameCoreFields {
        &self.0
    }

    pub fn id(&self) -> ExactFnspV4FrameId {
        let bytes = self.to_canonical_bytes();
        let mut hasher = blake3::Hasher::new_derive_key(FRAME_ID_DOMAIN);
        hasher.update(&bytes);
        ExactFnspV4FrameId(*hasher.finalize().as_bytes())
    }

    pub fn to_canonical_bytes(&self) -> [u8; EXACT_FNSP_V4_FRAME_CORE_LEN] {
        let fields = &self.0;
        let mut out = [0u8; EXACT_FNSP_V4_FRAME_CORE_LEN];
        write_prefix(&mut out, FRAME_MAGIC);
        let mut cursor = PREFIX_LEN;
        write_32(&mut out, &mut cursor, fields.activation_id.bytes());
        write_u64(&mut out, &mut cursor, fields.sequence);
        out[cursor] = fields.predecessor.tag();
        cursor += 1;
        write_32(&mut out, &mut cursor, fields.predecessor.bytes());
        write_u64(&mut out, &mut cursor, fields.receipt_index);
        write_32(&mut out, &mut cursor, fields.receipt_hash);
        write_optional_receipt_predecessor(&mut out, &mut cursor, fields.full_predecessor);
        write_32(&mut out, &mut cursor, fields.block_id);
        write_u64(&mut out, &mut cursor, fields.commit_ordinal);
        write_32(&mut out, &mut cursor, fields.turn_hash);
        write_32(&mut out, &mut cursor, fields.forest_hash);
        write_32(&mut out, &mut cursor, fields.actor);
        write_32(&mut out, &mut cursor, fields.federation_id);
        write_32(&mut out, &mut cursor, fields.full_pre_state);
        write_32(&mut out, &mut cursor, fields.full_post_state);
        write_state_point(&mut out, &mut cursor, fields.exact_before);
        write_state_point(&mut out, &mut cursor, fields.exact_after);
        write_32(&mut out, &mut cursor, fields.accepted_statement_digest);
        write_32(&mut out, &mut cursor, fields.accepted_proof_digest);
        write_32(&mut out, &mut cursor, fields.consequence_commitment);
        write_32(&mut out, &mut cursor, fields.output_notes_commitment);
        debug_assert_eq!(cursor, EXACT_FNSP_V4_FRAME_CORE_LEN);
        out
    }

    pub fn decode_canonical(
        bytes: &[u8],
        activation: &ExactFnspV4ActivationCore,
    ) -> Result<Self, ExactFnspV4ConsensusError> {
        require_wire(bytes, EXACT_FNSP_V4_FRAME_CORE_LEN, FRAME_MAGIC)?;
        let mut cursor = PREFIX_LEN;
        let activation_id = ExactFnspV4ActivationId(read_32(bytes, &mut cursor));
        let sequence = read_u64(bytes, &mut cursor);
        let predecessor_tag = bytes[cursor];
        cursor += 1;
        let predecessor_bytes = read_32(bytes, &mut cursor);
        let predecessor = match predecessor_tag {
            1 => {
                ExactFnspV4FramePredecessor::Activation(ExactFnspV4ActivationId(predecessor_bytes))
            }
            2 => ExactFnspV4FramePredecessor::Frame(ExactFnspV4FrameId(predecessor_bytes)),
            tag => return Err(ExactFnspV4ConsensusError::BadPredecessorTag(tag)),
        };
        let receipt_index = read_u64(bytes, &mut cursor);
        let receipt_hash = read_32(bytes, &mut cursor);
        let full_predecessor = read_optional_receipt_predecessor(bytes, &mut cursor)?;
        let block_id = read_32(bytes, &mut cursor);
        let commit_ordinal = read_u64(bytes, &mut cursor);
        let turn_hash = read_32(bytes, &mut cursor);
        let forest_hash = read_32(bytes, &mut cursor);
        let actor = read_32(bytes, &mut cursor);
        let federation_id = read_32(bytes, &mut cursor);
        let full_pre_state = read_32(bytes, &mut cursor);
        let full_post_state = read_32(bytes, &mut cursor);
        let exact_before = read_state_point(bytes, &mut cursor)?;
        let exact_after = read_state_point(bytes, &mut cursor)?;
        let accepted_statement_digest = read_32(bytes, &mut cursor);
        let accepted_proof_digest = read_32(bytes, &mut cursor);
        let consequence_commitment = read_32(bytes, &mut cursor);
        let output_notes_commitment = read_32(bytes, &mut cursor);
        debug_assert_eq!(cursor, EXACT_FNSP_V4_FRAME_CORE_LEN);
        Self::new(
            activation,
            ExactFnspV4FrameCoreFields {
                activation_id,
                sequence,
                predecessor,
                receipt_index,
                receipt_hash,
                full_predecessor,
                block_id,
                commit_ordinal,
                turn_hash,
                forest_hash,
                actor,
                federation_id,
                full_pre_state,
                full_post_state,
                exact_before,
                exact_after,
                accepted_statement_digest,
                accepted_proof_digest,
                consequence_commitment,
                output_notes_commitment,
            },
        )
    }

    fn validate_scope(
        &self,
        activation: &ExactFnspV4ActivationCore,
    ) -> Result<(), ExactFnspV4ConsensusError> {
        if self.0.activation_id != activation.id() {
            return Err(ExactFnspV4ConsensusError::ActivationIdentityMismatch);
        }
        if self.0.federation_id != activation.federation_id {
            return Err(ExactFnspV4ConsensusError::FederationMismatch);
        }
        Ok(())
    }
}

/// One validator's classical observation of a fixed common frame ID.
///
/// The validator key/signature are outside both common core encodings.  This is not a committee or
/// threshold certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalExactFnspV4Envelope {
    federation_id: [u8; 32],
    committee_epoch: u64,
    commit_ordinal: u64,
    frame_id: ExactFnspV4FrameId,
    validator_public_key: [u8; 32],
    signature: [u8; 64],
}

impl LocalExactFnspV4Envelope {
    pub fn sign(
        activation: &ExactFnspV4ActivationCore,
        frame: &ExactFnspV4FrameCore,
        signing_key: &SigningKey,
    ) -> Result<Self, ExactFnspV4ConsensusError> {
        frame.validate_scope(activation)?;
        let frame_id = frame.id();
        let message = local_envelope_signature_message(
            activation.federation_id,
            activation.committee_epoch,
            frame.0.commit_ordinal,
            frame_id,
        );
        let signature = signing_key.sign(&message).to_bytes();
        Ok(Self {
            federation_id: activation.federation_id,
            committee_epoch: activation.committee_epoch,
            commit_ordinal: frame.0.commit_ordinal,
            frame_id,
            validator_public_key: signing_key.verifying_key().to_bytes(),
            signature,
        })
    }

    pub fn verify(
        &self,
        activation: &ExactFnspV4ActivationCore,
        frame: &ExactFnspV4FrameCore,
    ) -> Result<(), ExactFnspV4ConsensusError> {
        frame.validate_scope(activation)?;
        if self.federation_id != activation.federation_id
            || self.committee_epoch != activation.committee_epoch
            || self.commit_ordinal != frame.0.commit_ordinal
            || self.frame_id != frame.id()
        {
            return Err(ExactFnspV4ConsensusError::EnvelopeCoreMismatch);
        }
        let key = VerifyingKey::from_bytes(&self.validator_public_key)
            .map_err(|_| ExactFnspV4ConsensusError::InvalidValidatorKey)?;
        let signature = ed25519_dalek::Signature::from_bytes(&self.signature);
        key.verify_strict(&self.signature_message(), &signature)
            .map_err(|_| ExactFnspV4ConsensusError::InvalidEnvelopeSignature)
    }

    pub const fn frame_id(&self) -> ExactFnspV4FrameId {
        self.frame_id
    }

    pub const fn validator_public_key(&self) -> [u8; 32] {
        self.validator_public_key
    }

    pub fn signature_message(&self) -> [u8; LOCAL_ENVELOPE_MESSAGE_LEN] {
        local_envelope_signature_message(
            self.federation_id,
            self.committee_epoch,
            self.commit_ordinal,
            self.frame_id,
        )
    }

    pub fn to_canonical_bytes(&self) -> [u8; LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN] {
        let mut out = [0u8; LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN];
        write_prefix(&mut out, ENVELOPE_MAGIC);
        let mut cursor = PREFIX_LEN;
        write_32(&mut out, &mut cursor, self.federation_id);
        write_u64(&mut out, &mut cursor, self.committee_epoch);
        write_u64(&mut out, &mut cursor, self.commit_ordinal);
        write_32(&mut out, &mut cursor, self.frame_id.bytes());
        write_32(&mut out, &mut cursor, self.validator_public_key);
        out[cursor..cursor + 64].copy_from_slice(&self.signature);
        cursor += 64;
        debug_assert_eq!(cursor, LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN);
        out
    }

    pub fn decode_canonical(bytes: &[u8]) -> Result<Self, ExactFnspV4ConsensusError> {
        require_wire(bytes, LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN, ENVELOPE_MAGIC)?;
        let mut cursor = PREFIX_LEN;
        let federation_id = read_32(bytes, &mut cursor);
        let committee_epoch = read_u64(bytes, &mut cursor);
        let commit_ordinal = read_u64(bytes, &mut cursor);
        let frame_id = ExactFnspV4FrameId(read_32(bytes, &mut cursor));
        let validator_public_key = read_32(bytes, &mut cursor);
        let mut signature = [0u8; 64];
        signature.copy_from_slice(&bytes[cursor..cursor + 64]);
        cursor += 64;
        debug_assert_eq!(cursor, LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN);
        Ok(Self {
            federation_id,
            committee_epoch,
            commit_ordinal,
            frame_id,
            validator_public_key,
            signature,
        })
    }
}

fn local_envelope_signature_message(
    federation_id: [u8; 32],
    committee_epoch: u64,
    commit_ordinal: u64,
    frame_id: ExactFnspV4FrameId,
) -> [u8; LOCAL_ENVELOPE_MESSAGE_LEN] {
    let mut message = [0u8; LOCAL_ENVELOPE_MESSAGE_LEN];
    let mut cursor = 0;
    message[..LOCAL_ENVELOPE_SIGNATURE_DOMAIN.len()]
        .copy_from_slice(LOCAL_ENVELOPE_SIGNATURE_DOMAIN);
    cursor += LOCAL_ENVELOPE_SIGNATURE_DOMAIN.len();
    message[cursor..cursor + 32].copy_from_slice(&federation_id);
    cursor += 32;
    message[cursor..cursor + 8].copy_from_slice(&committee_epoch.to_le_bytes());
    cursor += 8;
    message[cursor..cursor + 8].copy_from_slice(&commit_ordinal.to_le_bytes());
    cursor += 8;
    message[cursor..cursor + 32].copy_from_slice(&frame_id.bytes());
    message
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactFnspV4ConsensusError {
    WrongWireLength { expected: u64, actual: u64 },
    WrongMagic,
    UnsupportedVersion(u16),
    NonZeroReserved,
    NonCanonicalAbsentPayload,
    BadOptionalTag(u8),
    BadPredecessorTag(u8),
    NonCanonicalFieldLane { lane: u64, value: u32 },
    ExactStateCommitMismatch,
    ExactStatePointInvalid,
    ZeroProtocolEpoch,
    CutoverCoordinateMismatch,
    ActivationIdentityMismatch,
    FederationMismatch,
    ZeroFrameSequence,
    FirstFramePredecessorMismatch,
    ContinuationPredecessorMismatch,
    ActivationStateMismatch,
    ReceiptPredecessorOrder,
    ExactCountOverflow,
    ExactCountStepMismatch,
    EnvelopeCoreMismatch,
    InvalidValidatorKey,
    InvalidEnvelopeSignature,
}

impl fmt::Display for ExactFnspV4ConsensusError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongWireLength { expected, actual } => {
                write!(
                    f,
                    "wrong exact-v4 wire length: expected {expected}, got {actual}"
                )
            }
            Self::WrongMagic => f.write_str("wrong exact-v4 wire magic"),
            Self::UnsupportedVersion(version) => {
                write!(f, "unsupported exact-v4 wire version {version}")
            }
            Self::NonZeroReserved => f.write_str("nonzero exact-v4 reserved bytes"),
            Self::NonCanonicalAbsentPayload => {
                f.write_str("absent exact-v4 optional field has nonzero payload")
            }
            Self::BadOptionalTag(tag) => write!(f, "bad exact-v4 optional tag {tag}"),
            Self::BadPredecessorTag(tag) => write!(f, "bad exact-v4 predecessor tag {tag}"),
            Self::NonCanonicalFieldLane { lane, value } => {
                write!(f, "non-canonical exact-v4 field lane {lane}: {value}")
            }
            Self::ExactStateCommitMismatch => f.write_str("exact-v4 FNS3 state commit mismatch"),
            Self::ExactStatePointInvalid => f.write_str("invalid exact-v4 exact state point"),
            Self::ZeroProtocolEpoch => f.write_str("exact-v4 protocol epoch zero is reserved"),
            Self::CutoverCoordinateMismatch => {
                f.write_str("exact-v4 cutover index/tail shape mismatch")
            }
            Self::ActivationIdentityMismatch => {
                f.write_str("exact-v4 frame activation identity mismatch")
            }
            Self::FederationMismatch => f.write_str("exact-v4 federation mismatch"),
            Self::ZeroFrameSequence => f.write_str("exact-v4 frame sequence zero is reserved"),
            Self::FirstFramePredecessorMismatch => {
                f.write_str("exact-v4 first frame does not link its activation")
            }
            Self::ContinuationPredecessorMismatch => {
                f.write_str("exact-v4 continuation does not link a frame")
            }
            Self::ActivationStateMismatch => {
                f.write_str("exact-v4 first frame does not begin at activation state")
            }
            Self::ReceiptPredecessorOrder => {
                f.write_str("exact-v4 per-actor receipt predecessor is not earlier")
            }
            Self::ExactCountOverflow => f.write_str("exact-v4 exact count overflow"),
            Self::ExactCountStepMismatch => f.write_str("exact-v4 exact count must advance by one"),
            Self::EnvelopeCoreMismatch => {
                f.write_str("local exact-v4 envelope does not match recomputed common core")
            }
            Self::InvalidValidatorKey => f.write_str("invalid local validator public key"),
            Self::InvalidEnvelopeSignature => {
                f.write_str("invalid local exact-v4 envelope signature")
            }
        }
    }
}

impl std::error::Error for ExactFnspV4ConsensusError {}

fn write_prefix(out: &mut [u8], magic: [u8; 4]) {
    out[..4].copy_from_slice(&magic);
    out[4..6].copy_from_slice(&WIRE_VERSION.to_le_bytes());
    // [6..8] is a mandatory zero reserved field.
}

fn require_wire(
    bytes: &[u8],
    expected: usize,
    magic: [u8; 4],
) -> Result<(), ExactFnspV4ConsensusError> {
    if bytes.len() != expected {
        return Err(ExactFnspV4ConsensusError::WrongWireLength {
            expected: u64::try_from(expected).expect("wire length fits u64"),
            actual: u64::try_from(bytes.len()).unwrap_or(u64::MAX),
        });
    }
    if bytes[..4] != magic {
        return Err(ExactFnspV4ConsensusError::WrongMagic);
    }
    let version = u16::from_le_bytes(bytes[4..6].try_into().expect("version bytes"));
    if version != WIRE_VERSION {
        return Err(ExactFnspV4ConsensusError::UnsupportedVersion(version));
    }
    if bytes[6..8] != [0, 0] {
        return Err(ExactFnspV4ConsensusError::NonZeroReserved);
    }
    Ok(())
}

fn write_u64(out: &mut [u8], cursor: &mut usize, value: u64) {
    out[*cursor..*cursor + 8].copy_from_slice(&value.to_le_bytes());
    *cursor += 8;
}

fn read_u64(bytes: &[u8], cursor: &mut usize) -> u64 {
    let value = u64::from_le_bytes(bytes[*cursor..*cursor + 8].try_into().expect("u64 bytes"));
    *cursor += 8;
    value
}

fn write_32(out: &mut [u8], cursor: &mut usize, value: [u8; 32]) {
    out[*cursor..*cursor + 32].copy_from_slice(&value);
    *cursor += 32;
}

fn read_32(bytes: &[u8], cursor: &mut usize) -> [u8; 32] {
    let value = bytes[*cursor..*cursor + 32]
        .try_into()
        .expect("32-byte field");
    *cursor += 32;
    value
}

fn write_optional_32(out: &mut [u8], cursor: &mut usize, value: Option<[u8; 32]>) {
    match value {
        None => {
            out[*cursor] = 0;
            *cursor += 33;
        }
        Some(value) => {
            out[*cursor] = 1;
            *cursor += 1;
            write_32(out, cursor, value);
        }
    }
}

fn read_optional_32(
    bytes: &[u8],
    cursor: &mut usize,
) -> Result<Option<[u8; 32]>, ExactFnspV4ConsensusError> {
    let tag = bytes[*cursor];
    *cursor += 1;
    let payload = read_32(bytes, cursor);
    match tag {
        0 if payload == [0; 32] => Ok(None),
        0 => Err(ExactFnspV4ConsensusError::NonCanonicalAbsentPayload),
        1 => Ok(Some(payload)),
        tag => Err(ExactFnspV4ConsensusError::BadOptionalTag(tag)),
    }
}

fn write_optional_receipt_predecessor(
    out: &mut [u8],
    cursor: &mut usize,
    value: Option<ExactFnspV4ReceiptPredecessor>,
) {
    match value {
        None => {
            out[*cursor] = 0;
            *cursor += 41;
        }
        Some(value) => {
            out[*cursor] = 1;
            *cursor += 1;
            write_u64(out, cursor, value.index);
            write_32(out, cursor, value.hash);
        }
    }
}

fn read_optional_receipt_predecessor(
    bytes: &[u8],
    cursor: &mut usize,
) -> Result<Option<ExactFnspV4ReceiptPredecessor>, ExactFnspV4ConsensusError> {
    let tag = bytes[*cursor];
    *cursor += 1;
    let index = read_u64(bytes, cursor);
    let hash = read_32(bytes, cursor);
    match tag {
        0 if index == 0 && hash == [0; 32] => Ok(None),
        0 => Err(ExactFnspV4ConsensusError::NonCanonicalAbsentPayload),
        1 => Ok(Some(ExactFnspV4ReceiptPredecessor { index, hash })),
        tag => Err(ExactFnspV4ConsensusError::BadOptionalTag(tag)),
    }
}

fn write_state_point(out: &mut [u8], cursor: &mut usize, point: ExactFnspV3StatePoint) {
    write_digest(out, cursor, point.root());
    write_u64(out, cursor, point.count());
    write_digest(out, cursor, point.fns3());
}

fn read_state_point(
    bytes: &[u8],
    cursor: &mut usize,
) -> Result<ExactFnspV3StatePoint, ExactFnspV4ConsensusError> {
    let root = read_digest(bytes, cursor)?;
    let count = read_u64(bytes, cursor);
    let claimed_fns3 = read_digest(bytes, cursor)?;
    let point = ExactFnspV3StatePoint::new(root, count)
        .map_err(|_| ExactFnspV4ConsensusError::ExactStatePointInvalid)?;
    if point.fns3() != claimed_fns3 {
        return Err(ExactFnspV4ConsensusError::ExactStateCommitMismatch);
    }
    Ok(point)
}

fn write_digest(out: &mut [u8], cursor: &mut usize, digest: Digest8) {
    for lane in digest {
        out[*cursor..*cursor + 4].copy_from_slice(&lane.as_u32().to_le_bytes());
        *cursor += 4;
    }
}

fn read_digest(bytes: &[u8], cursor: &mut usize) -> Result<Digest8, ExactFnspV4ConsensusError> {
    let mut digest = [BabyBear::ZERO; 8];
    for (lane, slot) in digest.iter_mut().enumerate() {
        let value = u32::from_le_bytes(
            bytes[*cursor..*cursor + 4]
                .try_into()
                .expect("field lane bytes"),
        );
        *cursor += 4;
        if value >= BABYBEAR_P {
            return Err(ExactFnspV4ConsensusError::NonCanonicalFieldLane {
                lane: u64::try_from(lane).expect("lane index fits u64"),
                value,
            });
        }
        *slot = BabyBear::new_canonical(value);
    }
    Ok(digest)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::exact_nullifier_aafi::ExactNullifierAafi;

    fn point() -> ExactFnspV3StatePoint {
        let aafi = ExactNullifierAafi::new();
        ExactFnspV3StatePoint::new(aafi.root(), aafi.count()).expect("initial point")
    }

    fn next_point(before: ExactFnspV3StatePoint, tag: u32) -> ExactFnspV3StatePoint {
        ExactFnspV3StatePoint::new([BabyBear::new_canonical(tag); 8], before.count() + 1)
            .expect("next point")
    }

    fn activation() -> ExactFnspV4ActivationCore {
        ExactFnspV4ActivationCore::new(
            4,
            [0xf4; 32],
            11,
            9,
            Some([0x99; 32]),
            point(),
            [0x71; 32],
            [0x72; 32],
        )
        .expect("activation")
    }

    fn frame(activation: &ExactFnspV4ActivationCore) -> ExactFnspV4FrameCore {
        let before = activation.exact_initial();
        ExactFnspV4FrameCore::new(
            activation,
            ExactFnspV4FrameCoreFields {
                activation_id: activation.id(),
                sequence: 1,
                predecessor: ExactFnspV4FramePredecessor::Activation(activation.id()),
                receipt_index: 9,
                receipt_hash: [0x21; 32],
                full_predecessor: Some(ExactFnspV4ReceiptPredecessor {
                    index: 7,
                    hash: [0x20; 32],
                }),
                block_id: [0xb1; 32],
                commit_ordinal: 17,
                turn_hash: [0x31; 32],
                forest_hash: [0x32; 32],
                actor: [0xa1; 32],
                federation_id: activation.federation_id(),
                full_pre_state: [0x41; 32],
                full_post_state: [0x42; 32],
                exact_before: before,
                exact_after: next_point(before, 13),
                accepted_statement_digest: [0x51; 32],
                accepted_proof_digest: [0x52; 32],
                consequence_commitment: [0x53; 32],
                output_notes_commitment: [0x54; 32],
            },
        )
        .expect("frame")
    }

    #[test]
    fn different_local_keys_share_identical_consensus_ids_but_distinct_valid_envelopes() {
        let activation = activation();
        let frame = frame(&activation);
        let activation_id = activation.id();
        let frame_id = frame.id();
        let left = LocalExactFnspV4Envelope::sign(
            &activation,
            &frame,
            &SigningKey::from_bytes(&[0x11; 32]),
        )
        .expect("left envelope");
        let right = LocalExactFnspV4Envelope::sign(
            &activation,
            &frame,
            &SigningKey::from_bytes(&[0x22; 32]),
        )
        .expect("right envelope");

        assert_eq!(activation.id(), activation_id);
        assert_eq!(frame.id(), frame_id);
        assert_eq!(left.frame_id(), right.frame_id());
        assert_eq!(left.signature_message(), right.signature_message());
        assert_ne!(left.validator_public_key(), right.validator_public_key());
        assert_ne!(left.to_canonical_bytes(), right.to_canonical_bytes());
        left.verify(&activation, &frame).expect("left verifies");
        right.verify(&activation, &frame).expect("right verifies");
    }

    #[test]
    fn mutating_common_core_changes_id_and_invalidates_old_envelope() {
        let activation = activation();
        let frame = frame(&activation);
        let envelope = LocalExactFnspV4Envelope::sign(
            &activation,
            &frame,
            &SigningKey::from_bytes(&[0x33; 32]),
        )
        .expect("envelope");
        let mut fields = frame.fields().clone();
        fields.output_notes_commitment[0] ^= 1;
        let mutated = ExactFnspV4FrameCore::new(&activation, fields).expect("mutated core");
        assert_ne!(frame.id(), mutated.id());
        assert_eq!(
            envelope.verify(&activation, &mutated),
            Err(ExactFnspV4ConsensusError::EnvelopeCoreMismatch)
        );
    }

    #[test]
    fn mutating_only_envelope_signature_never_changes_core_id() {
        let activation = activation();
        let frame = frame(&activation);
        let frame_id = frame.id();
        let envelope = LocalExactFnspV4Envelope::sign(
            &activation,
            &frame,
            &SigningKey::from_bytes(&[0x44; 32]),
        )
        .expect("envelope");
        let mut bytes = envelope.to_canonical_bytes();
        bytes[LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN - 1] ^= 1;
        let forged =
            LocalExactFnspV4Envelope::decode_canonical(&bytes).expect("structural envelope");
        assert_eq!(frame.id(), frame_id);
        assert_eq!(forged.frame_id(), frame_id);
        assert_eq!(
            forged.verify(&activation, &frame),
            Err(ExactFnspV4ConsensusError::InvalidEnvelopeSignature)
        );
    }

    #[test]
    fn fixed_width_codecs_roundtrip_and_refuse_noncanonical_bytes() {
        let activation = activation();
        let frame = frame(&activation);
        assert_eq!(
            ExactFnspV4ActivationCore::decode_canonical(&activation.to_canonical_bytes()).unwrap(),
            activation
        );
        assert_eq!(
            ExactFnspV4FrameCore::decode_canonical(&frame.to_canonical_bytes(), &activation)
                .unwrap(),
            frame
        );

        let mut trailing = activation.to_canonical_bytes().to_vec();
        trailing.push(0);
        assert!(matches!(
            ExactFnspV4ActivationCore::decode_canonical(&trailing),
            Err(ExactFnspV4ConsensusError::WrongWireLength { .. })
        ));
        let mut reserved = activation.to_canonical_bytes();
        reserved[6] = 1;
        assert_eq!(
            ExactFnspV4ActivationCore::decode_canonical(&reserved),
            Err(ExactFnspV4ConsensusError::NonZeroReserved)
        );

        let empty = ExactFnspV4ActivationCore::new(
            4,
            [0xf4; 32],
            11,
            0,
            None,
            point(),
            [0x71; 32],
            [0x72; 32],
        )
        .unwrap();
        let mut noncanonical_none = empty.to_canonical_bytes();
        // Prefix + protocol epoch + federation + committee epoch + cursor + option tag.
        noncanonical_none[65] = 1;
        assert_eq!(
            ExactFnspV4ActivationCore::decode_canonical(&noncanonical_none),
            Err(ExactFnspV4ConsensusError::NonCanonicalAbsentPayload)
        );
    }

    #[test]
    fn cross_federation_or_activation_substitution_refuses() {
        let activation = activation();
        let frame = frame(&activation);
        let other = ExactFnspV4ActivationCore::new(
            activation.protocol_epoch(),
            [0xee; 32],
            activation.committee_epoch(),
            activation.receipt_cutover_next_index(),
            activation.receipt_cutover_tail_hash(),
            activation.exact_initial(),
            activation.verifier_program_id(),
            activation.transition_program_id(),
        )
        .unwrap();
        let envelope = LocalExactFnspV4Envelope::sign(
            &activation,
            &frame,
            &SigningKey::from_bytes(&[0x55; 32]),
        )
        .unwrap();
        assert_eq!(
            envelope.verify(&other, &frame),
            Err(ExactFnspV4ConsensusError::ActivationIdentityMismatch)
        );
    }
}
