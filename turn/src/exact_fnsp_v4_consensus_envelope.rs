//! Signer-independent exact-FNSP consensus cores and local validator envelopes.
//!
//! FNSP-v3 activation identity includes one node-local executor public key.  That format is useful
//! as solo-node recovery evidence, but it is not a deterministic federation consensus coordinate:
//! validators with distinct local keys hash distinct activation preimages.  V4 separates:
//!
//! * fixed-width [`ExactFnspV4ActivationCore`] and [`ExactFnspV4FrameCore`] records, whose IDs contain
//!   no local signer identity, signature, receipt encoding, or wall-clock field; and
//! * [`HybridLocalExactFnspV4Envelope`], an Ed25519 AND ML-DSA-65 observation of one already-fixed
//!   frame ID at one federation/committee epoch/commit ordinal.
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
const RECEIPT_MAGIC: [u8; 4] = *b"EXR4";
const FRAME_MAGIC: [u8; 4] = *b"EXF4";
const ENVELOPE_MAGIC: [u8; 4] = *b"EXE4";
const WIRE_VERSION: u16 = 1;

const ACTIVATION_ID_DOMAIN: &str = "dregg-exact-fnsp-v4-activation-core-v1";
const RECEIPT_ID_DOMAIN: &str = "dregg-exact-fnsp-v4-consensus-receipt-core-v1";
const FRAME_ID_DOMAIN: &str = "dregg-exact-fnsp-v4-frame-core-v1";
const LOCAL_ENVELOPE_SIGNATURE_DOMAIN: &[u8] = b"dregg-exact-fnsp-v4-local-envelope-signature-v1:";
const LOCAL_ENVELOPE_PQ_CONTEXT: &[u8] = b"dregg-exact-fnsp-v4-local-envelope-pq-v1";

const PREFIX_LEN: usize = 8;
pub const EXACT_FNSP_V4_ACTIVATION_CORE_LEN: usize = 233;
pub const EXACT_RECEIPT_CORE_V4_LEN: usize = 304;
pub const EXACT_FNSP_V4_FRAME_CORE_LEN: usize = 642;
pub const HYBRID_LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN: usize =
    184 + dregg_pq::ML_DSA_PK_LEN + dregg_pq::ML_DSA_SIG_LEN;
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

/// Typed ID of a deterministic, signature-free exact receipt projection.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExactReceiptIdV4([u8; 32]);

impl ExactReceiptIdV4 {
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
        if federation_id == [0; 32] {
            return Err(ExactFnspV4ConsensusError::ZeroFederationId);
        }
        if verifier_program_id == [0; 32] {
            return Err(ExactFnspV4ConsensusError::ZeroVerifierProgramId);
        }
        if transition_program_id == [0; 32] {
            return Err(ExactFnspV4ConsensusError::ZeroTransitionProgramId);
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

/// Deterministic receipt projection embedded in every exact-v4 frame.
///
/// The old [`crate::TurnReceipt::receipt_hash`] includes `TurnReceipt::timestamp`, which production
/// executors currently seed from their local wall clock.  It therefore cannot be promoted to a
/// federation consensus coordinate.  This fixed record has no timestamp, signature, signer key, or
/// local receipt bytes.  If a future protocol needs time, it must add an explicitly finalized
/// consensus block time in a new wire version.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactReceiptCoreV4 {
    block_id: [u8; 32],
    commit_ordinal: u64,
    turn_hash: [u8; 32],
    forest_hash: [u8; 32],
    actor: [u8; 32],
    federation_id: [u8; 32],
    full_pre_state: [u8; 32],
    full_post_state: [u8; 32],
    semantic_outcome_commitment: [u8; 32],
    output_notes_commitment: [u8; 32],
}

impl ExactReceiptCoreV4 {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        block_id: [u8; 32],
        commit_ordinal: u64,
        turn_hash: [u8; 32],
        forest_hash: [u8; 32],
        actor: [u8; 32],
        federation_id: [u8; 32],
        full_pre_state: [u8; 32],
        full_post_state: [u8; 32],
        semantic_outcome_commitment: [u8; 32],
        output_notes_commitment: [u8; 32],
    ) -> Result<Self, ExactFnspV4ConsensusError> {
        if federation_id == [0; 32] {
            return Err(ExactFnspV4ConsensusError::ZeroFederationId);
        }
        Ok(Self {
            block_id,
            commit_ordinal,
            turn_hash,
            forest_hash,
            actor,
            federation_id,
            full_pre_state,
            full_post_state,
            semantic_outcome_commitment,
            output_notes_commitment,
        })
    }

    pub const fn block_id(&self) -> [u8; 32] {
        self.block_id
    }

    pub const fn commit_ordinal(&self) -> u64 {
        self.commit_ordinal
    }

    pub const fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }

    pub fn id(&self) -> ExactReceiptIdV4 {
        let mut hasher = blake3::Hasher::new_derive_key(RECEIPT_ID_DOMAIN);
        hasher.update(&self.to_canonical_bytes());
        ExactReceiptIdV4(*hasher.finalize().as_bytes())
    }

    pub fn to_canonical_bytes(&self) -> [u8; EXACT_RECEIPT_CORE_V4_LEN] {
        let mut out = [0u8; EXACT_RECEIPT_CORE_V4_LEN];
        write_prefix(&mut out, RECEIPT_MAGIC);
        let mut cursor = PREFIX_LEN;
        write_32(&mut out, &mut cursor, self.block_id);
        write_u64(&mut out, &mut cursor, self.commit_ordinal);
        write_32(&mut out, &mut cursor, self.turn_hash);
        write_32(&mut out, &mut cursor, self.forest_hash);
        write_32(&mut out, &mut cursor, self.actor);
        write_32(&mut out, &mut cursor, self.federation_id);
        write_32(&mut out, &mut cursor, self.full_pre_state);
        write_32(&mut out, &mut cursor, self.full_post_state);
        write_32(&mut out, &mut cursor, self.semantic_outcome_commitment);
        write_32(&mut out, &mut cursor, self.output_notes_commitment);
        debug_assert_eq!(cursor, EXACT_RECEIPT_CORE_V4_LEN);
        out
    }

    pub fn decode_canonical(bytes: &[u8]) -> Result<Self, ExactFnspV4ConsensusError> {
        require_wire(bytes, EXACT_RECEIPT_CORE_V4_LEN, RECEIPT_MAGIC)?;
        let mut cursor = PREFIX_LEN;
        let block_id = read_32(bytes, &mut cursor);
        let commit_ordinal = read_u64(bytes, &mut cursor);
        let turn_hash = read_32(bytes, &mut cursor);
        let forest_hash = read_32(bytes, &mut cursor);
        let actor = read_32(bytes, &mut cursor);
        let federation_id = read_32(bytes, &mut cursor);
        let full_pre_state = read_32(bytes, &mut cursor);
        let full_post_state = read_32(bytes, &mut cursor);
        let semantic_outcome_commitment = read_32(bytes, &mut cursor);
        let output_notes_commitment = read_32(bytes, &mut cursor);
        debug_assert_eq!(cursor, EXACT_RECEIPT_CORE_V4_LEN);
        Self::new(
            block_id,
            commit_ordinal,
            turn_hash,
            forest_hash,
            actor,
            federation_id,
            full_pre_state,
            full_post_state,
            semantic_outcome_commitment,
            output_notes_commitment,
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
    pub id: ExactReceiptIdV4,
}

/// Caller-carried fields used to construct a validated fixed-width frame core.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactFnspV4FrameCoreFields {
    pub activation_id: ExactFnspV4ActivationId,
    pub sequence: u64,
    pub predecessor: ExactFnspV4FramePredecessor,
    pub receipt_index: u64,
    pub receipt: ExactReceiptCoreV4,
    pub full_predecessor: Option<ExactFnspV4ReceiptPredecessor>,
    pub exact_before: ExactFnspV3StatePoint,
    pub exact_after: ExactFnspV3StatePoint,
    pub accepted_statement_digest: [u8; 32],
    pub accepted_proof_digest: [u8; 32],
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
        if fields.receipt.federation_id() != activation.federation_id {
            return Err(ExactFnspV4ConsensusError::FederationMismatch);
        }
        if fields.sequence == 0 {
            return Err(ExactFnspV4ConsensusError::ZeroFrameSequence);
        }
        if fields.receipt_index < activation.receipt_cutover_next_index {
            return Err(ExactFnspV4ConsensusError::ReceiptBeforeCutover);
        }
        match (fields.sequence, fields.predecessor) {
            (1, ExactFnspV4FramePredecessor::Activation(id)) if id == activation.id() => {
                // `sequence` is the epoch-relative frame number, independent of the physical exact
                // accumulator generation/count inherited at activation.  Its first receipt is
                // exactly the activated durable receipt cutover coordinate.
                if fields.receipt_index != activation.receipt_cutover_next_index {
                    return Err(ExactFnspV4ConsensusError::FirstReceiptIndexMismatch);
                }
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
        let receipt = fields.receipt.to_canonical_bytes();
        out[cursor..cursor + EXACT_RECEIPT_CORE_V4_LEN].copy_from_slice(&receipt);
        cursor += EXACT_RECEIPT_CORE_V4_LEN;
        write_optional_receipt_predecessor(&mut out, &mut cursor, fields.full_predecessor);
        write_state_point(&mut out, &mut cursor, fields.exact_before);
        write_state_point(&mut out, &mut cursor, fields.exact_after);
        write_32(&mut out, &mut cursor, fields.accepted_statement_digest);
        write_32(&mut out, &mut cursor, fields.accepted_proof_digest);
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
        let receipt = ExactReceiptCoreV4::decode_canonical(
            &bytes[cursor..cursor + EXACT_RECEIPT_CORE_V4_LEN],
        )?;
        cursor += EXACT_RECEIPT_CORE_V4_LEN;
        let full_predecessor = read_optional_receipt_predecessor(bytes, &mut cursor)?;
        let exact_before = read_state_point(bytes, &mut cursor)?;
        let exact_after = read_state_point(bytes, &mut cursor)?;
        let accepted_statement_digest = read_32(bytes, &mut cursor);
        let accepted_proof_digest = read_32(bytes, &mut cursor);
        debug_assert_eq!(cursor, EXACT_FNSP_V4_FRAME_CORE_LEN);
        Self::new(
            activation,
            ExactFnspV4FrameCoreFields {
                activation_id,
                sequence,
                predecessor,
                receipt_index,
                receipt,
                full_predecessor,
                exact_before,
                exact_after,
                accepted_statement_digest,
                accepted_proof_digest,
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
        if self.0.receipt.federation_id() != activation.federation_id {
            return Err(ExactFnspV4ConsensusError::FederationMismatch);
        }
        Ok(())
    }
}

/// Independently enrolled hybrid identity expected for one validator.
///
/// Verification takes this value from federation policy; the public keys carried in an envelope
/// never authorize themselves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridExactFnspV4ValidatorIdentity {
    pub ed25519: [u8; 32],
    pub ml_dsa_65: [u8; dregg_pq::ML_DSA_PK_LEN],
}

/// One validator's hybrid observation of a fixed common frame ID.
///
/// Both signatures cover the same message.  The validator keys/signatures are outside both common
/// core encodings.  This is not a committee or threshold certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridLocalExactFnspV4Envelope {
    federation_id: [u8; 32],
    committee_epoch: u64,
    commit_ordinal: u64,
    frame_id: ExactFnspV4FrameId,
    validator_ed25519_public_key: [u8; 32],
    validator_ml_dsa_public_key: [u8; dregg_pq::ML_DSA_PK_LEN],
    ed25519_signature: [u8; 64],
    ml_dsa_signature: [u8; dregg_pq::ML_DSA_SIG_LEN],
}

impl HybridLocalExactFnspV4Envelope {
    /// Derive both validator keys from the same seed and sign both halves.
    pub fn sign_from_seed(
        activation: &ExactFnspV4ActivationCore,
        frame: &ExactFnspV4FrameCore,
        seed: &[u8; 32],
    ) -> Result<Self, ExactFnspV4ConsensusError> {
        frame.validate_scope(activation)?;
        let frame_id = frame.id();
        let message = local_envelope_signature_message(
            activation.federation_id,
            activation.committee_epoch,
            frame.0.receipt.commit_ordinal(),
            frame_id,
        );
        let classical = SigningKey::from_bytes(seed);
        let pq = dregg_pq::MlDsaKey::from_ed25519_seed(seed);
        let validator_ml_dsa_public_key = pq
            .public_bytes()
            .try_into()
            .map_err(|_| ExactFnspV4ConsensusError::PqPrimitiveLengthMismatch)?;
        let ml_dsa_signature = pq
            .try_sign_deterministic(LOCAL_ENVELOPE_PQ_CONTEXT, &message)
            .ok_or(ExactFnspV4ConsensusError::PqSigningFailed)?
            .try_into()
            .map_err(|_| ExactFnspV4ConsensusError::PqPrimitiveLengthMismatch)?;
        Ok(Self {
            federation_id: activation.federation_id,
            committee_epoch: activation.committee_epoch,
            commit_ordinal: frame.0.receipt.commit_ordinal(),
            frame_id,
            validator_ed25519_public_key: classical.verifying_key().to_bytes(),
            validator_ml_dsa_public_key,
            ed25519_signature: classical.sign(&message).to_bytes(),
            ml_dsa_signature,
        })
    }

    /// Verify BOTH signature halves against independently expected keys.
    pub fn verify_against(
        &self,
        activation: &ExactFnspV4ActivationCore,
        frame: &ExactFnspV4FrameCore,
        expected: &HybridExactFnspV4ValidatorIdentity,
    ) -> Result<(), ExactFnspV4ConsensusError> {
        frame.validate_scope(activation)?;
        if self.federation_id != activation.federation_id
            || self.committee_epoch != activation.committee_epoch
            || self.commit_ordinal != frame.0.receipt.commit_ordinal()
            || self.frame_id != frame.id()
        {
            return Err(ExactFnspV4ConsensusError::EnvelopeCoreMismatch);
        }
        if self.validator_ed25519_public_key != expected.ed25519
            || self.validator_ml_dsa_public_key != expected.ml_dsa_65
        {
            return Err(ExactFnspV4ConsensusError::UnexpectedValidatorIdentity);
        }
        let message = self.signature_message();
        let key = VerifyingKey::from_bytes(&expected.ed25519)
            .map_err(|_| ExactFnspV4ConsensusError::InvalidValidatorKey)?;
        let signature = ed25519_dalek::Signature::from_bytes(&self.ed25519_signature);
        key.verify_strict(&message, &signature)
            .map_err(|_| ExactFnspV4ConsensusError::InvalidEnvelopeClassicalSignature)?;
        if !dregg_pq::ml_dsa_verify(
            &expected.ml_dsa_65,
            LOCAL_ENVELOPE_PQ_CONTEXT,
            &message,
            &self.ml_dsa_signature,
        ) {
            return Err(ExactFnspV4ConsensusError::InvalidEnvelopePqSignature);
        }
        Ok(())
    }

    pub const fn frame_id(&self) -> ExactFnspV4FrameId {
        self.frame_id
    }

    pub fn validator_identity(&self) -> HybridExactFnspV4ValidatorIdentity {
        HybridExactFnspV4ValidatorIdentity {
            ed25519: self.validator_ed25519_public_key,
            ml_dsa_65: self.validator_ml_dsa_public_key,
        }
    }

    pub fn signature_message(&self) -> [u8; LOCAL_ENVELOPE_MESSAGE_LEN] {
        local_envelope_signature_message(
            self.federation_id,
            self.committee_epoch,
            self.commit_ordinal,
            self.frame_id,
        )
    }

    pub fn to_canonical_bytes(&self) -> [u8; HYBRID_LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN] {
        let mut out = [0u8; HYBRID_LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN];
        write_prefix(&mut out, ENVELOPE_MAGIC);
        let mut cursor = PREFIX_LEN;
        write_32(&mut out, &mut cursor, self.federation_id);
        write_u64(&mut out, &mut cursor, self.committee_epoch);
        write_u64(&mut out, &mut cursor, self.commit_ordinal);
        write_32(&mut out, &mut cursor, self.frame_id.bytes());
        write_32(&mut out, &mut cursor, self.validator_ed25519_public_key);
        out[cursor..cursor + dregg_pq::ML_DSA_PK_LEN]
            .copy_from_slice(&self.validator_ml_dsa_public_key);
        cursor += dregg_pq::ML_DSA_PK_LEN;
        out[cursor..cursor + 64].copy_from_slice(&self.ed25519_signature);
        cursor += 64;
        out[cursor..cursor + dregg_pq::ML_DSA_SIG_LEN].copy_from_slice(&self.ml_dsa_signature);
        cursor += dregg_pq::ML_DSA_SIG_LEN;
        debug_assert_eq!(cursor, HYBRID_LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN);
        out
    }

    pub fn decode_canonical(bytes: &[u8]) -> Result<Self, ExactFnspV4ConsensusError> {
        require_wire(
            bytes,
            HYBRID_LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN,
            ENVELOPE_MAGIC,
        )?;
        let mut cursor = PREFIX_LEN;
        let federation_id = read_32(bytes, &mut cursor);
        let committee_epoch = read_u64(bytes, &mut cursor);
        let commit_ordinal = read_u64(bytes, &mut cursor);
        let frame_id = ExactFnspV4FrameId(read_32(bytes, &mut cursor));
        let validator_ed25519_public_key = read_32(bytes, &mut cursor);
        let mut validator_ml_dsa_public_key = [0u8; dregg_pq::ML_DSA_PK_LEN];
        validator_ml_dsa_public_key
            .copy_from_slice(&bytes[cursor..cursor + dregg_pq::ML_DSA_PK_LEN]);
        cursor += dregg_pq::ML_DSA_PK_LEN;
        let mut ed25519_signature = [0u8; 64];
        ed25519_signature.copy_from_slice(&bytes[cursor..cursor + 64]);
        cursor += 64;
        let mut ml_dsa_signature = [0u8; dregg_pq::ML_DSA_SIG_LEN];
        ml_dsa_signature.copy_from_slice(&bytes[cursor..cursor + dregg_pq::ML_DSA_SIG_LEN]);
        cursor += dregg_pq::ML_DSA_SIG_LEN;
        debug_assert_eq!(cursor, HYBRID_LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN);
        Ok(Self {
            federation_id,
            committee_epoch,
            commit_ordinal,
            frame_id,
            validator_ed25519_public_key,
            validator_ml_dsa_public_key,
            ed25519_signature,
            ml_dsa_signature,
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
    ZeroFederationId,
    ZeroVerifierProgramId,
    ZeroTransitionProgramId,
    CutoverCoordinateMismatch,
    ActivationIdentityMismatch,
    FederationMismatch,
    ZeroFrameSequence,
    ReceiptBeforeCutover,
    FirstReceiptIndexMismatch,
    FirstFramePredecessorMismatch,
    ContinuationPredecessorMismatch,
    ActivationStateMismatch,
    ReceiptPredecessorOrder,
    ExactCountOverflow,
    ExactCountStepMismatch,
    EnvelopeCoreMismatch,
    UnexpectedValidatorIdentity,
    InvalidValidatorKey,
    InvalidEnvelopeClassicalSignature,
    InvalidEnvelopePqSignature,
    PqSigningFailed,
    PqPrimitiveLengthMismatch,
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
            Self::ZeroFederationId => f.write_str("exact-v4 federation ID cannot be zero"),
            Self::ZeroVerifierProgramId => {
                f.write_str("exact-v4 verifier program ID cannot be zero")
            }
            Self::ZeroTransitionProgramId => {
                f.write_str("exact-v4 transition program ID cannot be zero")
            }
            Self::CutoverCoordinateMismatch => {
                f.write_str("exact-v4 cutover index/tail shape mismatch")
            }
            Self::ActivationIdentityMismatch => {
                f.write_str("exact-v4 frame activation identity mismatch")
            }
            Self::FederationMismatch => f.write_str("exact-v4 federation mismatch"),
            Self::ZeroFrameSequence => f.write_str("exact-v4 frame sequence zero is reserved"),
            Self::ReceiptBeforeCutover => {
                f.write_str("exact-v4 frame receipt precedes activation cutover")
            }
            Self::FirstReceiptIndexMismatch => {
                f.write_str("exact-v4 first frame receipt is not the activation cutover index")
            }
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
            Self::UnexpectedValidatorIdentity => {
                f.write_str("local exact-v4 envelope keys do not match enrolled validator identity")
            }
            Self::InvalidValidatorKey => f.write_str("invalid local validator public key"),
            Self::InvalidEnvelopeClassicalSignature => {
                f.write_str("invalid local exact-v4 Ed25519 envelope signature")
            }
            Self::InvalidEnvelopePqSignature => {
                f.write_str("invalid local exact-v4 ML-DSA-65 envelope signature")
            }
            Self::PqSigningFailed => f.write_str("local exact-v4 ML-DSA-65 signing failed closed"),
            Self::PqPrimitiveLengthMismatch => {
                f.write_str("local exact-v4 ML-DSA primitive returned a wrong-length object")
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
            write_32(out, cursor, value.id.bytes());
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
        1 => Ok(Some(ExactFnspV4ReceiptPredecessor {
            index,
            id: ExactReceiptIdV4(hash),
        })),
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

    fn receipt(activation: &ExactFnspV4ActivationCore) -> ExactReceiptCoreV4 {
        ExactReceiptCoreV4::new(
            [0xb1; 32],
            17,
            [0x31; 32],
            [0x32; 32],
            [0xa1; 32],
            activation.federation_id(),
            [0x41; 32],
            [0x42; 32],
            [0x53; 32],
            [0x54; 32],
        )
        .expect("receipt")
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
                receipt: receipt(activation),
                full_predecessor: Some(ExactFnspV4ReceiptPredecessor {
                    index: 7,
                    id: ExactReceiptIdV4([0x20; 32]),
                }),
                exact_before: before,
                exact_after: next_point(before, 13),
                accepted_statement_digest: [0x51; 32],
                accepted_proof_digest: [0x52; 32],
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
        let left = HybridLocalExactFnspV4Envelope::sign_from_seed(&activation, &frame, &[0x11; 32])
            .expect("left envelope");
        let right =
            HybridLocalExactFnspV4Envelope::sign_from_seed(&activation, &frame, &[0x22; 32])
                .expect("right envelope");
        let left_identity = left.validator_identity();
        let right_identity = right.validator_identity();

        assert_eq!(activation.id(), activation_id);
        assert_eq!(frame.id(), frame_id);
        assert_eq!(left.frame_id(), right.frame_id());
        assert_eq!(left.signature_message(), right.signature_message());
        assert_ne!(left_identity, right_identity);
        assert_ne!(left.to_canonical_bytes(), right.to_canonical_bytes());
        left.verify_against(&activation, &frame, &left_identity)
            .expect("left verifies");
        right
            .verify_against(&activation, &frame, &right_identity)
            .expect("right verifies");
    }

    #[test]
    fn mutating_common_core_changes_id_and_invalidates_old_envelope() {
        let activation = activation();
        let frame = frame(&activation);
        let envelope =
            HybridLocalExactFnspV4Envelope::sign_from_seed(&activation, &frame, &[0x33; 32])
                .expect("envelope");
        let identity = envelope.validator_identity();
        let mut fields = frame.fields().clone();
        fields.receipt.output_notes_commitment[0] ^= 1;
        let mutated = ExactFnspV4FrameCore::new(&activation, fields).expect("mutated core");
        assert_ne!(frame.id(), mutated.id());
        assert_eq!(
            envelope.verify_against(&activation, &mutated, &identity),
            Err(ExactFnspV4ConsensusError::EnvelopeCoreMismatch)
        );
    }

    #[test]
    fn both_signature_halves_are_required_and_neither_changes_core_id() {
        let activation = activation();
        let frame = frame(&activation);
        let frame_id = frame.id();
        let envelope =
            HybridLocalExactFnspV4Envelope::sign_from_seed(&activation, &frame, &[0x44; 32])
                .expect("envelope");
        let identity = envelope.validator_identity();
        let mut pq_forged_bytes = envelope.to_canonical_bytes();
        pq_forged_bytes[HYBRID_LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN - 1] ^= 1;
        let pq_forged = HybridLocalExactFnspV4Envelope::decode_canonical(&pq_forged_bytes)
            .expect("structural envelope");
        assert_eq!(frame.id(), frame_id);
        assert_eq!(pq_forged.frame_id(), frame_id);
        assert_eq!(
            pq_forged.verify_against(&activation, &frame, &identity),
            Err(ExactFnspV4ConsensusError::InvalidEnvelopePqSignature)
        );

        let mut classical_forged_bytes = envelope.to_canonical_bytes();
        let classical_signature_offset =
            PREFIX_LEN + 32 + 8 + 8 + 32 + 32 + dregg_pq::ML_DSA_PK_LEN;
        classical_forged_bytes[classical_signature_offset] ^= 1;
        let classical_forged =
            HybridLocalExactFnspV4Envelope::decode_canonical(&classical_forged_bytes).unwrap();
        assert_eq!(
            classical_forged.verify_against(&activation, &frame, &identity),
            Err(ExactFnspV4ConsensusError::InvalidEnvelopeClassicalSignature)
        );

        assert!(matches!(
            HybridLocalExactFnspV4Envelope::decode_canonical(
                &envelope.to_canonical_bytes()[..HYBRID_LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN - 1]
            ),
            Err(ExactFnspV4ConsensusError::WrongWireLength { .. })
        ));
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
            ExactReceiptCoreV4::decode_canonical(&frame.fields().receipt.to_canonical_bytes())
                .unwrap(),
            frame.fields().receipt
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
    fn local_wall_clock_and_signature_bytes_cannot_enter_consensus_receipt_id() {
        let activation = activation();
        let core = receipt(&activation);
        let mut left = crate::TurnReceipt {
            timestamp: 10,
            ..crate::TurnReceipt::default()
        };
        let mut right = left.clone();
        right.timestamp = 99;
        left.executor_signature = Some(vec![1; 64]);
        right.executor_signature = Some(vec![2; 64]);
        assert_ne!(left.receipt_hash(), right.receipt_hash());
        assert_eq!(core.id(), receipt(&activation).id());
    }

    #[test]
    fn zero_identity_pins_and_pre_cutover_frames_refuse() {
        let exact = point();
        assert_eq!(
            ExactFnspV4ActivationCore::new(4, [0xf4; 32], 11, 0, None, exact, [0; 32], [0x72; 32]),
            Err(ExactFnspV4ConsensusError::ZeroVerifierProgramId)
        );
        assert_eq!(
            ExactFnspV4ActivationCore::new(4, [0xf4; 32], 11, 0, None, exact, [0x71; 32], [0; 32]),
            Err(ExactFnspV4ConsensusError::ZeroTransitionProgramId)
        );
        let activation = activation();
        let mut fields = frame(&activation).fields().clone();
        fields.receipt_index = activation.receipt_cutover_next_index() - 1;
        assert_eq!(
            ExactFnspV4FrameCore::new(&activation, fields),
            Err(ExactFnspV4ConsensusError::ReceiptBeforeCutover)
        );
    }

    #[test]
    fn epoch_relative_sequence_one_is_independent_of_nonempty_exact_generation() {
        let inherited = ExactFnspV3StatePoint::new([BabyBear::new_canonical(19); 8], 41).unwrap();
        let activation = ExactFnspV4ActivationCore::new(
            4,
            [0xf4; 32],
            11,
            9,
            Some([0x99; 32]),
            inherited,
            [0x71; 32],
            [0x72; 32],
        )
        .unwrap();
        let built = frame(&activation);
        assert_eq!(built.fields().sequence, 1);
        assert_eq!(built.fields().exact_before.count(), 41);
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
        let envelope =
            HybridLocalExactFnspV4Envelope::sign_from_seed(&activation, &frame, &[0x55; 32])
                .unwrap();
        let identity = envelope.validator_identity();
        assert_eq!(
            envelope.verify_against(&other, &frame, &identity),
            Err(ExactFnspV4ConsensusError::ActivationIdentityMismatch)
        );
    }
}
