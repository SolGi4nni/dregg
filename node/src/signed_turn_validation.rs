//! One application-payload admission predicate for every `SignedTurn` ingress.
//!
//! Consensus authentication proves which validator carried a payload; it does
//! not authorize the payload's agent.  HTTP admission, finalized-block
//! execution, and the PostgreSQL drainer therefore call this module before any
//! ledger mutation.  Keeping the predicate here prevents a new transport from
//! accidentally implementing a weaker subset.

use dregg_sdk::SignedTurn;
use dregg_turn::TurnExecutor;
use serde::{Deserialize, Serialize};

/// A strict wire-decoding failure for the outer application envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SignedTurnDecodeError {
    Malformed(String),
    TrailingBytes { count: usize },
}

impl SignedTurnDecodeError {
    pub const fn code(&self) -> &'static str {
        match self {
            Self::Malformed(_) => "malformed-signed-turn",
            Self::TrailingBytes { .. } => "trailing-signed-turn-bytes",
        }
    }
}

impl core::fmt::Display for SignedTurnDecodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Malformed(error) => write!(f, "malformed SignedTurn bytes: {error}"),
            Self::TrailingBytes { count } => {
                write!(f, "trailing bytes after SignedTurn envelope: {count}")
            }
        }
    }
}

impl std::error::Error for SignedTurnDecodeError {}

/// Decode exactly one `SignedTurn`, consuming the complete transport payload.
/// `postcard::from_bytes` currently accepts a valid prefix and ignores a suffix;
/// every mutation ingress uses this strict wrapper so no transport can disagree
/// about the signed envelope's canonical boundary.
pub fn decode_signed_turn(bytes: &[u8]) -> Result<SignedTurn, SignedTurnDecodeError> {
    let (signed, remainder) = postcard::take_from_bytes(bytes)
        .map_err(|error| SignedTurnDecodeError::Malformed(error.to_string()))?;
    if !remainder.is_empty() {
        return Err(SignedTurnDecodeError::TrailingBytes {
            count: remainder.len(),
        });
    }
    Ok(signed)
}

/// A stable, transport-independent reason a `SignedTurn` failed admission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SignedTurnValidationError {
    InvalidEd25519Signature,
    AgentSignerMismatch,
    PqSignatureRequired,
    IncompletePqEnvelope,
    PqIdentityNotEnrolled,
    EnrolledPqSignerMismatch,
    LiveAgentSignerMismatch,
    StalePqIdentityEpoch { enrolled: u64, live: u64 },
    SubstitutedPqPublicKey,
    InvalidPqSignature,
}

impl SignedTurnValidationError {
    /// Stable machine code used by durable finalized-payload rejection records.
    pub const fn code(&self) -> &'static str {
        match self {
            Self::InvalidEd25519Signature => "invalid-ed25519-signature",
            Self::AgentSignerMismatch => "agent-signer-mismatch",
            Self::PqSignatureRequired => "pq-signature-required",
            Self::IncompletePqEnvelope => "incomplete-pq-envelope",
            Self::PqIdentityNotEnrolled => "pq-identity-not-enrolled",
            Self::EnrolledPqSignerMismatch => "enrolled-pq-signer-mismatch",
            Self::LiveAgentSignerMismatch => "live-agent-signer-mismatch",
            Self::StalePqIdentityEpoch { .. } => "stale-pq-identity-epoch",
            Self::SubstitutedPqPublicKey => "substituted-pq-public-key",
            Self::InvalidPqSignature => "invalid-pq-signature",
        }
    }
}

impl core::fmt::Display for SignedTurnValidationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidEd25519Signature => f.write_str("invalid turn signature"),
            Self::AgentSignerMismatch => {
                f.write_str("turn agent does not match signer default cell")
            }
            Self::PqSignatureRequired => {
                f.write_str("post-quantum turn signature required but absent")
            }
            Self::IncompletePqEnvelope => {
                f.write_str("post-quantum turn signature and public key must both be present")
            }
            Self::PqIdentityNotEnrolled => {
                f.write_str("required post-quantum signer identity is not independently enrolled")
            }
            Self::EnrolledPqSignerMismatch => {
                f.write_str("enrolled post-quantum identity does not bind the outer Ed25519 signer")
            }
            Self::LiveAgentSignerMismatch => {
                f.write_str("live agent identity does not bind the outer Ed25519 signer")
            }
            Self::StalePqIdentityEpoch { enrolled, live } => write!(
                f,
                "enrolled post-quantum identity epoch {enrolled} is stale for live agent epoch {live}"
            ),
            Self::SubstitutedPqPublicKey => f.write_str(
                "carried post-quantum signer does not match the independently enrolled identity",
            ),
            Self::InvalidPqSignature => f.write_str("invalid post-quantum turn signature"),
        }
    }
}

impl std::error::Error for SignedTurnValidationError {}

/// Result of complete validation.  Returning the already-computed hash keeps
/// every caller on the exact bytes both signature halves authenticated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValidatedSignedTurn {
    pub turn_hash: [u8; 32],
}

/// Validate the complete outer `SignedTurn` perimeter.
///
/// `live_agent` is independently loaded node state, never reconstructed from
/// the envelope.  The executor's PQ registry is likewise host-fed by
/// `executor_setup`; this function never enrolls a carried key.  Required-PQ
/// mode therefore fails closed when no enrollment exists.  The explicit
/// unaudited test/library mode (`require_pq == false`) may exercise an unenrolled
/// optional PQ half while still rejecting a malformed present half. Native node
/// admission requires PQ and never enters that branch.
pub fn validate_signed_turn(
    signed: &SignedTurn,
    executor: &TurnExecutor,
    live_agent: Option<&dregg_cell::Cell>,
) -> Result<ValidatedSignedTurn, SignedTurnValidationError> {
    let turn_hash = signed.turn.hash();
    if !signed.signer.verify(&turn_hash, &signed.signature) {
        return Err(SignedTurnValidationError::InvalidEd25519Signature);
    }

    let default_token_id = *blake3::hash(b"default").as_bytes();
    let expected_agent = dregg_cell::CellId::derive_raw(&signed.signer.0, &default_token_id);
    if signed.turn.agent != expected_agent {
        return Err(SignedTurnValidationError::AgentSignerMismatch);
    }

    let has_pq_signature = !signed.pq_signature.is_empty();
    let has_pq_public_key = !signed.pq_signer.is_empty();
    if has_pq_signature != has_pq_public_key {
        return Err(SignedTurnValidationError::IncompletePqEnvelope);
    }
    if !has_pq_signature {
        return if executor.require_pq() {
            Err(SignedTurnValidationError::PqSignatureRequired)
        } else {
            Ok(ValidatedSignedTurn { turn_hash })
        };
    }

    let enrolled = executor.enrolled_pq_identity(&expected_agent);
    let verification_key: &[u8] = if let Some(enrolled) = enrolled.as_ref() {
        if enrolled.target_ed25519 != signed.signer.0 {
            return Err(SignedTurnValidationError::EnrolledPqSignerMismatch);
        }
        if let Some(cell) = live_agent {
            if *cell.public_key() != signed.signer.0 {
                return Err(SignedTurnValidationError::LiveAgentSignerMismatch);
            }
            let live_epoch = cell.state.delegation_epoch();
            if enrolled.epoch != live_epoch {
                return Err(SignedTurnValidationError::StalePqIdentityEpoch {
                    enrolled: enrolled.epoch,
                    live: live_epoch,
                });
            }
        }
        if enrolled.public_key.as_slice() != signed.pq_signer.as_slice() {
            return Err(SignedTurnValidationError::SubstitutedPqPublicKey);
        }
        enrolled.public_key.as_slice()
    } else if executor.require_pq() {
        return Err(SignedTurnValidationError::PqIdentityNotEnrolled);
    } else {
        // Explicit unaudited test/library mode only: the carried key has no
        // independent authority, but a present signature must still verify
        // rather than fail open.
        signed.pq_signer.as_slice()
    };

    if !dregg_turn::pq::ml_dsa_verify(verification_key, &turn_hash, &signed.pq_signature) {
        return Err(SignedTurnValidationError::InvalidPqSignature);
    }

    Ok(ValidatedSignedTurn { turn_hash })
}

/// Versioned durable record for a consensus-finalized payload that the
/// application predicate refused.  It deliberately contains only deterministic
/// inputs/codes: no wall clock, local error formatting, or validator-local data.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FinalizedPayloadRejectionRecord {
    pub version: u8,
    pub block_id: [u8; 32],
    pub payload_hash: [u8; 32],
    pub turn_hash: Option<[u8; 32]>,
    pub reason_code: String,
}

impl FinalizedPayloadRejectionRecord {
    pub const VERSION: u8 = 1;

    pub fn new(
        block_id: [u8; 32],
        payload: &[u8],
        turn_hash: Option<[u8; 32]>,
        reason_code: impl Into<String>,
    ) -> Self {
        Self {
            version: Self::VERSION,
            block_id,
            payload_hash: *blake3::hash(payload).as_bytes(),
            turn_hash,
            reason_code: reason_code.into(),
        }
    }

    pub fn storage_key(block_id: &[u8; 32]) -> String {
        format!(
            "finalized_payload_rejection:v1:{}",
            dregg_types::hex_encode(block_id)
        )
    }

    pub fn encode(&self) -> Result<Vec<u8>, postcard::Error> {
        postcard::to_stdvec(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_sdk::AgentCipherclerk;
    use dregg_turn::{CallForest, ComputronCosts, Turn};

    fn empty_turn(agent: dregg_cell::CellId) -> Turn {
        Turn {
            agent,
            nonce: 0,
            fee: 0,
            memo: None,
            valid_until: Some(i64::MAX / 2),
            call_forest: CallForest::new(),
            depends_on: vec![],
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    fn signed_fixture(seed: [u8; 32]) -> (AgentCipherclerk, SignedTurn, dregg_cell::Cell) {
        let clerk = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(seed));
        let token = *blake3::hash(b"default").as_bytes();
        let cell = dregg_cell::Cell::with_balance(clerk.public_key().0, token, 1_000_000);
        let signed = clerk.sign_turn(&empty_turn(cell.id()));
        (clerk, signed, cell)
    }

    fn required_executor_for(
        signed: &SignedTurn,
        cell: &dregg_cell::Cell,
        independently_derived_pq_key: Vec<u8>,
    ) -> TurnExecutor {
        let executor = TurnExecutor::new(ComputronCosts::default());
        executor.set_require_pq(true);
        executor
            .enroll_pq_identity(
                signed.turn.agent,
                signed.signer.0,
                cell.state.delegation_epoch(),
                independently_derived_pq_key,
            )
            .expect("fixture enrollment");
        executor
    }

    #[test]
    fn required_hybrid_accepts_only_the_enrolled_outer_identity() {
        let seed = [7; 32];
        let (_clerk, signed, cell) = signed_fixture(seed);
        let enrolled = dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&seed).public_bytes();
        let executor = required_executor_for(&signed, &cell, enrolled);
        assert!(validate_signed_turn(&signed, &executor, Some(&cell)).is_ok());
    }

    #[test]
    fn hostile_outer_pq_variants_fail_closed() {
        let seed = [8; 32];
        let (_clerk, signed, cell) = signed_fixture(seed);
        let enrolled = dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&seed).public_bytes();
        let executor = required_executor_for(&signed, &cell, enrolled);

        let mut stripped = signed.clone();
        stripped.pq_signature.clear();
        stripped.pq_signer.clear();
        assert_eq!(
            validate_signed_turn(&stripped, &executor, Some(&cell)),
            Err(SignedTurnValidationError::PqSignatureRequired)
        );

        let mut invalid = signed.clone();
        invalid.pq_signature[0] ^= 0x80;
        assert_eq!(
            validate_signed_turn(&invalid, &executor, Some(&cell)),
            Err(SignedTurnValidationError::InvalidPqSignature)
        );

        let attacker = dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&[91; 32]);
        let mut substituted = signed.clone();
        substituted.pq_signer = attacker.public_bytes();
        substituted.pq_signature = attacker
            .sign(&signed.turn.hash())
            .expect("attacker produces a valid signature under its own key");
        assert!(dregg_turn::pq::ml_dsa_verify(
            &substituted.pq_signer,
            &substituted.turn.hash(),
            &substituted.pq_signature
        ));
        assert_eq!(
            validate_signed_turn(&substituted, &executor, Some(&cell)),
            Err(SignedTurnValidationError::SubstitutedPqPublicKey)
        );
    }

    #[test]
    fn victim_agent_substitution_is_rejected_before_pq_and_has_stable_record() {
        let (_attacker, mut signed, _attacker_cell) = signed_fixture([9; 32]);
        let victim = dregg_cell::Cell::with_balance([0x55; 32], [0x66; 32], 99_000);
        let before_balance = victim.state.balance();
        let before_nonce = victim.state.nonce();
        signed.turn.agent = victim.id();
        signed.turn.fee = 50_000;
        signed.turn.nonce = before_nonce;

        // Re-sign after choosing the victim fields: the adversary owns both of
        // its own keys; only the signer→agent authority relation is false.
        let attacker = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([9; 32]));
        signed = attacker.sign_turn(&signed.turn);
        let executor = TurnExecutor::new(ComputronCosts::default());
        executor.set_require_pq(true);
        let err = validate_signed_turn(&signed, &executor, Some(&victim)).unwrap_err();
        assert_eq!(err, SignedTurnValidationError::AgentSignerMismatch);
        assert_eq!(victim.state.balance(), before_balance);
        assert_eq!(victim.state.nonce(), before_nonce);

        let block = [0xAB; 32];
        let bytes = postcard::to_stdvec(&signed).expect("encode hostile turn");
        let a = FinalizedPayloadRejectionRecord::new(
            block,
            &bytes,
            Some(signed.turn.hash()),
            err.code(),
        );
        let b = FinalizedPayloadRejectionRecord::new(
            block,
            &bytes,
            Some(signed.turn.hash()),
            err.code(),
        );
        assert_eq!(a.encode().unwrap(), b.encode().unwrap());
        assert_eq!(
            FinalizedPayloadRejectionRecord::storage_key(&block),
            format!("finalized_payload_rejection:v1:{}", "ab".repeat(32))
        );
    }

    #[test]
    fn strict_decoder_refuses_a_valid_signed_turn_prefix_with_trailing_bytes() {
        let (_clerk, signed, _cell) = signed_fixture([10; 32]);
        let canonical = postcard::to_stdvec(&signed).expect("encode SignedTurn");
        let decoded = decode_signed_turn(&canonical).expect("canonical envelope decodes");
        assert_eq!(decoded.turn.hash(), signed.turn.hash());
        assert_eq!(decoded.signer.0, signed.signer.0);
        assert_eq!(decoded.signature.0, signed.signature.0);
        assert_eq!(decoded.pq_signer, signed.pq_signer);
        assert_eq!(decoded.pq_signature, signed.pq_signature);

        let mut smuggled = canonical;
        smuggled.extend_from_slice(&[0x00, 0xA5]);
        assert!(matches!(
            decode_signed_turn(&smuggled),
            Err(SignedTurnDecodeError::TrailingBytes { count: 2 })
        ));
    }
}
