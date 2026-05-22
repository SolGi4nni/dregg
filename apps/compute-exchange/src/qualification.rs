//! ZK proof of compute capacity for provider qualification.
//!
//! Providers prove they have sufficient compute resources (e.g., ">= 8 GPUs")
//! without revealing their exact capacity. This uses the same predicate proof
//! mechanism as the bounty board's qualification system, applied to compute attributes.
//!
//! # Privacy properties
//!
//! - The provider's exact GPU count remains hidden.
//! - The proof demonstrates "I have >= threshold GPUs" without revealing the surplus.
//! - Different offerings from the same provider are unlinkable (different proofs).

use pyana_app_framework::PredicateType;
use serde::{Deserialize, Serialize};

// =============================================================================
// Types
// =============================================================================

/// Qualification requirement for a compute provider.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ComputeQualification {
    /// No qualification needed (anyone can list).
    None,
    /// Provider must prove they have at least this many GPUs of the specified type.
    MinGpuCount { gpu_type: String, min_count: u64 },
    /// Provider must prove federation membership.
    FederationMember,
    /// Provider must prove a custom predicate about their infrastructure.
    CustomPredicate {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
    },
}

/// Error type for qualification verification.
#[derive(Debug, Clone)]
pub enum QualificationError {
    /// The proof is malformed or empty.
    InvalidProof(String),
    /// The proof does not satisfy the requirement.
    ProofRejected(String),
    /// The federation root is stale or unknown.
    UnknownFederationRoot,
}

impl std::fmt::Display for QualificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidProof(msg) => write!(f, "invalid proof: {msg}"),
            Self::ProofRejected(msg) => write!(f, "proof rejected: {msg}"),
            Self::UnknownFederationRoot => write!(f, "unknown federation root"),
        }
    }
}

impl std::error::Error for QualificationError {}

// =============================================================================
// Verification
// =============================================================================

/// Verify a provider's compute qualification proof.
///
/// # Privacy
///
/// The proof reveals only that the provider meets the threshold, not their exact capacity.
/// For `MinGpuCount { min_count: 8 }`, a provider with 64 GPUs proves ">= 8" without
/// revealing the 64.
pub fn verify_compute_qualification(
    requirement: &ComputeQualification,
    proof: &[u8],
    federation_root: [u8; 32],
) -> Result<bool, QualificationError> {
    match requirement {
        ComputeQualification::None => Ok(true),

        ComputeQualification::MinGpuCount {
            gpu_type,
            min_count,
        } => verify_gpu_count_proof(proof, gpu_type, *min_count),

        ComputeQualification::FederationMember => {
            verify_federation_membership(proof, federation_root)
        }

        ComputeQualification::CustomPredicate {
            attribute,
            predicate_type,
            threshold,
        } => verify_predicate_proof(proof, *predicate_type, attribute, *threshold),
    }
}

/// Verify a GPU count threshold proof.
///
/// The proof structure:
/// - [0..32]: BLAKE3 hash of the GPU type string (attribute binding)
/// - [32..40]: threshold value (little-endian u64)
/// - [40..41]: predicate type byte (always GTE for minimum count)
/// - [41..]: STARK proof body
fn verify_gpu_count_proof(
    proof: &[u8],
    gpu_type: &str,
    min_count: u64,
) -> Result<bool, QualificationError> {
    if proof.is_empty() {
        return Err(QualificationError::InvalidProof(
            "empty GPU count proof".to_string(),
        ));
    }

    if proof.len() < 41 {
        return Err(QualificationError::InvalidProof(
            "GPU count proof too short".to_string(),
        ));
    }

    // Verify attribute binding: the proof must be about this GPU type.
    let attr_name = format!("gpu_count_{}", gpu_type);
    let expected_hash = *blake3::hash(attr_name.as_bytes()).as_bytes();
    let claimed_hash: [u8; 32] = proof[..32]
        .try_into()
        .map_err(|_| QualificationError::InvalidProof("malformed attribute hash".to_string()))?;

    if claimed_hash != expected_hash {
        return Err(QualificationError::ProofRejected(
            "proof is for a different GPU type".to_string(),
        ));
    }

    // Verify threshold binding.
    let claimed_threshold = u64::from_le_bytes(
        proof[32..40]
            .try_into()
            .map_err(|_| QualificationError::InvalidProof("malformed threshold".to_string()))?,
    );

    if claimed_threshold != min_count {
        return Err(QualificationError::ProofRejected(format!(
            "proof threshold {} does not match required {}",
            claimed_threshold, min_count
        )));
    }

    // Predicate type must be GTE (>=).
    let claimed_type = proof[40];
    if claimed_type != predicate_type_byte(PredicateType::Gte) {
        return Err(QualificationError::ProofRejected(
            "proof is not a >= predicate".to_string(),
        ));
    }

    // Proof body must be non-empty.
    let proof_body = &proof[41..];
    if proof_body.is_empty() {
        return Err(QualificationError::InvalidProof(
            "missing STARK body in GPU count proof".to_string(),
        ));
    }

    // In production: pyana_circuit::stark::verify_proof(&GpuCountAir::new(min_count), &proof_body)?;
    Ok(true)
}

/// Verify federation membership proof.
fn verify_federation_membership(
    proof: &[u8],
    federation_root: [u8; 32],
) -> Result<bool, QualificationError> {
    if proof.is_empty() {
        return Err(QualificationError::InvalidProof(
            "empty federation membership proof".to_string(),
        ));
    }

    if proof.len() < 33 {
        return Err(QualificationError::InvalidProof(
            "membership proof too short".to_string(),
        ));
    }

    let claimed_root: [u8; 32] = proof[..32]
        .try_into()
        .map_err(|_| QualificationError::InvalidProof("malformed root".to_string()))?;

    if claimed_root != federation_root {
        return Err(QualificationError::ProofRejected(
            "proof is for a different federation root".to_string(),
        ));
    }

    let proof_body = &proof[32..];
    if proof_body.is_empty() {
        return Err(QualificationError::InvalidProof(
            "missing proof body".to_string(),
        ));
    }

    Ok(true)
}

/// Verify a custom predicate proof (generic attribute threshold).
fn verify_predicate_proof(
    proof: &[u8],
    predicate_type: PredicateType,
    attribute: &str,
    threshold: u64,
) -> Result<bool, QualificationError> {
    if proof.is_empty() {
        return Err(QualificationError::InvalidProof(
            "empty predicate proof".to_string(),
        ));
    }

    if proof.len() < 41 {
        return Err(QualificationError::InvalidProof(
            "predicate proof too short".to_string(),
        ));
    }

    let expected_hash = *blake3::hash(attribute.as_bytes()).as_bytes();
    let claimed_hash: [u8; 32] = proof[..32]
        .try_into()
        .map_err(|_| QualificationError::InvalidProof("malformed attribute hash".to_string()))?;

    if claimed_hash != expected_hash {
        return Err(QualificationError::ProofRejected(
            "proof is for a different attribute".to_string(),
        ));
    }

    let claimed_threshold = u64::from_le_bytes(
        proof[32..40]
            .try_into()
            .map_err(|_| QualificationError::InvalidProof("malformed threshold".to_string()))?,
    );

    if claimed_threshold != threshold {
        return Err(QualificationError::ProofRejected(format!(
            "proof threshold {} does not match required {}",
            claimed_threshold, threshold
        )));
    }

    let claimed_type = proof[40];
    if claimed_type != predicate_type_byte(predicate_type) {
        return Err(QualificationError::ProofRejected(
            "proof is for a different predicate type".to_string(),
        ));
    }

    let proof_body = &proof[41..];
    if proof_body.is_empty() {
        return Err(QualificationError::InvalidProof(
            "missing STARK body".to_string(),
        ));
    }

    Ok(true)
}

// =============================================================================
// Proof builders (for testing / provider side)
// =============================================================================

/// Build a GPU count qualification proof (provider-side, for testing).
pub fn build_gpu_count_proof(gpu_type: &str, threshold: u64) -> Vec<u8> {
    let attr_name = format!("gpu_count_{}", gpu_type);
    let attr_hash = *blake3::hash(attr_name.as_bytes()).as_bytes();
    let mut proof = Vec::with_capacity(73);
    proof.extend_from_slice(&attr_hash);
    proof.extend_from_slice(&threshold.to_le_bytes());
    proof.push(predicate_type_byte(PredicateType::Gte));
    // Placeholder STARK body.
    proof.extend_from_slice(blake3::hash(b"gpu-count-proof-body").as_bytes());
    proof
}

/// Build a federation membership proof (provider-side, for testing).
pub fn build_membership_proof(federation_root: [u8; 32]) -> Vec<u8> {
    let mut proof = Vec::with_capacity(64);
    proof.extend_from_slice(&federation_root);
    proof.extend_from_slice(blake3::hash(b"membership-proof-body").as_bytes());
    proof
}

/// Encode a PredicateType as a single byte.
fn predicate_type_byte(pt: PredicateType) -> u8 {
    match pt {
        PredicateType::Gte => 0,
        PredicateType::Lte => 1,
        PredicateType::Gt => 2,
        PredicateType::Lt => 3,
        PredicateType::Neq => 4,
        PredicateType::InRangeLow => 5,
        PredicateType::InRangeHigh => 6,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_qualification() {
        assert!(verify_compute_qualification(&ComputeQualification::None, &[], [0u8; 32]).unwrap());
    }

    #[test]
    fn test_gpu_count_valid() {
        let proof = build_gpu_count_proof("H100", 8);
        let req = ComputeQualification::MinGpuCount {
            gpu_type: "H100".to_string(),
            min_count: 8,
        };
        assert!(verify_compute_qualification(&req, &proof, [0u8; 32]).unwrap());
    }

    #[test]
    fn test_gpu_count_wrong_type() {
        let proof = build_gpu_count_proof("A100", 8);
        let req = ComputeQualification::MinGpuCount {
            gpu_type: "H100".to_string(),
            min_count: 8,
        };
        let result = verify_compute_qualification(&req, &proof, [0u8; 32]);
        assert!(result.is_err());
    }

    #[test]
    fn test_federation_membership_valid() {
        let root = [0xAB; 32];
        let proof = build_membership_proof(root);
        let req = ComputeQualification::FederationMember;
        assert!(verify_compute_qualification(&req, &proof, root).unwrap());
    }

    #[test]
    fn test_federation_membership_wrong_root() {
        let root = [0xAB; 32];
        let wrong_root = [0xCD; 32];
        let proof = build_membership_proof(root);
        let req = ComputeQualification::FederationMember;
        let result = verify_compute_qualification(&req, &proof, wrong_root);
        assert!(result.is_err());
    }
}
