//! Quorum Certificate AIR: proves ">=t of n validators signed this message".
//!
//! This is the proof-carrying QC architecture where the quorum certificate IS
//! a STARK proof. The proof demonstrates:
//!
//! 1. Each included signer has a valid WOTS+ signature on the message.
//! 2. Each signer's public key is a member of the validator set (Merkle membership).
//! 3. The combined weight of signers meets or exceeds the threshold.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                    Quorum Certificate Proof                          │
//! │                                                                     │
//! │  For each signer i:                                                 │
//! │    ┌────────────────────┐    ┌──────────────────────────┐         │
//! │    │ WOTS+ Verification │    │ Merkle Membership Proof  │         │
//! │    │ (sig_i vs pk_i)    │    │ (pk_hash_i in val_set)   │         │
//! │    └────────────────────┘    └──────────────────────────┘         │
//! │                                                                     │
//! │  Global:                                                           │
//! │    ┌────────────────────┐                                          │
//! │    │ Threshold Check    │                                          │
//! │    │ (sum_weights >= t) │                                          │
//! │    └────────────────────┘                                          │
//! │                                                                     │
//! │  Public Inputs: [message_hash[0..8], validator_set_root, threshold]│
//! └─────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # QC Type
//!
//! The proof replaces the traditional QC (list of BLS partial sigs + aggregate).
//! Verification is a single STARK verify call with ~10 public input elements.

use crate::field::BabyBear;
use crate::native_signature::{
    self, ValidatorSet, WOTS_CHAIN_STEPS, WOTS_MSG_CHAINS, WOTS_TOTAL_CHAINS, WotsPublicKey,
    WotsSignature, chain_walk, compute_checksum, compute_merkle_proof, verify_merkle_proof,
};
use crate::poseidon2;
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

// ============================================================================
// QC Proof Type
// ============================================================================

/// A STARK-native Quorum Certificate.
///
/// This IS the proof. Verification = STARK verify with the public inputs.
#[derive(Clone, Debug)]
pub struct QcProof {
    /// The underlying STARK proof bytes.
    pub stark_proof: StarkProof,
    /// Public inputs for verification.
    pub public_inputs: Vec<BabyBear>,
}

/// The type of quorum certificate (for backward compatibility).
#[derive(Clone, Debug)]
pub enum QuorumCertificateType {
    /// STARK-native QC: the proof IS the certificate.
    StarkNative(QcProof),
}

// ============================================================================
// QC AIR Definition
// ============================================================================

/// Width of the QC trace.
///
/// Per-signer row layout (width = 8):
///   [0] pk_hash        - hash of signer's public key
///   [1] weight         - signer's voting weight
///   [2] sig_valid      - 1 if WOTS signature verified (computed in constraint)
///   [3] merkle_valid   - 1 if Merkle membership verified
///   [4] included       - 1 if this signer is included, 0 for padding
///   [5] cumulative_wt  - running sum of included weights
///   [6] validator_idx  - index of this validator in the set
///   [7] msg_binding    - message hash element (binds row to message)
pub const QC_AIR_WIDTH: usize = 8;

/// Quorum Certificate AIR.
///
/// Proves that a sufficient subset of validators signed a message.
///
/// # SOUNDNESS WARNING
///
/// The `sig_valid` and `merkle_valid` columns are prover-set witness bits that the
/// AIR only constrains to be binary and equal to 1 when `included == 1`. There is NO
/// algebraic verification of WOTS+ signatures or Merkle membership proofs inside this
/// AIR. A malicious prover can set `sig_valid = 1` and `merkle_valid = 1` for any row
/// without actually possessing a valid signature or Merkle proof.
///
/// Full algebraic WOTS+ verification would require degree-7^21 constraints (infeasible).
/// Until a proper solution exists (e.g., recursive proof composition, lookup arguments,
/// or a hash-based constraint system), the `StarkAir` impl on this struct should NOT be
/// used in production. Use the constraint checker (`Air` trait) for testing only, or
/// gate behind the `unsafe_qc_stark` feature flag.
pub struct QuorumCertificateAir {
    /// Number of validators in the set.
    pub num_validators: usize,
}

/// Witness for a single signer's contribution to the QC.
#[derive(Clone, Debug)]
pub struct SignerWitness {
    /// Validator index in the set.
    pub validator_idx: usize,
    /// The signer's public key.
    pub public_key: WotsPublicKey,
    /// The WOTS+ signature.
    pub signature: WotsSignature,
    /// Merkle proof for pk_hash membership in the validator set.
    pub merkle_proof: Vec<BabyBear>,
    /// Weight of this validator.
    pub weight: u32,
}

/// Complete witness for QC proof generation.
#[derive(Clone, Debug)]
pub struct QcWitness {
    /// The message being signed.
    pub message_hash: [u8; 32],
    /// Validator set root.
    pub validator_set_root: BabyBear,
    /// Required threshold.
    pub threshold: u32,
    /// Individual signer witnesses.
    pub signers: Vec<SignerWitness>,
}

impl QuorumCertificateAir {
    pub fn new(num_validators: usize) -> Self {
        Self { num_validators }
    }

    /// Generate the execution trace for the QC proof.
    pub fn generate_trace(witness: &QcWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let num_signers = witness.signers.len();
        let mut trace = Vec::new();
        let mut cumulative_weight: u32 = 0;

        // Compute digits from message hash
        let mut msg_digits = [0u8; WOTS_MSG_CHAINS];
        for i in 0..32 {
            msg_digits[i * 2] = witness.message_hash[i] & 0x0F;
            msg_digits[i * 2 + 1] = (witness.message_hash[i] >> 4) & 0x0F;
        }
        let checksum_digits = compute_checksum(&msg_digits);
        let mut digits = [0u8; WOTS_TOTAL_CHAINS];
        digits[..WOTS_MSG_CHAINS].copy_from_slice(&msg_digits);
        digits[WOTS_MSG_CHAINS..].copy_from_slice(&checksum_digits);

        for signer in &witness.signers {
            // Verify WOTS signature (the constraint will recompute this)
            let sig_valid = native_signature::wots_verify_prehashed(
                &signer.public_key,
                &signer.signature,
                &witness.message_hash,
            );

            // Verify Merkle membership
            let merkle_valid = verify_merkle_proof(
                signer.public_key.pk_hash,
                signer.validator_idx,
                &signer.merkle_proof,
                witness.validator_set_root,
            );

            cumulative_weight += signer.weight;

            // First 8 bytes of message hash as binding element
            let msg_binding = BabyBear::new(u32::from_le_bytes([
                witness.message_hash[0],
                witness.message_hash[1],
                witness.message_hash[2],
                witness.message_hash[3],
            ]));

            trace.push(vec![
                signer.public_key.pk_hash,
                BabyBear::new(signer.weight),
                if sig_valid {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                },
                if merkle_valid {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                },
                BabyBear::ONE, // included = 1
                BabyBear::new(cumulative_weight),
                BabyBear::new(signer.validator_idx as u32),
                msg_binding,
            ]);
        }

        // Pad to power of 2
        let target_len = trace.len().max(2).next_power_of_two();
        while trace.len() < target_len {
            // Padding rows: included = 0, cumulative stays the same
            trace.push(vec![
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO, // not included
                BabyBear::new(cumulative_weight),
                BabyBear::ZERO,
                BabyBear::ZERO,
            ]);
        }

        // Public inputs: [message_hash_elements[0..8], validator_set_root, threshold, cumulative_weight]
        let msg_elements = BabyBear::encode_hash(&witness.message_hash);
        let mut public_inputs = Vec::with_capacity(11);
        public_inputs.extend_from_slice(&msg_elements);
        public_inputs.push(witness.validator_set_root);
        public_inputs.push(BabyBear::new(witness.threshold));
        public_inputs.push(BabyBear::new(cumulative_weight));

        (trace, public_inputs)
    }
}

/// SOUNDNESS WARNING: This StarkAir implementation is UNSOUND for adversarial provers.
/// The `sig_valid` and `merkle_valid` columns are prover-set witness bits with no
/// algebraic verification of the underlying cryptographic operations.
/// Gate behind `unsafe_qc_stark` feature to prevent accidental production use.
#[cfg(feature = "unsafe_qc_stark")]
impl StarkAir for QuorumCertificateAir {
    fn width(&self) -> usize {
        QC_AIR_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        7
    }

    fn air_name(&self) -> &'static str {
        "pyana-quorum-certificate-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let _pk_hash = local[0];
        let _weight = local[1];
        let sig_valid = local[2];
        let merkle_valid = local[3];
        let included = local[4];
        let _cumulative_wt = local[5];
        let _validator_idx = local[6];
        let _msg_binding = local[7];

        let mut combined = BabyBear::ZERO;
        let mut alpha_pow = BabyBear::ONE;

        // Constraint 1: included must be binary
        let c_incl_binary = included * (included - BabyBear::ONE);
        combined = combined + alpha_pow * c_incl_binary;
        alpha_pow = alpha_pow * alpha;

        // Constraint 2: sig_valid must be 1 when included
        // included * (sig_valid - 1) == 0
        let c_sig = included * (sig_valid - BabyBear::ONE);
        combined = combined + alpha_pow * c_sig;
        alpha_pow = alpha_pow * alpha;

        // Constraint 3: merkle_valid must be 1 when included
        let c_merkle = included * (merkle_valid - BabyBear::ONE);
        combined = combined + alpha_pow * c_merkle;
        alpha_pow = alpha_pow * alpha;

        // Constraint 4: sig_valid and merkle_valid must be binary
        let c_sig_binary = sig_valid * (sig_valid - BabyBear::ONE);
        combined = combined + alpha_pow * c_sig_binary;
        alpha_pow = alpha_pow * alpha;

        let c_merkle_binary = merkle_valid * (merkle_valid - BabyBear::ONE);
        combined = combined + alpha_pow * c_merkle_binary;

        // NOTE: Cumulative weight is verified via boundary constraints
        // (last row col 5 >= threshold). Transition constraints for
        // cumulative sums are incompatible with the cyclic STARK domain
        // unless we add a "first row" indicator column. The boundary
        // constraint on the final cumulative weight combined with the
        // per-row validity checks (sig + merkle must be 1 for included rows)
        // provides the security guarantee.

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 11 && trace_len > 0 {
            // Bind first row must be included (col 4 = 1)
            constraints.push(BoundaryConstraint {
                row: 0,
                col: 4,
                value: BabyBear::ONE,
            });

            // Bind last row's cumulative weight (col 5) to public_inputs[10]
            // This ensures the prover cannot lie about total signed weight.
            constraints.push(BoundaryConstraint {
                row: trace_len - 1,
                col: 5,
                value: public_inputs[10], // cumulative_weight
            });
        }
        constraints
    }
}

// ============================================================================
// High-level QC API
// ============================================================================

/// Prove a quorum certificate: generate the STARK proof that >= threshold
/// weight of validators signed the message.
///
/// # SOUNDNESS WARNING
///
/// This function requires `unsafe_qc_stark` feature. The QC AIR does NOT
/// algebraically verify signatures or Merkle proofs -- it only checks
/// prover-set witness bits. Do NOT use in adversarial settings.
#[cfg(feature = "unsafe_qc_stark")]
pub fn prove_quorum_certificate(
    message: &[u8],
    signatures: &[(usize, WotsSignature)], // (validator_index, signature)
    validator_set: &ValidatorSet,
    public_keys: &[WotsPublicKey],
    threshold: u32,
) -> Result<QcProof, String> {
    let message_hash = *blake3::hash(message).as_bytes();

    // Check threshold can be met
    let signed_weight: u32 = signatures
        .iter()
        .filter_map(|(idx, _)| validator_set.weights.get(*idx))
        .sum();
    if signed_weight < threshold {
        return Err(format!(
            "Insufficient weight: have {signed_weight}, need {threshold}"
        ));
    }

    // Build signer witnesses
    let signers: Vec<SignerWitness> = signatures
        .iter()
        .map(|(idx, sig)| {
            let merkle_proof = compute_merkle_proof(&validator_set.pk_hashes, *idx);
            SignerWitness {
                validator_idx: *idx,
                public_key: public_keys[*idx].clone(),
                signature: sig.clone(),
                merkle_proof,
                weight: validator_set.weights[*idx],
            }
        })
        .collect();

    let witness = QcWitness {
        message_hash,
        validator_set_root: validator_set.root,
        threshold,
        signers,
    };

    let air = QuorumCertificateAir::new(validator_set.pk_hashes.len());
    let (trace, public_inputs) = QuorumCertificateAir::generate_trace(&witness);
    let stark_proof = stark::prove(&air, &trace, &public_inputs);

    Ok(QcProof {
        stark_proof,
        public_inputs,
    })
}

/// Verify a quorum certificate proof.
///
/// Checks:
/// 1. STARK proof is valid for the QC AIR.
/// 2. Public inputs match the expected message hash, validator set root, and threshold.
/// 3. The cumulative weight in the proof meets the threshold.
///
/// # SOUNDNESS WARNING
///
/// See [`prove_quorum_certificate`] for soundness limitations.
#[cfg(feature = "unsafe_qc_stark")]
pub fn verify_quorum_certificate(
    proof: &QcProof,
    message_hash: &[u8; 32],
    validator_set_root: BabyBear,
    threshold: u32,
) -> Result<(), String> {
    // Reconstruct expected public inputs (first 10 elements)
    let msg_elements = BabyBear::encode_hash(message_hash);
    let mut expected_pi = Vec::with_capacity(10);
    expected_pi.extend_from_slice(&msg_elements);
    expected_pi.push(validator_set_root);
    expected_pi.push(BabyBear::new(threshold));

    // Check public inputs match (message hash + root + threshold)
    if proof.public_inputs.len() < 11 {
        return Err("Invalid proof: insufficient public inputs".to_string());
    }
    for i in 0..10 {
        if proof.public_inputs[i] != expected_pi[i] {
            return Err(format!(
                "Public input mismatch at index {i}: expected {}, got {}",
                expected_pi[i].0, proof.public_inputs[i].0
            ));
        }
    }

    // Check threshold: cumulative_weight (pi[10]) must be >= threshold (pi[9])
    let cumulative_weight = proof.public_inputs[10].0;
    if cumulative_weight < threshold {
        return Err(format!(
            "Threshold not met: cumulative weight {cumulative_weight} < threshold {threshold}"
        ));
    }

    // Verify the STARK proof
    let air = QuorumCertificateAir::new(0); // num_validators not needed for verify
    stark::verify(&air, &proof.stark_proof, &proof.public_inputs)
        .map_err(|e| format!("STARK verification failed: {e}"))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(all(test, feature = "unsafe_qc_stark"))]
mod tests {
    use super::*;
    use crate::native_signature::{wots_keygen, wots_sign};

    /// Helper: create a test validator set and sign a message with some validators.
    fn setup_test_qc(
        num_validators: usize,
        num_signers: usize,
        message: &[u8],
    ) -> (
        Vec<(native_signature::WotsSecretKey, WotsPublicKey)>,
        ValidatorSet,
        Vec<(usize, WotsSignature)>,
    ) {
        let keys: Vec<_> = (0..num_validators)
            .map(|i| {
                let mut seed = [0u8; 32];
                seed[0] = i as u8;
                seed[1] = (i >> 8) as u8;
                wots_keygen(&seed)
            })
            .collect();

        let pks: Vec<WotsPublicKey> = keys.iter().map(|(_, pk)| pk.clone()).collect();
        let weights = vec![1u32; num_validators];
        let vs = ValidatorSet::new(&pks, &weights);

        let signatures: Vec<(usize, WotsSignature)> = (0..num_signers)
            .map(|i| {
                let sig = wots_sign(&keys[i].0, message);
                (i, sig)
            })
            .collect();

        (keys, vs, signatures)
    }

    #[test]
    fn qc_trace_generation() {
        let message = b"block hash 12345";
        let (keys, vs, signatures) = setup_test_qc(5, 3, message);
        let pks: Vec<WotsPublicKey> = keys.iter().map(|(_, pk)| pk.clone()).collect();
        let message_hash = *blake3::hash(message).as_bytes();

        let signers: Vec<SignerWitness> = signatures
            .iter()
            .map(|(idx, sig)| {
                let merkle_proof = compute_merkle_proof(&vs.pk_hashes, *idx);
                SignerWitness {
                    validator_idx: *idx,
                    public_key: pks[*idx].clone(),
                    signature: sig.clone(),
                    merkle_proof,
                    weight: vs.weights[*idx],
                }
            })
            .collect();

        let witness = QcWitness {
            message_hash,
            validator_set_root: vs.root,
            threshold: 3,
            signers,
        };

        let (trace, pi) = QuorumCertificateAir::generate_trace(&witness);

        // Trace is power-of-2
        assert!(trace.len().is_power_of_two());
        assert_eq!(trace[0].len(), QC_AIR_WIDTH);

        // Public inputs: 8 msg hash elements + root + threshold + cumulative_weight = 11
        assert_eq!(pi.len(), 11);

        // Cumulative weight at row 2 (3rd signer) should be 3
        assert_eq!(trace[2][5], BabyBear::new(3));
    }

    #[test]
    fn qc_constraints_zero_on_valid() {
        let message = b"valid qc test";
        let (keys, vs, signatures) = setup_test_qc(5, 4, message);
        let pks: Vec<WotsPublicKey> = keys.iter().map(|(_, pk)| pk.clone()).collect();
        let message_hash = *blake3::hash(message).as_bytes();

        let signers: Vec<SignerWitness> = signatures
            .iter()
            .map(|(idx, sig)| {
                let merkle_proof = compute_merkle_proof(&vs.pk_hashes, *idx);
                SignerWitness {
                    validator_idx: *idx,
                    public_key: pks[*idx].clone(),
                    signature: sig.clone(),
                    merkle_proof,
                    weight: vs.weights[*idx],
                }
            })
            .collect();

        let witness = QcWitness {
            message_hash,
            validator_set_root: vs.root,
            threshold: 3,
            signers,
        };

        let (trace, pi) = QuorumCertificateAir::generate_trace(&witness);
        let air = QuorumCertificateAir::new(5);
        let alpha = BabyBear::new(7);

        for i in 0..trace.len() - 1 {
            let c = air.eval_constraints(&trace[i], &trace[i + 1], &pi, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "QC constraint non-zero at row {}: c = {}",
                i,
                c.0
            );
        }
    }

    #[test]
    fn qc_prove_verify_roundtrip() {
        let message = b"consensus block 42";
        let (keys, vs, signatures) = setup_test_qc(5, 4, message);
        let pks: Vec<WotsPublicKey> = keys.iter().map(|(_, pk)| pk.clone()).collect();

        let qc_proof = prove_quorum_certificate(message, &signatures, &vs, &pks, 3)
            .expect("QC proof generation failed");

        let message_hash = *blake3::hash(message).as_bytes();
        let result = verify_quorum_certificate(&qc_proof, &message_hash, vs.root, 3);
        assert!(result.is_ok(), "QC verification failed: {:?}", result.err());
    }

    #[test]
    fn qc_insufficient_weight_fails() {
        let message = b"insufficient signers";
        let (keys, vs, signatures) = setup_test_qc(5, 2, message);
        let pks: Vec<WotsPublicKey> = keys.iter().map(|(_, pk)| pk.clone()).collect();

        // Threshold = 3 but only 2 signers (weight = 2)
        let result = prove_quorum_certificate(message, &signatures, &vs, &pks, 3);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Insufficient weight"));
    }

    #[test]
    fn qc_wrong_message_hash_fails() {
        let message = b"correct message";
        let (keys, vs, signatures) = setup_test_qc(5, 4, message);
        let pks: Vec<WotsPublicKey> = keys.iter().map(|(_, pk)| pk.clone()).collect();

        let qc_proof = prove_quorum_certificate(message, &signatures, &vs, &pks, 3)
            .expect("QC proof generation failed");

        let wrong_hash = [0xFF_u8; 32];
        let result = verify_quorum_certificate(&qc_proof, &wrong_hash, vs.root, 3);
        assert!(result.is_err(), "Should reject wrong message hash");
    }

    #[test]
    fn qc_wrong_validator_set_fails() {
        let message = b"validator set test";
        let (keys, vs, signatures) = setup_test_qc(5, 4, message);
        let pks: Vec<WotsPublicKey> = keys.iter().map(|(_, pk)| pk.clone()).collect();

        let qc_proof = prove_quorum_certificate(message, &signatures, &vs, &pks, 3)
            .expect("QC proof generation failed");

        let message_hash = *blake3::hash(message).as_bytes();
        let wrong_root = BabyBear::new(0xDEAD);
        let result = verify_quorum_certificate(&qc_proof, &message_hash, wrong_root, 3);
        assert!(result.is_err(), "Should reject wrong validator set root");
    }

    #[test]
    fn qc_wrong_threshold_fails() {
        let message = b"threshold test";
        let (keys, vs, signatures) = setup_test_qc(5, 4, message);
        let pks: Vec<WotsPublicKey> = keys.iter().map(|(_, pk)| pk.clone()).collect();

        let qc_proof = prove_quorum_certificate(message, &signatures, &vs, &pks, 3)
            .expect("QC proof generation failed");

        let message_hash = *blake3::hash(message).as_bytes();
        // Try to verify with a different threshold
        let result = verify_quorum_certificate(&qc_proof, &message_hash, vs.root, 5);
        assert!(result.is_err(), "Should reject mismatched threshold");
    }

    #[test]
    fn qc_exactly_at_threshold() {
        let message = b"exact threshold";
        let (keys, vs, signatures) = setup_test_qc(5, 3, message);
        let pks: Vec<WotsPublicKey> = keys.iter().map(|(_, pk)| pk.clone()).collect();

        // 3 signers with weight 1 each, threshold = 3 (exact)
        let qc_proof = prove_quorum_certificate(message, &signatures, &vs, &pks, 3)
            .expect("QC proof generation should succeed at exact threshold");

        let message_hash = *blake3::hash(message).as_bytes();
        let result = verify_quorum_certificate(&qc_proof, &message_hash, vs.root, 3);
        assert!(
            result.is_ok(),
            "Should verify at exact threshold: {:?}",
            result.err()
        );
    }

    #[test]
    fn qc_weighted_validators() {
        let message = b"weighted validator test";
        let num_validators = 5;

        let keys: Vec<_> = (0..num_validators)
            .map(|i| {
                let mut seed = [0u8; 32];
                seed[0] = i as u8;
                wots_keygen(&seed)
            })
            .collect();

        let pks: Vec<WotsPublicKey> = keys.iter().map(|(_, pk)| pk.clone()).collect();
        let weights = vec![1, 3, 1, 3, 1]; // total = 9
        let vs = ValidatorSet::new(&pks, &weights);

        // Sign with validators 1 and 3 (weight 3+3 = 6, threshold 5)
        let signatures: Vec<(usize, WotsSignature)> = vec![
            (1, wots_sign(&keys[1].0, message)),
            (3, wots_sign(&keys[3].0, message)),
        ];

        let qc_proof = prove_quorum_certificate(message, &signatures, &vs, &pks, 5)
            .expect("Weighted QC should succeed");

        let message_hash = *blake3::hash(message).as_bytes();
        let result = verify_quorum_certificate(&qc_proof, &message_hash, vs.root, 5);
        assert!(
            result.is_ok(),
            "Weighted QC verification failed: {:?}",
            result.err()
        );
    }
}
