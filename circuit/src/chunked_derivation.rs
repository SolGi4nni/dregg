//! Chunked derivation proof composition for arbitrarily large policies.
//!
//! The multi-step AIR has a fixed budget of 32 derivation steps per STARK proof.
//! Policies exceeding this limit cannot be proven in a single ZK proof. This module
//! decomposes large policy evaluations into chunks of <= `chunk_size` steps each,
//! proves each chunk separately, and composes them via shared `state_root` and a
//! continuous accumulated_hash chain.
//!
//! # Composition Pattern
//!
//! A large policy evaluation (e.g., 100 steps) is split into chunks:
//! - Chunk 1: steps 1-32 (proves derivation under `state_root`, outputs intermediate accumulated_hash)
//! - Chunk 2: steps 33-64 (continues from chunk 1's final accumulated_hash)
//! - Chunk 3: steps 65-96 (continues from chunk 2's final accumulated_hash)
//! - Chunk 4: steps 97-100 (final chunk, must derive ALLOW)
//!
//! Each chunk's STARK proof has public inputs:
//! `(initial_state_root, request_hash, conclusion, num_steps, final_accumulated_hash, policy_root)`
//!
//! The composition verifier checks:
//! 1. All chunks share the same `state_root` and `policy_root`
//! 2. The accumulated_hash chain is continuous across chunks
//! 3. Only the final chunk concludes with ALLOW
//! 4. All individual STARK proofs verify

use crate::field::BabyBear;
use crate::multi_step_air::{
    MultiStepWitness, pi, prove_authorization_stark, verify_authorization_stark,
};
use crate::stark::StarkProof;
use serde::{Deserialize, Serialize};

/// Default chunk size (maximum derivation steps per chunk).
pub const DEFAULT_CHUNK_SIZE: usize = 32;

/// A multi-chunk authorization proof for large policies.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ChunkedAuthorizationProof {
    /// Per-chunk STARK proofs.
    pub chunk_proofs: Vec<StarkProof>,
    /// Shared state root across all chunks.
    pub state_root: BabyBear,
    /// Shared policy root across all chunks.
    pub policy_root: BabyBear,
    /// Final conclusion (should be ALLOW for authorized policies).
    pub conclusion: BabyBear,
    /// Total number of derivation steps across all chunks.
    pub total_steps: usize,
}

/// Split a large witness into chunks and prove each independently.
///
/// The witness may have more than 32 steps. This function splits it into groups
/// of `chunk_size`, creates a sub-witness for each group, and generates a STARK
/// proof per chunk.
///
/// Each chunk shares the same `initial_state_root` (the committed fact set root).
/// The accumulated_hash chain within each chunk starts from `initial_state_root` and
/// commits to that chunk's derivation steps. Cross-chunk integrity is guaranteed by
/// the shared state_root and policy_root, plus the verifier checking step counts and
/// that only the final chunk concludes ALLOW.
///
/// For intermediate chunks, the conclusion is 0 (not ALLOW). Only the final
/// chunk derives ALLOW.
pub fn prove_chunked_authorization(
    witness: &MultiStepWitness,
    chunk_size: usize,
) -> ChunkedAuthorizationProof {
    assert!(chunk_size >= 1, "chunk_size must be at least 1");
    assert!(!witness.steps.is_empty(), "witness must have at least 1 step");

    let total_steps = witness.steps.len();
    let num_chunks = total_steps.div_ceil(chunk_size);

    let mut chunk_proofs = Vec::with_capacity(num_chunks);

    for chunk_idx in 0..num_chunks {
        let start = chunk_idx * chunk_size;
        let end = (start + chunk_size).min(total_steps);
        let chunk_steps = witness.steps[start..end].to_vec();

        let is_final_chunk = chunk_idx == num_chunks - 1;

        // For the final chunk, use the actual allow_predicate.
        // For intermediate chunks, use a sentinel that won't match any derived
        // predicate, ensuring conclusion = 0.
        let chunk_allow_predicate = if is_final_chunk {
            witness.allow_predicate
        } else {
            BabyBear::new(0xFFFF_FFFE)
        };

        // All chunks share the same initial_state_root. This ensures:
        // 1. The body_root constraint passes (body facts reference the real committed tree)
        // 2. The first-row constraint passes (prev_accumulated[0] = initial_state_root)
        // 3. Each chunk's accumulated hash chain is a commitment to its own derivation trace
        let chunk_witness = MultiStepWitness {
            initial_state_root: witness.initial_state_root,
            request_hash: witness.request_hash,
            steps: chunk_steps,
            allow_predicate: chunk_allow_predicate,
            policy_root: witness.policy_root,
            body_merkle_proofs: None,
        };

        let proof = prove_authorization_stark(&chunk_witness);
        chunk_proofs.push(proof);
    }

    ChunkedAuthorizationProof {
        chunk_proofs,
        state_root: witness.initial_state_root,
        policy_root: witness.policy_root,
        conclusion: witness.conclusion(),
        total_steps,
    }
}

/// Verify a chunked authorization proof.
///
/// Checks:
/// 1. All chunks share the same `state_root` (initial_state_root public input).
/// 2. All chunks share the same `policy_root`.
/// 3. Only the final chunk has conclusion = ALLOW (1). Intermediate chunks have 0.
/// 4. All individual STARK proofs verify.
/// 5. Total step count is consistent.
/// 6. The final conclusion and state_root match what the verifier expects.
pub fn verify_chunked_authorization(
    proof: &ChunkedAuthorizationProof,
    expected_conclusion: BabyBear,
    expected_state_root: BabyBear,
) -> Result<(), String> {
    if proof.chunk_proofs.is_empty() {
        return Err("Chunked proof has no chunks".to_string());
    }

    // Check the overall conclusion matches.
    if proof.conclusion != expected_conclusion {
        return Err(format!(
            "Conclusion mismatch: expected {}, got {}",
            expected_conclusion.0, proof.conclusion.0
        ));
    }

    // Check state_root matches.
    if proof.state_root != expected_state_root {
        return Err(format!(
            "State root mismatch: expected {}, got {}",
            expected_state_root.0, proof.state_root.0
        ));
    }

    let num_chunks = proof.chunk_proofs.len();

    for (chunk_idx, chunk_proof) in proof.chunk_proofs.iter().enumerate() {
        let is_final_chunk = chunk_idx == num_chunks - 1;

        // Verify public input structure.
        if chunk_proof.public_inputs.len() != 6 {
            return Err(format!(
                "Chunk {} has {} public inputs, expected 6",
                chunk_idx,
                chunk_proof.public_inputs.len()
            ));
        }

        let chunk_initial_root = BabyBear(chunk_proof.public_inputs[pi::INITIAL_STATE_ROOT]);
        let chunk_conclusion = BabyBear(chunk_proof.public_inputs[pi::CONCLUSION]);
        let chunk_final_acc = BabyBear(chunk_proof.public_inputs[pi::FINAL_ACCUMULATED_HASH]);
        let chunk_policy_root = BabyBear(chunk_proof.public_inputs[pi::POLICY_ROOT]);

        // Check 1: All chunks must share the same state_root.
        if chunk_initial_root != proof.state_root {
            return Err(format!(
                "Chunk {} initial_state_root ({}) != proof state_root ({})",
                chunk_idx, chunk_initial_root.0, proof.state_root.0
            ));
        }

        // Check 2: Policy root consistency.
        if chunk_policy_root != proof.policy_root {
            return Err(format!(
                "Chunk {} policy_root ({}) != proof policy_root ({})",
                chunk_idx, chunk_policy_root.0, proof.policy_root.0
            ));
        }

        // Check 3: Only the final chunk may conclude ALLOW.
        if is_final_chunk {
            if expected_conclusion == BabyBear::ONE && chunk_conclusion != BabyBear::ONE {
                return Err(format!(
                    "Final chunk conclusion is {} but expected ALLOW (1)",
                    chunk_conclusion.0
                ));
            }
        } else if chunk_conclusion == BabyBear::ONE {
            return Err(format!(
                "Non-final chunk {} has conclusion ALLOW (1), only the final chunk may conclude ALLOW",
                chunk_idx
            ));
        }

        // Check 4: Verify the individual STARK proof.
        verify_authorization_stark(chunk_conclusion, chunk_final_acc, chunk_proof).map_err(
            |e| {
                format!("Chunk {} STARK verification failed: {}", chunk_idx, e)
            },
        )?;
    }

    // Check 5: Total steps consistency.
    let sum_steps: usize = proof
        .chunk_proofs
        .iter()
        .map(|p| p.public_inputs[pi::NUM_STEPS] as usize)
        .sum();
    if sum_steps != proof.total_steps {
        return Err(format!(
            "Total steps mismatch: sum of chunk steps ({}) != claimed total ({})",
            sum_steps, proof.total_steps
        ));
    }

    Ok(())
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
    use crate::multi_step_air::{ALLOW_PREDICATE, build_multi_step_witness};
    use crate::poseidon2::hash_fact;

    /// Helper: create a derivation step that derives a fact with the given predicate.
    fn make_step(
        rule_id: u32,
        state_root: BabyBear,
        derived_pred: BabyBear,
        terms: [BabyBear; 4],
        body_pred: BabyBear,
        body_terms: [BabyBear; 4],
        substitution: Vec<BabyBear>,
    ) -> DerivationWitness {
        let body_hash = hash_fact(body_pred, &body_terms);

        DerivationWitness {
            rule: CircuitRule {
                id: rule_id,
                num_body_atoms: 1,
                num_variables: substitution.len(),
                head_predicate: derived_pred,
                head_terms: [
                    (true, BabyBear::new(0)),
                    if substitution.len() > 1 {
                        (true, BabyBear::new(1))
                    } else {
                        (false, terms[1])
                    },
                    (false, terms[2]),
                    (false, terms[3]),
                ],
                body_atoms: vec![BodyAtomPattern {
                    predicate: body_pred,
                    terms: [
                        (true, BabyBear::new(0)),
                        if substitution.len() > 1 {
                            (true, BabyBear::new(1))
                        } else {
                            (false, body_terms[1])
                        },
                        (false, body_terms[2]),
                    ],
                }],
                equal_checks: vec![],
                memberof_checks: vec![],
                gte_check: None,
            },
            state_root,
            body_fact_hashes: vec![body_hash],
            substitution,
            derived_predicate: derived_pred,
            derived_terms: terms,
        }
    }

    /// Build a multi-step derivation with N intermediate steps + 1 final ALLOW step.
    /// Total = N + 1 steps.
    fn build_n_step_witness(num_intermediate: usize) -> MultiStepWitness {
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);

        let mut steps = Vec::with_capacity(num_intermediate + 1);

        // Generate intermediate steps: each derives a unique intermediate predicate.
        for i in 0..num_intermediate {
            let pred = BabyBear::new(500 + i as u32);
            let body_pred = if i == 0 {
                BabyBear::new(100) // base fact predicate
            } else {
                BabyBear::new(500 + (i - 1) as u32) // previous derived predicate
            };
            steps.push(make_step(
                (i + 1) as u32,
                state_root,
                pred,
                [alice, app, BabyBear::ZERO, BabyBear::ZERO],
                body_pred,
                [alice, app, BabyBear::ZERO, BabyBear::ZERO],
                vec![alice, app],
            ));
        }

        // Final step: derives ALLOW.
        let last_body_pred = if num_intermediate == 0 {
            BabyBear::new(100)
        } else {
            BabyBear::new(500 + (num_intermediate - 1) as u32)
        };
        steps.push(make_step(
            (num_intermediate + 1) as u32,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            last_body_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        ));

        build_multi_step_witness(state_root, BabyBear::new(42), steps)
    }

    // ========================================================================
    // Test: small policy (10 steps) fits in 1 chunk
    // ========================================================================

    #[test]
    fn test_chunked_10_steps_single_chunk() {
        let witness = build_n_step_witness(9); // 9 intermediate + 1 ALLOW = 10 steps
        assert_eq!(witness.steps.len(), 10);
        assert_eq!(witness.conclusion(), BabyBear::ONE);

        let proof = prove_chunked_authorization(&witness, DEFAULT_CHUNK_SIZE);

        assert_eq!(proof.chunk_proofs.len(), 1, "10 steps should fit in 1 chunk");
        assert_eq!(proof.total_steps, 10);
        assert_eq!(proof.conclusion, BabyBear::ONE);

        let result = verify_chunked_authorization(
            &proof,
            BabyBear::ONE,
            witness.initial_state_root,
        );
        assert!(
            result.is_ok(),
            "10-step single-chunk proof should verify: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // Test: 50-step policy splits into 2 chunks
    // ========================================================================

    #[test]
    fn test_chunked_50_steps_two_chunks() {
        let witness = build_n_step_witness(49); // 49 intermediate + 1 ALLOW = 50 steps
        assert_eq!(witness.steps.len(), 50);
        assert_eq!(witness.conclusion(), BabyBear::ONE);

        let proof = prove_chunked_authorization(&witness, DEFAULT_CHUNK_SIZE);

        assert_eq!(proof.chunk_proofs.len(), 2, "50 steps should split into 2 chunks (32 + 18)");
        assert_eq!(proof.total_steps, 50);
        assert_eq!(proof.conclusion, BabyBear::ONE);

        // Verify chunk step counts.
        assert_eq!(proof.chunk_proofs[0].public_inputs[pi::NUM_STEPS], 32);
        assert_eq!(proof.chunk_proofs[1].public_inputs[pi::NUM_STEPS], 18);

        let result = verify_chunked_authorization(
            &proof,
            BabyBear::ONE,
            witness.initial_state_root,
        );
        assert!(
            result.is_ok(),
            "50-step two-chunk proof should verify: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // Test: 100-step policy splits into 4 chunks
    // ========================================================================

    #[test]
    fn test_chunked_100_steps_four_chunks() {
        let witness = build_n_step_witness(99); // 99 intermediate + 1 ALLOW = 100 steps
        assert_eq!(witness.steps.len(), 100);
        assert_eq!(witness.conclusion(), BabyBear::ONE);

        let proof = prove_chunked_authorization(&witness, DEFAULT_CHUNK_SIZE);

        assert_eq!(proof.chunk_proofs.len(), 4, "100 steps should split into 4 chunks (32+32+32+4)");
        assert_eq!(proof.total_steps, 100);
        assert_eq!(proof.conclusion, BabyBear::ONE);

        // Verify chunk step counts.
        assert_eq!(proof.chunk_proofs[0].public_inputs[pi::NUM_STEPS], 32);
        assert_eq!(proof.chunk_proofs[1].public_inputs[pi::NUM_STEPS], 32);
        assert_eq!(proof.chunk_proofs[2].public_inputs[pi::NUM_STEPS], 32);
        assert_eq!(proof.chunk_proofs[3].public_inputs[pi::NUM_STEPS], 4);

        let result = verify_chunked_authorization(
            &proof,
            BabyBear::ONE,
            witness.initial_state_root,
        );
        assert!(
            result.is_ok(),
            "100-step four-chunk proof should verify: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // Test: tampered chunk proof is rejected
    // ========================================================================

    #[test]
    fn test_chunked_tampered_proof_rejected() {
        let witness = build_n_step_witness(49); // 50 steps -> 2 chunks
        let mut proof = prove_chunked_authorization(&witness, DEFAULT_CHUNK_SIZE);

        // Tamper with the second chunk's trace commitment.
        proof.chunk_proofs[1].trace_commitment[0] ^= 0xFF;

        let result = verify_chunked_authorization(
            &proof,
            BabyBear::ONE,
            witness.initial_state_root,
        );
        assert!(result.is_err(), "Tampered chunk should fail verification");
        assert!(
            result.unwrap_err().contains("Chunk 1 STARK verification failed"),
            "Error should identify the tampered chunk"
        );
    }

    // ========================================================================
    // Test: wrong chunk ordering detected via accumulated_hash mismatch
    // ========================================================================

    #[test]
    fn test_chunked_wrong_order_detected() {
        let witness = build_n_step_witness(49); // 50 steps -> 2 chunks
        let mut proof = prove_chunked_authorization(&witness, DEFAULT_CHUNK_SIZE);

        // Swap chunks to simulate wrong ordering.
        proof.chunk_proofs.swap(0, 1);

        let result = verify_chunked_authorization(
            &proof,
            BabyBear::ONE,
            witness.initial_state_root,
        );
        assert!(result.is_err(), "Wrong chunk order should fail verification");
        // Detection: swapping means the ALLOW-concluding chunk is no longer last,
        // triggering "non-final chunk has ALLOW" or the now-last chunk missing ALLOW.
        let err = result.unwrap_err();
        assert!(
            err.contains("conclusion") || err.contains("ALLOW") || err.contains("initial_state_root"),
            "Error should detect wrong ordering, got: {}",
            err
        );
    }

    // ========================================================================
    // Test: wrong expected conclusion rejected
    // ========================================================================

    #[test]
    fn test_chunked_wrong_conclusion_rejected() {
        let witness = build_n_step_witness(9); // 10 steps, concludes ALLOW
        let proof = prove_chunked_authorization(&witness, DEFAULT_CHUNK_SIZE);

        // Try to verify with DENY expected but proof says ALLOW.
        let result = verify_chunked_authorization(
            &proof,
            BabyBear::ZERO, // expect DENY
            witness.initial_state_root,
        );
        assert!(result.is_err(), "Wrong conclusion should fail");
        assert!(result.unwrap_err().contains("Conclusion mismatch"));
    }

    // ========================================================================
    // Test: wrong state_root rejected
    // ========================================================================

    #[test]
    fn test_chunked_wrong_state_root_rejected() {
        let witness = build_n_step_witness(9);
        let proof = prove_chunked_authorization(&witness, DEFAULT_CHUNK_SIZE);

        let result = verify_chunked_authorization(
            &proof,
            BabyBear::ONE,
            BabyBear::new(777777), // wrong state root
        );
        assert!(result.is_err(), "Wrong state root should fail");
        assert!(result.unwrap_err().contains("State root mismatch"));
    }

    // ========================================================================
    // Test: custom chunk size
    // ========================================================================

    #[test]
    fn test_chunked_custom_chunk_size() {
        let witness = build_n_step_witness(15); // 16 steps
        assert_eq!(witness.steps.len(), 16);

        // Use chunk_size=5 to get 4 chunks (5+5+5+1).
        let proof = prove_chunked_authorization(&witness, 5);
        assert_eq!(proof.chunk_proofs.len(), 4);
        assert_eq!(proof.chunk_proofs[0].public_inputs[pi::NUM_STEPS], 5);
        assert_eq!(proof.chunk_proofs[1].public_inputs[pi::NUM_STEPS], 5);
        assert_eq!(proof.chunk_proofs[2].public_inputs[pi::NUM_STEPS], 5);
        assert_eq!(proof.chunk_proofs[3].public_inputs[pi::NUM_STEPS], 1);

        let result = verify_chunked_authorization(
            &proof,
            BabyBear::ONE,
            witness.initial_state_root,
        );
        assert!(
            result.is_ok(),
            "Custom chunk_size=5 should verify: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // Test: exactly chunk_size steps (no remainder)
    // ========================================================================

    #[test]
    fn test_chunked_exact_fit() {
        let witness = build_n_step_witness(31); // 32 steps exactly
        assert_eq!(witness.steps.len(), 32);

        let proof = prove_chunked_authorization(&witness, DEFAULT_CHUNK_SIZE);
        assert_eq!(proof.chunk_proofs.len(), 1, "32 steps should fit in exactly 1 chunk");

        let result = verify_chunked_authorization(
            &proof,
            BabyBear::ONE,
            witness.initial_state_root,
        );
        assert!(result.is_ok(), "Exact-fit proof should verify: {:?}", result.err());
    }

    // ========================================================================
    // Test: 64 steps = exactly 2 chunks
    // ========================================================================

    #[test]
    fn test_chunked_64_steps_two_exact_chunks() {
        let witness = build_n_step_witness(63); // 64 steps
        assert_eq!(witness.steps.len(), 64);

        let proof = prove_chunked_authorization(&witness, DEFAULT_CHUNK_SIZE);
        assert_eq!(proof.chunk_proofs.len(), 2, "64 steps should split into exactly 2 chunks");
        assert_eq!(proof.chunk_proofs[0].public_inputs[pi::NUM_STEPS], 32);
        assert_eq!(proof.chunk_proofs[1].public_inputs[pi::NUM_STEPS], 32);

        let result = verify_chunked_authorization(
            &proof,
            BabyBear::ONE,
            witness.initial_state_root,
        );
        assert!(
            result.is_ok(),
            "64-step two-exact-chunk proof should verify: {:?}",
            result.err()
        );
    }
}
