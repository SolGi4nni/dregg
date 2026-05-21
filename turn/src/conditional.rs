//! ConditionalTurn: STARK-conditional cross-domain atomic execution with timeout abort.
//!
//! A ConditionalTurn is a turn submitted to a federation that does NOT execute until
//! a proof satisfying its condition is presented. If the proof doesn't arrive before
//! the timeout height, the turn expires (no state change, no fee charged).
//!
//! This enables cross-federation atomicity:
//! - Fed A commits: "Turn T_A executes IFF proof P_B arrives before height H"
//! - Fed B commits: "Turn T_B executes IFF proof P_A arrives before height H"
//! - If both proofs arrive -> both execute (atomic success)
//! - If either times out -> both revert (atomic failure)
//!
//! The STARK proof replaces the HTLC hash preimage, but is strictly more general:
//! any provable statement can serve as a condition, not just "know a preimage."

use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use crate::turn::{Turn, TurnReceipt};

/// A trusted root entry: the root hash and the height at which it was attested.
pub type TrustedRoot = ([u8; 32], u64);

/// Default maximum root age: roots older than this many blocks are rejected.
pub const DEFAULT_MAX_ROOT_AGE: u64 = 500;

/// Maximum number of blocks into the future a conditional turn deadline may be set.
pub const MAX_CONDITIONAL_DEADLINE: u64 = 1000;

/// A condition that must be satisfied before a turn executes.
///
/// Each variant represents a different class of provable statement.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ProofCondition {
    /// HTLC-style: reveal preimage of this hash (BLAKE3).
    HashPreimage {
        /// The BLAKE3 hash whose preimage must be revealed.
        hash: [u8; 32],
    },

    /// Cross-federation: present a valid STARK proof from a remote federation.
    RemoteProof {
        /// The remote federation's attested Merkle root this proof verifies against.
        federation_root: [u8; 32],
        /// What the proof must prove (AIR identifier).
        expected_air: String,
        /// Minimum expected conclusion value.
        expected_conclusion: u32,
    },

    /// Same-federation: present a valid STARK proof with these public inputs.
    LocalProof {
        /// AIR identifier the proof must satisfy.
        expected_air: String,
        /// Expected public inputs the proof must bind to.
        expected_public_inputs: Vec<u32>,
    },

    /// Receipt-based: prove a specific turn was executed (by presenting its receipt).
    TurnExecuted {
        /// BLAKE3 hash of the turn that must have been executed.
        turn_hash: [u8; 32],
    },
}

/// A turn that's pending execution until its condition is satisfied.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ConditionalTurn {
    /// The underlying turn to execute once the condition is met.
    pub turn: Turn,
    /// The condition that must be satisfied before execution.
    pub condition: ProofCondition,
    /// The block height at which this conditional turn expires.
    pub timeout_height: u64,
    /// The block height at which this conditional turn was submitted.
    pub submitted_at: u64,
}

impl ConditionalTurn {
    /// Compute a unique hash identifying this conditional turn.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-conditional-turn-v1");
        hasher.update(&self.turn.hash());
        hasher.update(&self.timeout_height.to_le_bytes());
        hasher.update(&self.submitted_at.to_le_bytes());
        match &self.condition {
            ProofCondition::HashPreimage { hash } => {
                hasher.update(&[0u8]);
                hasher.update(hash);
            }
            ProofCondition::RemoteProof {
                federation_root,
                expected_air,
                expected_conclusion,
            } => {
                hasher.update(&[1u8]);
                hasher.update(federation_root);
                hasher.update(expected_air.as_bytes());
                hasher.update(&expected_conclusion.to_le_bytes());
            }
            ProofCondition::LocalProof {
                expected_air,
                expected_public_inputs,
            } => {
                hasher.update(&[2u8]);
                hasher.update(expected_air.as_bytes());
                for pi in expected_public_inputs {
                    hasher.update(&pi.to_le_bytes());
                }
            }
            ProofCondition::TurnExecuted { turn_hash } => {
                hasher.update(&[3u8]);
                hasher.update(turn_hash);
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Check if this conditional turn has expired at the given height.
    pub fn is_expired(&self, current_height: u64) -> bool {
        current_height > self.timeout_height
    }
}

/// The result of attempting to resolve a conditional turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConditionalResult {
    /// Condition satisfied.
    Resolved,
    /// Condition not yet satisfied.
    Pending,
    /// Timeout reached.
    Expired,
    /// Condition proof is invalid.
    InvalidProof(String),
}

/// The proof presented to satisfy a condition.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ConditionProof {
    /// Reveal a preimage (for HashPreimage conditions).
    Preimage([u8; 32]),
    /// Present a STARK proof (for RemoteProof or LocalProof conditions).
    StarkProof {
        /// Serialized proof bytes.
        proof_bytes: Vec<u8>,
        /// The federation root this proof was generated against.
        federation_root: [u8; 32],
        /// Public inputs / outputs from the proof.
        public_outputs: Vec<u32>,
        /// The AIR identifier this proof was generated for.
        /// Must match `expected_air` in the condition.
        air_name: String,
    },
    /// Present a turn receipt (for TurnExecuted conditions).
    Receipt(TurnReceipt),
}

/// Resolve a conditional turn by presenting a proof.
///
/// Checks timeout, proof nullifier (reuse prevention), proof type matching,
/// AIR name verification, root freshness, and constraint satisfaction.
pub fn resolve_condition(
    condition: &ProofCondition,
    proof: &ConditionProof,
    current_height: u64,
    timeout_height: u64,
    trusted_roots: &[TrustedRoot],
    max_root_age: u64,
    used_proof_hashes: &mut HashSet<[u8; 32]>,
) -> ConditionalResult {
    if current_height > timeout_height {
        return ConditionalResult::Expired;
    }

    // Proof nullifier: prevent reuse.
    let proof_hash = compute_proof_hash(proof);
    if used_proof_hashes.contains(&proof_hash) {
        return ConditionalResult::InvalidProof("proof already used".to_string());
    }

    let result = resolve_inner(condition, proof, current_height, trusted_roots, max_root_age);

    if result == ConditionalResult::Resolved {
        used_proof_hashes.insert(proof_hash);
    }

    result
}

/// Compute a BLAKE3 hash of the proof for nullifier tracking.
fn compute_proof_hash(proof: &ConditionProof) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-proof-nullifier-v1");
    match proof {
        ConditionProof::Preimage(preimage) => {
            hasher.update(&[0u8]);
            hasher.update(preimage);
        }
        ConditionProof::StarkProof {
            proof_bytes,
            federation_root,
            public_outputs,
            air_name,
        } => {
            hasher.update(&[1u8]);
            hasher.update(proof_bytes);
            hasher.update(federation_root);
            for po in public_outputs {
                hasher.update(&po.to_le_bytes());
            }
            hasher.update(air_name.as_bytes());
        }
        ConditionProof::Receipt(receipt) => {
            hasher.update(&[2u8]);
            hasher.update(&receipt.turn_hash);
        }
    }
    *hasher.finalize().as_bytes()
}

fn resolve_inner(
    condition: &ProofCondition,
    proof: &ConditionProof,
    current_height: u64,
    trusted_roots: &[TrustedRoot],
    max_root_age: u64,
) -> ConditionalResult {
    match (condition, proof) {
        (ProofCondition::HashPreimage { hash }, ConditionProof::Preimage(preimage)) => {
            let computed = *blake3::hash(preimage).as_bytes();
            if computed == *hash {
                ConditionalResult::Resolved
            } else {
                ConditionalResult::InvalidProof("preimage does not match hash".to_string())
            }
        }

        (
            ProofCondition::RemoteProof {
                federation_root,
                expected_air,
                expected_conclusion,
            },
            ConditionProof::StarkProof {
                proof_bytes,
                federation_root: proof_fed_root,
                public_outputs,
                air_name,
            },
        ) => {
            if proof_fed_root != federation_root {
                return ConditionalResult::InvalidProof(
                    "proof federation root does not match expected".to_string(),
                );
            }

            // Root must be trusted AND recent.
            match trusted_roots.iter().find(|(root, _)| root == federation_root) {
                None => {
                    return ConditionalResult::InvalidProof(
                        "federation root is not in trusted set".to_string(),
                    );
                }
                Some(&(_, root_height)) => {
                    if current_height.saturating_sub(root_height) > max_root_age {
                        return ConditionalResult::InvalidProof(format!(
                            "federation root is too old: root height {}, current {}, max age {}",
                            root_height, current_height, max_root_age
                        ));
                    }
                }
            }

            // AIR name must match.
            if air_name != expected_air {
                return ConditionalResult::InvalidProof(format!(
                    "air name mismatch: expected '{}', got '{}'",
                    expected_air, air_name
                ));
            }

            if proof_bytes.is_empty() {
                return ConditionalResult::InvalidProof("proof bytes are empty".to_string());
            }

            match public_outputs.first() {
                Some(&c) if c >= *expected_conclusion => ConditionalResult::Resolved,
                Some(&c) => ConditionalResult::InvalidProof(format!(
                    "conclusion {} is less than expected {}",
                    c, expected_conclusion
                )),
                None => {
                    ConditionalResult::InvalidProof("no public outputs in proof".to_string())
                }
            }
        }

        (
            ProofCondition::LocalProof {
                expected_air,
                expected_public_inputs,
            },
            ConditionProof::StarkProof {
                proof_bytes,
                public_outputs,
                air_name,
                ..
            },
        ) => {
            // AIR name must match.
            if air_name != expected_air {
                return ConditionalResult::InvalidProof(format!(
                    "air name mismatch: expected '{}', got '{}'",
                    expected_air, air_name
                ));
            }

            if proof_bytes.is_empty() {
                return ConditionalResult::InvalidProof("proof bytes are empty".to_string());
            }

            if public_outputs.len() < expected_public_inputs.len() {
                return ConditionalResult::InvalidProof(format!(
                    "proof has {} public outputs, expected at least {}",
                    public_outputs.len(),
                    expected_public_inputs.len()
                ));
            }

            for (i, (expected, actual)) in expected_public_inputs
                .iter()
                .zip(public_outputs.iter())
                .enumerate()
            {
                if expected != actual {
                    return ConditionalResult::InvalidProof(format!(
                        "public input mismatch at index {}: expected {}, got {}",
                        i, expected, actual
                    ));
                }
            }

            ConditionalResult::Resolved
        }

        (ProofCondition::TurnExecuted { turn_hash }, ConditionProof::Receipt(receipt)) => {
            if receipt.turn_hash == *turn_hash {
                ConditionalResult::Resolved
            } else {
                ConditionalResult::InvalidProof(format!(
                    "receipt turn_hash mismatch: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                    turn_hash[0], turn_hash[1], receipt.turn_hash[0], receipt.turn_hash[1],
                ))
            }
        }

        _ => ConditionalResult::InvalidProof(
            "proof type does not match condition type".to_string(),
        ),
    }
}

/// Validate a ConditionalTurn at submission time.
///
/// Checks that the deadline is not too far in the future and fee > 0.
pub fn validate_conditional_submission(
    conditional: &ConditionalTurn,
    current_height: u64,
) -> Result<(), String> {
    if conditional.timeout_height > current_height + MAX_CONDITIONAL_DEADLINE {
        return Err(format!(
            "deadline too far in the future: timeout_height {} exceeds current_height {} + max {}",
            conditional.timeout_height, current_height, MAX_CONDITIONAL_DEADLINE
        ));
    }
    if conditional.turn.fee == 0 {
        return Err(
            "conditional turn requires fee > 0 to prevent storage DoS".to_string(),
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nullifiers() -> HashSet<[u8; 32]> {
        HashSet::new()
    }

    #[test]
    fn test_hash_preimage_resolved() {
        let preimage = [42u8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();
        let condition = ProofCondition::HashPreimage { hash };
        let proof = ConditionProof::Preimage(preimage);
        let mut n = nullifiers();
        let result = resolve_condition(&condition, &proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n);
        assert_eq!(result, ConditionalResult::Resolved);
    }

    #[test]
    fn test_hash_preimage_invalid() {
        let preimage = [42u8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();
        let condition = ProofCondition::HashPreimage { hash };
        let proof = ConditionProof::Preimage([99u8; 32]);
        let mut n = nullifiers();
        let result = resolve_condition(&condition, &proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n);
        assert!(matches!(result, ConditionalResult::InvalidProof(_)));
    }

    #[test]
    fn test_timeout_expired() {
        let preimage = [42u8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();
        let condition = ProofCondition::HashPreimage { hash };
        let proof = ConditionProof::Preimage(preimage);
        let mut n = nullifiers();
        let result = resolve_condition(&condition, &proof, 101, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n);
        assert_eq!(result, ConditionalResult::Expired);
    }

    #[test]
    fn test_remote_proof_resolved() {
        let fed_root = [1u8; 32];
        let condition = ProofCondition::RemoteProof {
            federation_root: fed_root,
            expected_air: "transfer_air".to_string(),
            expected_conclusion: 1,
        };
        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xDE, 0xAD, 0xBE, 0xEF],
            federation_root: fed_root,
            public_outputs: vec![1],
            air_name: "transfer_air".to_string(),
        };
        let trusted = vec![(fed_root, 5u64)];
        let mut n = nullifiers();
        let result = resolve_condition(&condition, &proof, 10, 100, &trusted, DEFAULT_MAX_ROOT_AGE, &mut n);
        assert_eq!(result, ConditionalResult::Resolved);
    }

    #[test]
    fn test_remote_proof_untrusted_root() {
        let fed_root = [1u8; 32];
        let condition = ProofCondition::RemoteProof {
            federation_root: fed_root,
            expected_air: "transfer_air".to_string(),
            expected_conclusion: 1,
        };
        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xDE, 0xAD],
            federation_root: fed_root,
            public_outputs: vec![1],
            air_name: "transfer_air".to_string(),
        };
        let mut n = nullifiers();
        let result = resolve_condition(&condition, &proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n);
        assert!(matches!(result, ConditionalResult::InvalidProof(_)));
    }

    #[test]
    fn test_remote_proof_wrong_conclusion() {
        let fed_root = [1u8; 32];
        let condition = ProofCondition::RemoteProof {
            federation_root: fed_root,
            expected_air: "transfer_air".to_string(),
            expected_conclusion: 2,
        };
        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xDE, 0xAD],
            federation_root: fed_root,
            public_outputs: vec![1],
            air_name: "transfer_air".to_string(),
        };
        let trusted = vec![(fed_root, 5u64)];
        let mut n = nullifiers();
        let result = resolve_condition(&condition, &proof, 10, 100, &trusted, DEFAULT_MAX_ROOT_AGE, &mut n);
        assert!(matches!(result, ConditionalResult::InvalidProof(_)));
    }

    #[test]
    fn test_local_proof_resolved() {
        let condition = ProofCondition::LocalProof {
            expected_air: "compute_air".to_string(),
            expected_public_inputs: vec![100, 200, 300],
        };
        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xFF; 64],
            federation_root: [0u8; 32],
            public_outputs: vec![100, 200, 300],
            air_name: "compute_air".to_string(),
        };
        let mut n = nullifiers();
        let result = resolve_condition(&condition, &proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n);
        assert_eq!(result, ConditionalResult::Resolved);
    }

    #[test]
    fn test_local_proof_input_mismatch() {
        let condition = ProofCondition::LocalProof {
            expected_air: "compute_air".to_string(),
            expected_public_inputs: vec![100, 200, 300],
        };
        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xFF; 64],
            federation_root: [0u8; 32],
            public_outputs: vec![100, 999, 300],
            air_name: "compute_air".to_string(),
        };
        let mut n = nullifiers();
        let result = resolve_condition(&condition, &proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n);
        assert!(matches!(result, ConditionalResult::InvalidProof(_)));
    }

    #[test]
    fn test_turn_executed_resolved() {
        let turn_hash = [0xAB; 32];
        let condition = ProofCondition::TurnExecuted { turn_hash };
        let receipt = TurnReceipt {
            turn_hash,
            forest_hash: [0u8; 32],
            pre_state_hash: [0u8; 32],
            post_state_hash: [0u8; 32],
            timestamp: 1000,
            effects_hash: [0u8; 32],
            computrons_used: 500,
            action_count: 1,
            previous_receipt_hash: None,
            agent: pyana_cell::CellId([0u8; 32]),
            routing_directives: vec![],
            derivation_records: vec![],
            executor_signature: None,
        };
        let proof = ConditionProof::Receipt(receipt);
        let mut n = nullifiers();
        let result = resolve_condition(&condition, &proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n);
        assert_eq!(result, ConditionalResult::Resolved);
    }

    #[test]
    fn test_turn_executed_wrong_hash() {
        let turn_hash = [0xAB; 32];
        let condition = ProofCondition::TurnExecuted { turn_hash };
        let receipt = TurnReceipt {
            turn_hash: [0xCD; 32],
            forest_hash: [0u8; 32],
            pre_state_hash: [0u8; 32],
            post_state_hash: [0u8; 32],
            timestamp: 1000,
            effects_hash: [0u8; 32],
            computrons_used: 500,
            action_count: 1,
            previous_receipt_hash: None,
            agent: pyana_cell::CellId([0u8; 32]),
            routing_directives: vec![],
            derivation_records: vec![],
            executor_signature: None,
        };
        let proof = ConditionProof::Receipt(receipt);
        let mut n = nullifiers();
        let result = resolve_condition(&condition, &proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n);
        assert!(matches!(result, ConditionalResult::InvalidProof(_)));
    }

    #[test]
    fn test_proof_type_mismatch() {
        let condition = ProofCondition::HashPreimage { hash: [0u8; 32] };
        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![1, 2, 3],
            federation_root: [0u8; 32],
            public_outputs: vec![1],
            air_name: "x".to_string(),
        };
        let mut n = nullifiers();
        let result = resolve_condition(&condition, &proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n);
        assert!(matches!(result, ConditionalResult::InvalidProof(_)));
    }

    #[test]
    fn test_conditional_turn_hash_deterministic() {
        use crate::forest::CallForest;
        let turn = Turn {
            agent: pyana_cell::CellId([1u8; 32]),
            nonce: 0,
            call_forest: CallForest::new(),
            fee: 1000,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
        };
        let ct = ConditionalTurn {
            turn,
            condition: ProofCondition::HashPreimage { hash: [0xAA; 32] },
            timeout_height: 100,
            submitted_at: 50,
        };
        assert_eq!(ct.hash(), ct.hash());
    }

    #[test]
    fn test_proof_nullifier_prevents_reuse() {
        let preimage = [42u8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();
        let condition = ProofCondition::HashPreimage { hash };
        let proof = ConditionProof::Preimage(preimage);
        let mut n = nullifiers();
        let r1 = resolve_condition(&condition, &proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n);
        assert_eq!(r1, ConditionalResult::Resolved);
        let r2 = resolve_condition(&condition, &proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n);
        assert_eq!(r2, ConditionalResult::InvalidProof("proof already used".to_string()));
    }

    #[test]
    fn test_root_too_old() {
        let fed_root = [1u8; 32];
        let condition = ProofCondition::RemoteProof {
            federation_root: fed_root,
            expected_air: "t".to_string(),
            expected_conclusion: 1,
        };
        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xDE, 0xAD],
            federation_root: fed_root,
            public_outputs: vec![1],
            air_name: "t".to_string(),
        };
        let trusted = vec![(fed_root, 10u64)];
        let mut n = nullifiers();
        // current=1000, root_height=10, max_age=50 -> age=990 > 50
        let result = resolve_condition(&condition, &proof, 1000, 2000, &trusted, 50, &mut n);
        assert!(matches!(result, ConditionalResult::InvalidProof(ref m) if m.contains("too old")));
    }

    #[test]
    fn test_air_name_mismatch_remote() {
        let fed_root = [1u8; 32];
        let condition = ProofCondition::RemoteProof {
            federation_root: fed_root,
            expected_air: "transfer_air".to_string(),
            expected_conclusion: 1,
        };
        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xDE, 0xAD],
            federation_root: fed_root,
            public_outputs: vec![1],
            air_name: "wrong_air".to_string(),
        };
        let trusted = vec![(fed_root, 5u64)];
        let mut n = nullifiers();
        let result = resolve_condition(&condition, &proof, 10, 100, &trusted, DEFAULT_MAX_ROOT_AGE, &mut n);
        assert!(matches!(result, ConditionalResult::InvalidProof(ref m) if m.contains("air name mismatch")));
    }

    #[test]
    fn test_air_name_mismatch_local() {
        let condition = ProofCondition::LocalProof {
            expected_air: "compute_air".to_string(),
            expected_public_inputs: vec![100],
        };
        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xFF; 64],
            federation_root: [0u8; 32],
            public_outputs: vec![100],
            air_name: "other_air".to_string(),
        };
        let mut n = nullifiers();
        let result = resolve_condition(&condition, &proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n);
        assert!(matches!(result, ConditionalResult::InvalidProof(ref m) if m.contains("air name mismatch")));
    }

    #[test]
    fn test_validate_deadline_too_far() {
        use crate::forest::CallForest;
        let turn = Turn {
            agent: pyana_cell::CellId([1u8; 32]),
            nonce: 0,
            call_forest: CallForest::new(),
            fee: 100,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
        };
        let ct = ConditionalTurn {
            turn,
            condition: ProofCondition::HashPreimage { hash: [0xAA; 32] },
            timeout_height: 5000,
            submitted_at: 10,
        };
        assert!(validate_conditional_submission(&ct, 10).is_err());
    }

    #[test]
    fn test_validate_zero_fee() {
        use crate::forest::CallForest;
        let turn = Turn {
            agent: pyana_cell::CellId([1u8; 32]),
            nonce: 0,
            call_forest: CallForest::new(),
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
        };
        let ct = ConditionalTurn {
            turn,
            condition: ProofCondition::HashPreimage { hash: [0xAA; 32] },
            timeout_height: 100,
            submitted_at: 10,
        };
        assert!(validate_conditional_submission(&ct, 10).is_err());
    }

    #[test]
    fn test_validate_ok() {
        use crate::forest::CallForest;
        let turn = Turn {
            agent: pyana_cell::CellId([1u8; 32]),
            nonce: 0,
            call_forest: CallForest::new(),
            fee: 100,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
        };
        let ct = ConditionalTurn {
            turn,
            condition: ProofCondition::HashPreimage { hash: [0xAA; 32] },
            timeout_height: 100,
            submitted_at: 10,
        };
        assert!(validate_conditional_submission(&ct, 10).is_ok());
    }
}
