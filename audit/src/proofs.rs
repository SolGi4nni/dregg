//! Privacy-preserving audit proofs.
//!
//! These proofs allow an auditor to verify properties of a token's usage
//! history without learning the full details of that history.

use serde::{Deserialize, Serialize};

use crate::event::InclusionProof;
use crate::log::{BridgeHash, TimestampWitness};

/// Proof that a token was used exactly K times.
///
/// The auditor can verify:
/// 1. Each event proof is a valid inclusion in the stated log root.
/// 2. The count matches the number of proofs provided.
/// 3. The index commitment is consistent.
///
/// The auditor does NOT learn:
/// - What actions were taken (action_hash is opaque).
/// - The full event contents beyond what's needed for verification.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CountProof {
    /// The token being proved.
    pub token_id: [u8; 32],
    /// The claimed count of uses.
    pub count: u64,
    /// The log root this proof is valid against.
    pub log_root: [u8; 32],
    /// Total log size at proof generation time.
    pub log_size: u64,
    /// Commitment to the set of indices (for binding).
    pub index_commitment: [u8; 32],
    /// Inclusion proofs for each event. Each tuple is (global_index, leaf_hash, proof).
    pub event_proofs: Vec<(u64, [u8; 32], InclusionProof)>,
}

impl CountProof {
    /// Verify this count proof against the stated log root.
    ///
    /// Checks:
    /// 1. The number of proofs matches the claimed count.
    /// 2. Each inclusion proof is valid against the log root.
    /// 3. All indices are unique and in-range.
    /// 4. The index commitment matches.
    pub fn verify(&self) -> bool {
        // Count matches proofs.
        if self.event_proofs.len() as u64 != self.count {
            return false;
        }

        // Verify each inclusion proof.
        let mut seen_indices = std::collections::HashSet::new();
        let mut indices_for_commit = Vec::with_capacity(self.event_proofs.len());

        for (global_index, leaf_hash, proof) in &self.event_proofs {
            // Index must be in range.
            if *global_index >= self.log_size {
                return false;
            }

            // Index must be unique.
            if !seen_indices.insert(*global_index) {
                return false;
            }

            // Leaf hash must match the proof's leaf.
            if proof.leaf_hash != *leaf_hash {
                return false;
            }

            // Inclusion proof must verify against the log root.
            if !proof.verify(&self.log_root) {
                return false;
            }

            indices_for_commit.push(*global_index);
        }

        // Verify index commitment.
        let mut hasher = blake3::Hasher::new_derive_key("dregg-audit index-commit v1");
        for &idx in &indices_for_commit {
            hasher.update(&idx.to_le_bytes());
        }
        let expected_commitment = *hasher.finalize().as_bytes();
        if self.index_commitment != expected_commitment {
            return false;
        }

        true
    }
}

/// Proof that all uses of a token fall within a time range [start, end].
///
/// The auditor can verify:
/// 1. Each timestamp witness has a valid inclusion proof.
/// 2. All timestamps are within the claimed range.
///
/// The auditor does NOT learn:
/// - What actions were taken.
/// - Any other details of the events.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RangeProof {
    /// The token being proved.
    pub token_id: [u8; 32],
    /// Start of the time range (inclusive).
    pub range_start: i64,
    /// End of the time range (inclusive).
    pub range_end: i64,
    /// The log root this proof is valid against.
    pub log_root: [u8; 32],
    /// Total log size at proof generation time.
    pub log_size: u64,
    /// Timestamp witnesses for each event of this token.
    pub timestamp_witnesses: Vec<TimestampWitness>,
}

impl RangeProof {
    /// Verify this range proof.
    ///
    /// Checks:
    /// 1. Each witness has a valid inclusion proof.
    /// 2. All timestamps are within [range_start, range_end].
    /// 3. All indices are unique and in-range.
    pub fn verify(&self) -> bool {
        let mut seen_indices = std::collections::HashSet::new();

        for witness in &self.timestamp_witnesses {
            // Index in range.
            if witness.global_index >= self.log_size {
                return false;
            }

            // Unique index.
            if !seen_indices.insert(witness.global_index) {
                return false;
            }

            // Timestamp within range.
            if witness.timestamp < self.range_start || witness.timestamp > self.range_end {
                return false;
            }

            // Leaf hash must match the inclusion proof.
            if witness.inclusion_proof.leaf_hash != witness.leaf_hash {
                return false;
            }

            // Inclusion proof must verify.
            if !witness.inclusion_proof.verify(&self.log_root) {
                return false;
            }
        }

        true
    }

    /// Get the count of events in the range.
    pub fn count(&self) -> u64 {
        self.timestamp_witnesses.len() as u64
    }
}

/// Proof that the last use of a token occurred at a specific time.
///
/// The auditor can verify that the most recent event for this token
/// has the stated sequence number and timestamp.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LastUseProof {
    /// The token being proved.
    pub token_id: [u8; 32],
    /// The sequence number of the last event.
    pub last_sequence: u64,
    /// The timestamp of the last event.
    pub last_timestamp: i64,
    /// Hash of the last event.
    pub event_hash: [u8; 32],
    /// Merkle leaf hash.
    pub leaf_hash: [u8; 32],
    /// The log root this proof is valid against.
    pub log_root: [u8; 32],
    /// Total log size at proof generation time.
    pub log_size: u64,
    /// Inclusion proof for the last event.
    pub inclusion_proof: InclusionProof,
}

impl LastUseProof {
    /// Verify this last-use proof.
    ///
    /// Checks:
    /// 1. The inclusion proof is valid against the log root.
    /// 2. The leaf hash matches.
    pub fn verify(&self) -> bool {
        if self.inclusion_proof.leaf_hash != self.leaf_hash {
            return false;
        }
        self.inclusion_proof.verify(&self.log_root)
    }
}

/// Proof that the audit log is append-only (consistency proof).
///
/// Given an old snapshot (root, size) and a new snapshot (root, size),
/// this proves that the new log is an extension of the old log —
/// no events were removed or modified.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsistencyProof {
    /// Root of the log at the old snapshot.
    pub old_root: [u8; 32],
    /// Size of the log at the old snapshot.
    pub old_size: u64,
    /// Root of the log at the new snapshot.
    pub new_root: [u8; 32],
    /// Size of the log at the new snapshot.
    pub new_size: u64,
    /// Bridge hashes connecting old state to new state.
    pub bridge_hashes: Vec<BridgeHash>,
}

impl ConsistencyProof {
    /// Verify this consistency proof.
    ///
    /// This is a structural verification: we check that the bridge hashes
    /// are well-formed and consistent with the claimed sizes.
    ///
    /// Full verification requires reconstructing the old root from the
    /// new tree's prefix, which requires the actual leaf data. This method
    /// verifies the structural properties.
    pub fn verify_structure(&self) -> bool {
        // New size must be >= old size.
        if self.new_size < self.old_size {
            return false;
        }

        // If sizes are equal, roots must match and no bridges needed.
        if self.new_size == self.old_size {
            return self.new_root == self.old_root && self.bridge_hashes.is_empty();
        }

        // Bridge hashes should exist for a growing log.
        // Each bridge hash should have a valid depth and position.
        for bridge in &self.bridge_hashes {
            if bridge.depth == 0 || bridge.depth > 12 {
                return false;
            }
        }

        true
    }
}

/// Proof that a token has remaining budget.
///
/// Proves "token X has used K out of N total budget" without revealing
/// which specific events consumed the budget.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BudgetProof {
    /// The token being proved.
    pub token_id: [u8; 32],
    /// Total budget allocated.
    pub budget_limit: u64,
    /// Number of uses consumed.
    pub uses_consumed: u64,
    /// Remaining uses.
    pub remaining: u64,
    /// Whether a time window applies.
    pub windowed: bool,
    /// If windowed, the window start time.
    pub window_start: Option<i64>,
    /// If windowed, the window end time.
    pub window_end: Option<i64>,
    /// The underlying count proof (proves uses_consumed).
    pub count_proof: CountProof,
}

impl BudgetProof {
    /// Verify this budget proof.
    ///
    /// Checks:
    /// 1. The count proof is valid.
    /// 2. The arithmetic is consistent (remaining = budget_limit - uses_consumed).
    /// 3. The count proof's count matches uses_consumed.
    pub fn verify(&self) -> bool {
        // Arithmetic check.
        if self.uses_consumed > self.budget_limit {
            return false;
        }
        if self.remaining != self.budget_limit - self.uses_consumed {
            return false;
        }

        // Count must match.
        if self.count_proof.count != self.uses_consumed {
            return false;
        }

        // Token must match.
        if self.count_proof.token_id != self.token_id {
            return false;
        }

        // Verify the underlying count proof.
        self.count_proof.verify()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event::UsageEvent;
    use crate::log::AuditLog;

    fn make_event(token_id: [u8; 32], seq: u64, ts: i64) -> UsageEvent {
        UsageEvent::new(token_id, ts, [0xAA; 32], [0xBB; 32], seq)
    }

    #[test]
    fn count_proof_verifies() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        for i in 0..5 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        let proof = log.prove_count(&token);
        assert_eq!(proof.count, 5);
        assert!(proof.verify());
    }

    #[test]
    fn count_proof_empty_token() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];
        let other = [2u8; 32];

        for i in 0..3 {
            log.append(make_event(other, i, 1000 + i as i64));
        }

        let proof = log.prove_count(&token);
        assert_eq!(proof.count, 0);
        assert!(proof.verify());
    }

    #[test]
    fn count_proof_fails_with_tampered_count() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        for i in 0..3 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        let mut proof = log.prove_count(&token);
        proof.count = 5; // Tamper: claim 5 uses instead of 3.
        assert!(!proof.verify());
    }

    #[test]
    fn range_proof_verifies() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        for i in 0..5 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        let proof = log.prove_range(&token, 999, 1005);
        assert!(proof.verify());
        assert_eq!(proof.count(), 5);
    }

    #[test]
    fn range_proof_fails_outside_range() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        for i in 0..5 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        // Claim all events are in [1002, 1005] — but events at 1000, 1001 are outside.
        let proof = log.prove_range(&token, 1002, 1005);
        // The proof generation includes ALL events, so it will contain timestamps
        // outside the claimed range, and verification should fail.
        assert!(!proof.verify());
    }

    #[test]
    fn last_use_proof_verifies() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        for i in 0..5 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        let proof = log.prove_last_use(&token).unwrap();
        assert_eq!(proof.last_sequence, 4);
        assert_eq!(proof.last_timestamp, 1004);
        assert!(proof.verify());
    }

    #[test]
    fn last_use_proof_none_for_unused_token() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];
        assert!(log.prove_last_use(&token).is_none());
    }

    #[test]
    fn consistency_proof_same_size() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        for i in 0..3 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        let snapshot = log.snapshot();
        let proof = log.prove_consistency(&snapshot).unwrap();
        assert!(proof.verify_structure());
        assert_eq!(proof.old_root, proof.new_root);
        assert!(proof.bridge_hashes.is_empty());
    }

    #[test]
    fn consistency_proof_after_growth() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        for i in 0..3 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        let snapshot = log.snapshot();

        // Append more events.
        for i in 3..7 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        let proof = log.prove_consistency(&snapshot).unwrap();
        assert!(proof.verify_structure());
        assert_eq!(proof.old_root, snapshot.root);
        assert_ne!(proof.old_root, proof.new_root);
        assert!(!proof.bridge_hashes.is_empty());
    }

    #[test]
    fn consistency_proof_fails_for_future_snapshot() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        for i in 0..3 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        // Create a fake "future" snapshot.
        let fake_snapshot = crate::log::LogSnapshot {
            root: [0xFF; 32],
            size: 100,
        };

        assert!(log.prove_consistency(&fake_snapshot).is_none());
    }

    #[test]
    fn budget_proof_valid() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        for i in 0..3 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        let count_proof = log.prove_count(&token);
        let budget_proof = BudgetProof {
            token_id: token,
            budget_limit: 10,
            uses_consumed: 3,
            remaining: 7,
            windowed: false,
            window_start: None,
            window_end: None,
            count_proof,
        };

        assert!(budget_proof.verify());
    }

    #[test]
    fn budget_proof_fails_bad_arithmetic() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        for i in 0..3 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        let count_proof = log.prove_count(&token);
        let budget_proof = BudgetProof {
            token_id: token,
            budget_limit: 10,
            uses_consumed: 3,
            remaining: 8, // Wrong! Should be 7.
            windowed: false,
            window_start: None,
            window_end: None,
            count_proof,
        };

        assert!(!budget_proof.verify());
    }

    #[test]
    fn budget_proof_fails_count_mismatch() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        for i in 0..3 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        let count_proof = log.prove_count(&token);
        let budget_proof = BudgetProof {
            token_id: token,
            budget_limit: 10,
            uses_consumed: 5, // Doesn't match count_proof.count (3).
            remaining: 5,
            windowed: false,
            window_start: None,
            window_end: None,
            count_proof,
        };

        assert!(!budget_proof.verify());
    }
}
