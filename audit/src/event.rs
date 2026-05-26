//! Usage events and audit receipts.
//!
//! A `UsageEvent` records a single token presentation for authorization.
//! An `AuditReceipt` is issued by the verifier as proof that the event
//! was appended to the audit log.

use serde::{Deserialize, Serialize};

/// A single token usage event recorded in the audit trail.
///
/// Each event captures that a token (identified by `token_id`) was presented
/// to a verifier at a specific time for some action. The action itself is
/// hashed to preserve privacy — the auditor can verify consistency without
/// knowing what was actually done.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UsageEvent {
    /// Hash of the token state that was presented.
    pub token_id: [u8; 32],
    /// Unix timestamp (seconds since epoch) when the event occurred.
    pub timestamp: i64,
    /// Hash of the action performed (hides what was done).
    pub action_hash: [u8; 32],
    /// Identifier of the verifier that accepted the token.
    pub verifier_id: [u8; 32],
    /// Monotonically increasing sequence number per token.
    pub sequence: u64,
}

impl UsageEvent {
    /// Create a new usage event.
    pub fn new(
        token_id: [u8; 32],
        timestamp: i64,
        action_hash: [u8; 32],
        verifier_id: [u8; 32],
        sequence: u64,
    ) -> Self {
        Self {
            token_id,
            timestamp,
            action_hash,
            verifier_id,
            sequence,
        }
    }

    /// Compute the canonical hash of this event (used as the Merkle leaf).
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-audit event v1");
        hasher.update(&self.token_id);
        hasher.update(&self.timestamp.to_le_bytes());
        hasher.update(&self.action_hash);
        hasher.update(&self.verifier_id);
        hasher.update(&self.sequence.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Serialize the event to bytes for Merkle leaf insertion.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(32 + 8 + 32 + 32 + 8);
        buf.extend_from_slice(&self.token_id);
        buf.extend_from_slice(&self.timestamp.to_le_bytes());
        buf.extend_from_slice(&self.action_hash);
        buf.extend_from_slice(&self.verifier_id);
        buf.extend_from_slice(&self.sequence.to_le_bytes());
        buf
    }
}

/// Receipt issued by the verifier after appending an event to the audit log.
///
/// This receipt proves that a specific event was included in the log at a
/// specific point in time (characterized by `log_root_after`). The holder
/// can use this receipt to prove to third parties that the event was recorded.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuditReceipt {
    /// Hash of the event that was recorded.
    pub event_hash: [u8; 32],
    /// The log root immediately after this event was appended.
    pub log_root_after: [u8; 32],
    /// Proof that the event is included in the log with root `log_root_after`.
    pub inclusion_proof: InclusionProof,
    /// The global sequence number (position in the log).
    pub global_index: u64,
}

/// Proof that a specific event is included in the audit log Merkle tree.
///
/// This is a 4-ary Merkle inclusion proof, reusing the same structure as
/// `dregg-commit`'s `MerkleProof` but wrapped with audit-specific semantics.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InclusionProof {
    /// The leaf hash being proved.
    pub leaf_hash: [u8; 32],
    /// Path indices at each level (0..3), from leaf to root.
    pub path_indices: Vec<u8>,
    /// Sibling hashes at each level. Each entry is the 3 siblings at that level.
    pub siblings: Vec<[[u8; 32]; 3]>,
}

impl InclusionProof {
    /// Verify this inclusion proof against a given root.
    pub fn verify(&self, root: &[u8; 32]) -> bool {
        use dregg_commit::hash::{HASH_ARITY, hash_node};

        if self.path_indices.len() != self.siblings.len() {
            return false;
        }
        if self.path_indices.is_empty() {
            return false;
        }

        let mut current = self.leaf_hash;
        for level in 0..self.path_indices.len() {
            let idx = self.path_indices[level] as usize;
            if idx >= HASH_ARITY {
                return false;
            }
            let sibs = &self.siblings[level];
            let mut children = [[0u8; 32]; 4];
            let mut sib_idx = 0;
            for i in 0..HASH_ARITY {
                if i == idx {
                    children[i] = current;
                } else {
                    children[i] = sibs[sib_idx];
                    sib_idx += 1;
                }
            }
            current = hash_node(&children);
        }

        current == *root
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn event_hash_deterministic() {
        let e1 = UsageEvent::new([1u8; 32], 1000, [2u8; 32], [3u8; 32], 1);
        let e2 = UsageEvent::new([1u8; 32], 1000, [2u8; 32], [3u8; 32], 1);
        assert_eq!(e1.hash(), e2.hash());
    }

    #[test]
    fn event_hash_changes_with_fields() {
        let base = UsageEvent::new([1u8; 32], 1000, [2u8; 32], [3u8; 32], 1);
        let diff_token = UsageEvent::new([4u8; 32], 1000, [2u8; 32], [3u8; 32], 1);
        let diff_time = UsageEvent::new([1u8; 32], 2000, [2u8; 32], [3u8; 32], 1);
        let diff_action = UsageEvent::new([1u8; 32], 1000, [5u8; 32], [3u8; 32], 1);
        let diff_verifier = UsageEvent::new([1u8; 32], 1000, [2u8; 32], [6u8; 32], 1);
        let diff_seq = UsageEvent::new([1u8; 32], 1000, [2u8; 32], [3u8; 32], 2);

        assert_ne!(base.hash(), diff_token.hash());
        assert_ne!(base.hash(), diff_time.hash());
        assert_ne!(base.hash(), diff_action.hash());
        assert_ne!(base.hash(), diff_verifier.hash());
        assert_ne!(base.hash(), diff_seq.hash());
    }

    #[test]
    fn event_to_bytes_length() {
        let e = UsageEvent::new([0u8; 32], 0, [0u8; 32], [0u8; 32], 0);
        assert_eq!(e.to_bytes().len(), 32 + 8 + 32 + 32 + 8);
    }
}
