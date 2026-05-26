//! Revocation Merkle tree management.
//!
//! This module wraps the `dregg-commit` Merkle tree to maintain a set of
//! revoked token IDs. Each revoked token is represented as a leaf in the
//! 4-ary Merkle tree, where the leaf data is the BLAKE3 hash of the token ID.
//!
//! The tree supports:
//! - Adding revoked token IDs (insert)
//! - Checking if a token is revoked (membership)
//! - Proving a token is NOT revoked (non-membership proof)
//! - Getting the current Merkle root

use dregg_commit::merkle::MerkleTree;
use dregg_commit::{NonMembershipProof, hash_leaf};
use std::collections::HashSet;

use crate::types::{AttestedRoot, RevocationProof, hex_encode};

// =============================================================================
// Revocation Tree
// =============================================================================

/// A revocation tree backed by a 4-ary Merkle tree from `dregg-commit`.
///
/// Each leaf represents a revoked token: leaf_hash = H_leaf(token_id_bytes).
/// The tree root commits to the entire revocation set.
#[derive(Clone, Debug)]
pub struct RevocationTree {
    /// The underlying Merkle tree.
    tree: MerkleTree,
    /// Set of revoked token IDs (for quick lookup without tree traversal).
    revoked: HashSet<String>,
}

impl RevocationTree {
    /// Create a new empty revocation tree.
    pub fn new() -> Self {
        Self {
            tree: MerkleTree::new(),
            revoked: HashSet::new(),
        }
    }

    /// Get the current Merkle root of the revocation tree.
    pub fn root(&mut self) -> [u8; 32] {
        self.tree.root()
    }

    /// Short hex of the current root for display.
    pub fn root_hex(&mut self) -> String {
        let r = self.root();
        hex_encode(&r[..4])
    }

    /// Number of revoked tokens in the tree.
    pub fn len(&self) -> usize {
        self.revoked.len()
    }

    /// Whether the tree is empty (no revocations).
    pub fn is_empty(&self) -> bool {
        self.revoked.is_empty()
    }

    /// Check if a token ID is in the revoked set.
    pub fn is_revoked(&self, token_id: &str) -> bool {
        self.revoked.contains(token_id)
    }

    /// Revoke a token by adding it to the tree.
    /// Returns the new Merkle root after insertion.
    /// Returns None if the token was already revoked.
    pub fn revoke(&mut self, token_id: &str) -> Option<[u8; 32]> {
        if self.revoked.contains(token_id) {
            return None;
        }
        self.revoked.insert(token_id.to_string());
        let leaf_data = token_id_to_leaf_data(token_id);
        let new_root = self.tree.insert(&leaf_data);
        Some(new_root)
    }

    /// Batch-revoke multiple tokens. Returns the new root after all insertions.
    pub fn revoke_batch(&mut self, token_ids: &[String]) -> [u8; 32] {
        for token_id in token_ids {
            if !self.revoked.contains(token_id) {
                self.revoked.insert(token_id.clone());
                let leaf_data = token_id_to_leaf_data(token_id);
                self.tree.insert(&leaf_data);
            }
        }
        self.tree.root()
    }

    /// Generate a non-membership proof for a token ID.
    ///
    /// This proves that a token is NOT in the revocation set (i.e., it is still valid).
    /// Returns None if the token IS revoked (cannot prove non-membership).
    pub fn prove_non_membership(&self, token_id: &str) -> Option<NonMembershipProof> {
        if self.revoked.contains(token_id) {
            return None;
        }
        let leaf_data = token_id_to_leaf_data(token_id);
        let leaf_hash = hash_leaf(&leaf_data);
        self.tree.non_membership_proof_hash(&leaf_hash)
    }

    /// Verify a non-membership proof against the current root.
    pub fn verify_non_membership(&mut self, token_id: &str, proof: &NonMembershipProof) -> bool {
        let root = self.root();
        Self::verify_non_membership_against_root(&root, token_id, proof)
    }

    /// Verify a non-membership proof against a specific root (static method).
    pub fn verify_non_membership_against_root(
        root: &[u8; 32],
        _token_id: &str,
        proof: &NonMembershipProof,
    ) -> bool {
        MerkleTree::verify_non_membership(root, proof)
    }

    /// Check if a token is in the tree using the Merkle tree directly.
    pub fn contains_in_tree(&self, token_id: &str) -> bool {
        let leaf_data = token_id_to_leaf_data(token_id);
        self.tree.contains(&leaf_data)
    }
}

impl Default for RevocationTree {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Revocation Verifier
// =============================================================================

/// A verifier that can check whether a token is valid (not revoked) given
/// an attested root and a non-membership proof.
pub struct RevocationVerifier;

impl RevocationVerifier {
    /// Verify a revocation proof: confirm that the token is NOT in the
    /// revocation tree as of the attested root.
    ///
    /// Checks:
    /// 1. The attested root has enough quorum signatures (>= threshold).
    /// 2. The non-membership proof is valid against the attested Merkle root.
    pub fn verify(proof: &RevocationProof) -> RevocationVerification {
        // Check 1: quorum threshold met.
        if !proof.attested_root.has_quorum() {
            return RevocationVerification {
                valid: false,
                reason: "Insufficient quorum signatures".to_string(),
                signatures_present: proof.attested_root.quorum_signatures.len(),
                signatures_required: proof.attested_root.threshold,
            };
        }

        // Check 2: non-membership proof is valid against the attested root.
        let nm_valid = MerkleTree::verify_non_membership(
            &proof.attested_root.merkle_root,
            &proof.non_membership,
        );

        if !nm_valid {
            return RevocationVerification {
                valid: false,
                reason: "Non-membership proof invalid against attested root".to_string(),
                signatures_present: proof.attested_root.quorum_signatures.len(),
                signatures_required: proof.attested_root.threshold,
            };
        }

        RevocationVerification {
            valid: true,
            reason: "Token is not revoked (non-membership verified)".to_string(),
            signatures_present: proof.attested_root.quorum_signatures.len(),
            signatures_required: proof.attested_root.threshold,
        }
    }

    /// Build a complete RevocationProof given a tree, attested root, and token ID.
    pub fn build_proof(
        tree: &RevocationTree,
        attested_root: &AttestedRoot,
        token_id: &str,
    ) -> Option<RevocationProof> {
        let nm_proof = tree.prove_non_membership(token_id)?;
        Some(RevocationProof {
            token_id: token_id.to_string(),
            attested_root: attested_root.clone(),
            non_membership: nm_proof,
        })
    }
}

/// Result of verifying a revocation proof.
#[derive(Clone, Debug)]
pub struct RevocationVerification {
    /// Whether the verification passed.
    pub valid: bool,
    /// Human-readable explanation.
    pub reason: String,
    /// Number of quorum signatures present.
    pub signatures_present: usize,
    /// Number of quorum signatures required.
    pub signatures_required: usize,
}

// =============================================================================
// Helpers
// =============================================================================

/// Convert a token ID to the leaf data that gets inserted into the Merkle tree.
/// We hash the token ID string to get a fixed-size leaf.
fn token_id_to_leaf_data(token_id: &str) -> Vec<u8> {
    // Use domain-separated hashing for the token ID.
    let mut hasher = blake3::Hasher::new_derive_key("dregg-federation revoked-token v1");
    hasher.update(token_id.as_bytes());
    hasher.finalize().as_bytes().to_vec()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_tree() {
        let mut tree = RevocationTree::new();
        assert!(tree.is_empty());
        assert_eq!(tree.len(), 0);
        let root = tree.root();
        assert_ne!(root, [0u8; 32]); // Empty tree has a defined root (not all zeros).
    }

    #[test]
    fn revoke_single_token() {
        let mut tree = RevocationTree::new();
        let empty_root = tree.root();

        let new_root = tree.revoke("token-1");
        assert!(new_root.is_some());
        assert_ne!(new_root.unwrap(), empty_root);
        assert!(tree.is_revoked("token-1"));
        assert!(!tree.is_revoked("token-2"));
        assert_eq!(tree.len(), 1);
    }

    #[test]
    fn revoke_duplicate_returns_none() {
        let mut tree = RevocationTree::new();
        tree.revoke("token-1");
        assert!(tree.revoke("token-1").is_none());
        assert_eq!(tree.len(), 1);
    }

    #[test]
    fn non_membership_proof() {
        let mut tree = RevocationTree::new();
        tree.revoke("token-1");
        tree.revoke("token-3");

        // token-2 is NOT revoked, should have a non-membership proof.
        let proof = tree.prove_non_membership("token-2");
        assert!(proof.is_some());

        let proof = proof.unwrap();
        let root = tree.root();
        assert!(MerkleTree::verify_non_membership(&root, &proof));
    }

    #[test]
    fn no_non_membership_for_revoked() {
        let mut tree = RevocationTree::new();
        tree.revoke("token-1");

        // token-1 IS revoked, cannot prove non-membership.
        let proof = tree.prove_non_membership("token-1");
        assert!(proof.is_none());
    }

    #[test]
    fn batch_revoke() {
        let mut tree = RevocationTree::new();
        let ids = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        tree.revoke_batch(&ids);
        assert_eq!(tree.len(), 3);
        assert!(tree.is_revoked("a"));
        assert!(tree.is_revoked("b"));
        assert!(tree.is_revoked("c"));
        assert!(!tree.is_revoked("d"));
    }

    #[test]
    fn non_membership_proof_empty_tree() {
        let mut tree = RevocationTree::new();
        let proof = tree.prove_non_membership("anything");
        assert!(proof.is_some());

        let root = tree.root();
        assert!(MerkleTree::verify_non_membership(&root, &proof.unwrap()));
    }

    #[test]
    fn deterministic_root() {
        let mut t1 = RevocationTree::new();
        let mut t2 = RevocationTree::new();

        t1.revoke("alpha");
        t1.revoke("beta");

        t2.revoke("alpha");
        t2.revoke("beta");

        assert_eq!(t1.root(), t2.root());
    }

    #[test]
    fn order_independent_root() {
        let mut t1 = RevocationTree::new();
        let mut t2 = RevocationTree::new();

        t1.revoke("alpha");
        t1.revoke("beta");

        t2.revoke("beta");
        t2.revoke("alpha");

        assert_eq!(t1.root(), t2.root());
    }
}
