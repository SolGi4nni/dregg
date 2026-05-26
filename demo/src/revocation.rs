//! Revocation accumulator — backed by the REAL `dregg_federation::RevocationTree`.
//!
//! The revocation system uses a Merkle-tree-based accumulator (from `dregg-commit`)
//! to track revoked tokens. The key property is:
//!
//! - **Membership**: proving a token IS in the revoked set (it's been revoked)
//! - **Non-membership**: proving a token is NOT in the revoked set (still valid)
//!
//! In a federated system, revocation is particularly interesting:
//! - acme.corp can revoke tokens it issued
//! - partner.org can check revocation status without contacting acme.corp
//!   by checking the non-membership proof against the latest accumulator state
//! - If acme.corp revokes a token, the non-membership proof can no longer
//!   be produced, causing verification to fail
//!
//! This module uses the REAL `dregg_federation::RevocationTree` (Merkle-backed)
//! instead of a standalone hash-chain implementation.

use std::cell::RefCell;

use crate::authority::PublicKey;

/// Re-export the real non-membership proof type from dregg-commit.
pub use dregg_commit::NonMembershipProof;

// =============================================================================
// Revocation Tree Wrapper (backed by dregg_federation::RevocationTree)
// =============================================================================

/// A revocation tree backed by the REAL `dregg_federation::RevocationTree`
/// (which internally uses a 4-ary Merkle tree from `dregg-commit`).
pub struct RevocationAccumulator {
    /// The real Merkle-backed revocation tree (RefCell for interior mutability
    /// of root caching).
    tree: RefCell<dregg_federation::RevocationTree>,
}

impl RevocationAccumulator {
    /// Create a new empty accumulator for an authority.
    pub fn new(_authority: &PublicKey) -> Self {
        RevocationAccumulator {
            tree: RefCell::new(dregg_federation::RevocationTree::new()),
        }
    }

    /// Revoke a token by adding its ID to the Merkle tree.
    /// After this, non-membership proofs for this token_id become impossible.
    pub fn revoke(&self, token_id: &str) {
        self.tree.borrow_mut().revoke(token_id);
    }

    /// Check if a token ID has been revoked.
    pub fn is_revoked(&self, token_id: &str) -> bool {
        self.tree.borrow().is_revoked(token_id)
    }

    /// Generate a non-membership proof for a token ID.
    ///
    /// This proof demonstrates that the token has NOT been revoked.
    /// Returns None if the token IS revoked (proof cannot be generated).
    pub fn prove_non_membership(&self, token_id: &str) -> Option<NonMembershipProof> {
        self.tree.borrow().prove_non_membership(token_id)
    }

    /// Verify a non-membership proof against the current Merkle root.
    pub fn verify_non_membership(&self, proof: &NonMembershipProof) -> bool {
        let root = self.tree.borrow_mut().root();
        dregg_commit::merkle::MerkleTree::verify_non_membership(&root, proof)
    }
}

// =============================================================================
// Shared Revocation Registry
// =============================================================================

/// A federated revocation registry that multiple silos can check.
///
/// In the real system, this would be distributed via a gossip protocol
/// or a shared append-only log. For the demo, it's an in-process
/// shared data structure.
pub struct RevocationRegistry {
    /// Accumulators indexed by authority public key.
    accumulators: Vec<(PublicKey, RevocationAccumulator)>,
}

impl RevocationRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        RevocationRegistry {
            accumulators: Vec::new(),
        }
    }

    /// Register an accumulator for an authority.
    pub fn register(&mut self, authority: &PublicKey) {
        let acc = RevocationAccumulator::new(authority);
        self.accumulators.push((authority.clone(), acc));
    }

    /// Get the accumulator for an authority.
    pub fn get(&self, authority: &PublicKey) -> Option<&RevocationAccumulator> {
        self.accumulators
            .iter()
            .find(|(pk, _)| pk == authority)
            .map(|(_, acc)| acc)
    }

    /// Check if a token is revoked in any accumulator.
    pub fn is_revoked(&self, token_id: &str) -> bool {
        self.accumulators
            .iter()
            .any(|(_, acc)| acc.is_revoked(token_id))
    }

    /// Try to produce a non-membership proof for a token from its issuer's accumulator.
    pub fn prove_non_membership(
        &self,
        token_id: &str,
        issuer: &PublicKey,
    ) -> Option<NonMembershipProof> {
        self.get(issuer)
            .and_then(|acc| acc.prove_non_membership(token_id))
    }

    /// Verify a non-membership proof against the current accumulator state.
    pub fn verify_non_membership(&self, proof: &NonMembershipProof, issuer: &PublicKey) -> bool {
        match self.get(issuer) {
            Some(acc) => acc.verify_non_membership(proof),
            None => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_pubkey() -> PublicKey {
        let auth = crate::authority::Authority::new("test");
        auth.public_key
    }

    #[test]
    fn test_accumulator_creation() {
        let pk = test_pubkey();
        let acc = RevocationAccumulator::new(&pk);
        assert!(!acc.is_revoked("anything"));
    }

    #[test]
    fn test_revoke_token() {
        let pk = test_pubkey();
        let acc = RevocationAccumulator::new(&pk);

        acc.revoke("token-123");

        assert!(acc.is_revoked("token-123"));
        assert!(!acc.is_revoked("token-456"));
    }

    #[test]
    fn test_non_membership_proof() {
        let pk = test_pubkey();
        let acc = RevocationAccumulator::new(&pk);

        // Should be able to prove non-membership of a non-revoked token.
        let proof = acc.prove_non_membership("token-123");
        assert!(proof.is_some());

        let proof = proof.unwrap();
        assert!(acc.verify_non_membership(&proof));
    }

    #[test]
    fn test_non_membership_proof_fails_after_revocation() {
        let pk = test_pubkey();
        let acc = RevocationAccumulator::new(&pk);

        // Get a proof while token is still valid.
        let proof = acc.prove_non_membership("token-123").unwrap();
        assert!(acc.verify_non_membership(&proof));

        // Revoke the token.
        acc.revoke("token-123");

        // The old proof should now fail (Merkle root changed).
        assert!(!acc.verify_non_membership(&proof));

        // Cannot generate a new non-membership proof.
        assert!(acc.prove_non_membership("token-123").is_none());
    }

    #[test]
    fn test_registry() {
        let pk = test_pubkey();
        let mut registry = RevocationRegistry::new();
        registry.register(&pk);

        // Token is not revoked.
        assert!(!registry.is_revoked("token-123"));

        // Can prove non-membership.
        let proof = registry.prove_non_membership("token-123", &pk);
        assert!(proof.is_some());
        assert!(registry.verify_non_membership(proof.as_ref().unwrap(), &pk));

        // Revoke.
        registry.get(&pk).unwrap().revoke("token-123");

        // Now it's revoked.
        assert!(registry.is_revoked("token-123"));

        // Old proof fails.
        assert!(!registry.verify_non_membership(proof.as_ref().unwrap(), &pk));

        // Cannot get new non-membership proof.
        assert!(registry.prove_non_membership("token-123", &pk).is_none());
    }
}
