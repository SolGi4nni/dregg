//! Revocation list and non-revocation proof generation.
//!
//! When an issuer revokes a credential, its revocation hash is added to a
//! sorted Merkle tree. Holders must provide non-revocation proofs (proving
//! their credential's hash is NOT in the tree) when presenting to verifiers.

use pyana_circuit::field::BabyBear;
use pyana_circuit::non_revocation_air::{self, SortedRevocationTree};
use pyana_circuit::stark::StarkProof;

/// A non-revocation proof: demonstrates that a credential has not been revoked.
#[derive(Clone, Debug)]
pub struct NonRevocationProof {
    /// The revocation tree root this proof is against.
    pub revocation_root: BabyBear,
    /// Whether the proof is valid (credential is NOT revoked).
    pub is_valid: bool,
}

/// Manage a revocation list and generate proofs.
pub struct RevocationManager {
    /// Current revocation hashes.
    revoked_hashes: Vec<BabyBear>,
    /// The sorted revocation tree.
    tree: SortedRevocationTree,
    /// Tree depth.
    depth: usize,
}

impl RevocationManager {
    /// Create a new empty revocation manager.
    pub fn new(depth: usize) -> Self {
        Self {
            revoked_hashes: Vec::new(),
            tree: SortedRevocationTree::new(Vec::new(), depth),
            depth,
        }
    }

    /// Create from existing revocation hashes.
    pub fn from_hashes(hashes: Vec<BabyBear>, depth: usize) -> Self {
        let tree = SortedRevocationTree::new(hashes.clone(), depth);
        Self {
            revoked_hashes: hashes,
            tree,
            depth,
        }
    }

    /// Add a revocation hash (revoke a credential).
    pub fn revoke(&mut self, hash: BabyBear) {
        if !self.revoked_hashes.contains(&hash) {
            self.revoked_hashes.push(hash);
            self.tree = SortedRevocationTree::new(self.revoked_hashes.clone(), self.depth);
        }
    }

    /// Check if a hash is revoked.
    pub fn is_revoked(&self, hash: &BabyBear) -> bool {
        self.tree.contains(hash)
    }

    /// Get the current revocation tree root.
    pub fn root(&self) -> BabyBear {
        self.tree.root()
    }

    /// Get a reference to the underlying tree.
    pub fn tree(&self) -> &SortedRevocationTree {
        &self.tree
    }

    /// Generate a non-revocation proof for a credential hash.
    ///
    /// Returns a STARK proof that the given hash is NOT in the revocation tree.
    /// Returns None if the hash IS revoked (proof is impossible).
    pub fn prove_non_revocation(&self, credential_hash: BabyBear) -> Option<StarkProof> {
        let ancestor_hashes = vec![credential_hash];
        non_revocation_air::prove_non_revocation(&ancestor_hashes, &self.tree)
    }

    /// Verify a non-revocation proof against the current root.
    pub fn verify_proof(&self, proof: &StarkProof) -> bool {
        non_revocation_air::verify_non_revocation(self.root(), proof).is_ok()
    }

    /// Number of revoked credentials.
    pub fn num_revoked(&self) -> usize {
        self.revoked_hashes.len()
    }
}
