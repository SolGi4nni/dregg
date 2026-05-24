//! Persistent Poseidon2 note commitment tree.
//!
//! This wraps `Poseidon2MerkleTree` from `pyana-commit` with redb persistence,
//! providing a ZK-friendly note tree that can generate membership proofs
//! suitable for use inside STARK circuits.
//!
//! The Poseidon2 tree runs alongside the BLAKE3 tree: both store the same
//! logical note commitments, but in different hash domains. The BLAKE3 tree
//! provides fast non-ZK verification, while the Poseidon2 tree provides
//! membership proofs that can be verified inside a STARK proof.

use pyana_circuit::field::BabyBear;
use pyana_commit::poseidon2_tree::{
    Poseidon2MerkleProof, Poseidon2MerkleTree, commitment_to_field,
};

/// A persistent Poseidon2 note tree.
///
/// Maintains an in-memory `Poseidon2MerkleTree` and persists leaves for
/// recovery. The tree can generate Poseidon2 membership proofs that are
/// directly usable as witnesses in STARK proof generation.
#[derive(Clone, Debug)]
pub struct Poseidon2NoteTree {
    /// The underlying Poseidon2 Merkle tree.
    tree: Poseidon2MerkleTree,
}

impl Poseidon2NoteTree {
    /// Create a new empty Poseidon2 note tree with the default depth.
    pub fn new() -> Self {
        Self {
            tree: Poseidon2MerkleTree::new(),
        }
    }

    /// Create a new empty Poseidon2 note tree with a specific depth.
    pub fn with_depth(depth: usize) -> Self {
        Self {
            tree: Poseidon2MerkleTree::with_depth(depth),
        }
    }

    /// Append a BabyBear field element as a leaf commitment.
    /// Returns the position in the tree.
    pub fn append_commitment(&mut self, leaf: BabyBear) -> usize {
        self.tree.append(leaf)
    }

    /// Append a BLAKE3 note commitment by converting it to a field element first.
    ///
    /// This is the bridge function: takes a byte-domain commitment and inserts
    /// the corresponding field element into the Poseidon2 tree.
    /// Returns the position in the tree.
    pub fn append_blake3_commitment(&mut self, commitment: &[u8; 32]) -> usize {
        let field_elem = commitment_to_field(commitment);
        self.tree.append(field_elem)
    }

    /// Get the current Poseidon2 tree root.
    pub fn root(&mut self) -> BabyBear {
        self.tree.root()
    }

    /// Get the current root (immutable version).
    pub fn root_immutable(&self) -> BabyBear {
        self.tree.root_immutable()
    }

    /// Generate a Poseidon2 membership proof for a leaf at the given position.
    ///
    /// This proof can be used as a witness in `NoteSpendingWitness` for STARK
    /// proof generation.
    pub fn prove_membership(&self, position: usize) -> Option<Poseidon2MerkleProof> {
        self.tree.prove_membership(position)
    }

    /// Verify a membership proof against a root and leaf.
    pub fn verify_membership(root: BabyBear, leaf: BabyBear, proof: &Poseidon2MerkleProof) -> bool {
        Poseidon2MerkleTree::verify_membership(root, leaf, proof)
    }

    /// Number of notes in the tree.
    pub fn size(&self) -> usize {
        self.tree.len()
    }

    /// Whether the tree is empty.
    pub fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }

    /// Get the depth of the tree.
    pub fn depth(&self) -> usize {
        self.tree.depth()
    }

    /// Get all leaves (for persistence/recovery).
    pub fn leaves(&self) -> &[BabyBear] {
        self.tree.leaves()
    }

    /// Rebuild from a list of leaves (for recovery from persistence).
    pub fn from_leaves(leaves: Vec<BabyBear>, depth: usize) -> Self {
        Self {
            tree: Poseidon2MerkleTree::from_leaves(leaves, depth),
        }
    }

    /// Rebuild from a list of BLAKE3 commitments (for recovery from persistence).
    pub fn from_blake3_commitments(commitments: &[[u8; 32]], depth: usize) -> Self {
        let leaves: Vec<BabyBear> = commitments.iter().map(|c| commitment_to_field(c)).collect();
        Self::from_leaves(leaves, depth)
    }
}

impl Default for Poseidon2NoteTree {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn poseidon2_note_tree_basic() {
        let mut tree = Poseidon2NoteTree::new();
        assert!(tree.is_empty());
        assert_eq!(tree.size(), 0);

        let pos = tree.append_commitment(BabyBear::new(42));
        assert_eq!(pos, 0);
        assert_eq!(tree.size(), 1);
    }

    #[test]
    fn poseidon2_note_tree_prove_verify() {
        let mut tree = Poseidon2NoteTree::with_depth(4);
        let leaves: Vec<BabyBear> = (1..=10).map(|i| BabyBear::new(i * 100)).collect();
        for &leaf in &leaves {
            tree.append_commitment(leaf);
        }
        let root = tree.root();

        for (pos, &leaf) in leaves.iter().enumerate() {
            let proof = tree.prove_membership(pos).unwrap();
            assert!(
                Poseidon2NoteTree::verify_membership(root, leaf, &proof),
                "Failed at position {pos}"
            );
        }
    }

    #[test]
    fn poseidon2_note_tree_blake3_bridge() {
        let mut tree = Poseidon2NoteTree::with_depth(4);

        // Simulate BLAKE3 note commitments
        let commitment1 = [0x01_u8; 32];
        let commitment2 = [0x02_u8; 32];
        let commitment3 = [0x03_u8; 32];

        let pos1 = tree.append_blake3_commitment(&commitment1);
        let pos2 = tree.append_blake3_commitment(&commitment2);
        let pos3 = tree.append_blake3_commitment(&commitment3);

        assert_eq!(pos1, 0);
        assert_eq!(pos2, 1);
        assert_eq!(pos3, 2);

        let root = tree.root();

        // Verify membership using the converted field element
        let leaf1 = commitment_to_field(&commitment1);
        let proof1 = tree.prove_membership(0).unwrap();
        assert!(Poseidon2NoteTree::verify_membership(root, leaf1, &proof1));
    }

    #[test]
    fn poseidon2_note_tree_recovery() {
        let mut tree = Poseidon2NoteTree::with_depth(4);
        let commitments: Vec<[u8; 32]> = (0..5).map(|i| [i as u8; 32]).collect();
        for c in &commitments {
            tree.append_blake3_commitment(c);
        }
        let root_original = tree.root();

        // Recover from BLAKE3 commitments
        let mut recovered = Poseidon2NoteTree::from_blake3_commitments(&commitments, 4);
        let root_recovered = recovered.root();
        assert_eq!(root_original, root_recovered);
    }
}
