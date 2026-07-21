//! Persistent Poseidon2 note commitment tree.
//!
//! This wraps `Poseidon2MerkleTree` from `dregg-commit` with redb persistence,
//! providing a ZK-friendly note tree that can generate membership proofs
//! suitable for use inside STARK circuits.
//!
//! The Poseidon2 tree runs alongside the BLAKE3 tree: both store the same
//! logical note commitments, but in different hash domains. The BLAKE3 tree
//! provides fast non-ZK verification, while the Poseidon2 tree provides
//! membership proofs that can be verified inside a STARK proof.

use dregg_circuit::Faithful8;
use dregg_circuit::field::BabyBear;
use dregg_commit::poseidon2_tree::{
    NoteTree16Digest, Poseidon2MerkleProof, Poseidon2MerkleTree, Poseidon2NoteProof16,
    Poseidon2NoteTree16, commitment_to_field, commitment_to_lanes16,
};

/// A persistent Poseidon2 note tree.
///
/// Maintains an in-memory `Poseidon2MerkleTree` and persists leaves for
/// recovery. The tree can generate Poseidon2 membership proofs that are
/// directly usable as witnesses in STARK proof generation.
#[derive(Clone, Debug)]
pub struct Poseidon2NoteTree {
    /// Legacy one-felt tree, retained while its wire consumers rotate.
    tree: Poseidon2MerkleTree,
    /// Faithful sixteen-lane twin. Every byte-domain append advances this tree
    /// at the same position as `tree`; no scalar intermediary is reused.
    tree16: Poseidon2NoteTree16,
}

impl Poseidon2NoteTree {
    /// Create a new empty Poseidon2 note tree with the default depth.
    pub fn new() -> Self {
        Self {
            tree: Poseidon2MerkleTree::new(),
            tree16: Poseidon2NoteTree16::new(),
        }
    }

    /// Create a new empty Poseidon2 note tree with a specific depth.
    pub fn with_depth(depth: usize) -> Self {
        Self {
            tree: Poseidon2MerkleTree::with_depth(depth),
            tree16: Poseidon2NoteTree16::with_depth(depth),
        }
    }

    /// Append a BabyBear field element as a leaf commitment.
    /// Returns the position in the tree.
    pub fn append_commitment(&mut self, leaf: BabyBear) -> usize {
        // This scalar-only compatibility API has no original 32-byte source.
        // Give the wide twin the exact canonical u32 encoding of the field
        // element so both trees still advance at the same position. Production
        // note creation uses `append_blake3_commitment`, which carries all 32
        // source bytes and therefore takes the fully faithful path.
        let mut encoded = [0u8; 32];
        encoded[..4].copy_from_slice(&leaf.as_u32().to_le_bytes());
        let legacy_position = self.tree.append(leaf);
        let wide_position = self.tree16.append_commitment(&encoded);
        debug_assert_eq!(legacy_position, wide_position);
        legacy_position
    }

    /// Append a BLAKE3 note commitment by converting it to a field element first.
    ///
    /// This is the bridge function: takes a byte-domain commitment and inserts
    /// the corresponding field element into the Poseidon2 tree.
    /// Returns the position in the tree.
    pub fn append_blake3_commitment(&mut self, commitment: &[u8; 32]) -> usize {
        let field_elem = commitment_to_field(commitment);
        let legacy_position = self.tree.append(field_elem);
        let wide_position = self.tree16.append_commitment(commitment);
        debug_assert_eq!(legacy_position, wide_position);
        legacy_position
    }

    /// Get the current Poseidon2 tree root.
    pub fn root(&mut self) -> BabyBear {
        self.tree.root()
    }

    /// Get the current root (immutable version).
    pub fn root_immutable(&self) -> BabyBear {
        self.tree.root_immutable()
    }

    /// The faithful eight-felt / 32-byte root derived directly from exact
    /// sixteen-lane raw notes, with every internal node kept at faithful-eight
    /// width. This is the root new attestation and spend consumers should
    /// carry; [`Self::root`] remains the legacy scalar root.
    pub fn faithful_root(&mut self) -> Faithful8 {
        self.tree16.root()
    }

    /// Immutable form of [`Self::faithful_root`].
    pub fn faithful_root_immutable(&self) -> Faithful8 {
        self.tree16.root_immutable()
    }

    /// Generate a Poseidon2 membership proof for a leaf at the given position.
    ///
    /// This proof can be used as a witness in `NoteSpendingWitness` for STARK
    /// proof generation.
    pub fn prove_membership(&self, position: usize) -> Option<Poseidon2MerkleProof> {
        self.tree.prove_membership(position)
    }

    /// Generate a membership proof against the faithful sixteen-lane root.
    pub fn prove_membership16(&self, position: usize) -> Option<Poseidon2NoteProof16> {
        self.tree16.prove_membership(position)
    }

    /// Verify a membership proof against a root and leaf.
    pub fn verify_membership(root: BabyBear, leaf: BabyBear, proof: &Poseidon2MerkleProof) -> bool {
        Poseidon2MerkleTree::verify_membership(root, leaf, proof)
    }

    /// Verify a proof for an exact sixteen-lane leaf against a faithful-eight
    /// root.
    pub fn verify_membership16(
        root: Faithful8,
        leaf: NoteTree16Digest,
        proof: &Poseidon2NoteProof16,
    ) -> bool {
        Poseidon2NoteTree16::verify_membership(root, leaf, proof)
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

    /// Get every faithful raw sixteen-lane note leaf in append order.
    pub fn leaves16(&self) -> &[NoteTree16Digest] {
        self.tree16.leaves()
    }

    /// Rebuild from a list of leaves (for recovery from persistence).
    pub fn from_leaves(leaves: Vec<BabyBear>, depth: usize) -> Self {
        let leaves16 = leaves
            .iter()
            .map(|leaf| {
                let mut encoded = [0u8; 32];
                encoded[..4].copy_from_slice(&leaf.as_u32().to_le_bytes());
                commitment_to_lanes16(&encoded)
            })
            .collect();
        Self {
            tree: Poseidon2MerkleTree::from_leaves(leaves, depth),
            tree16: Poseidon2NoteTree16::from_leaves(leaves16, depth),
        }
    }

    /// Rebuild from a list of BLAKE3 commitments (for recovery from persistence).
    pub fn from_blake3_commitments(commitments: &[[u8; 32]], depth: usize) -> Self {
        let leaves: Vec<BabyBear> = commitments.iter().map(commitment_to_field).collect();
        Self {
            tree: Poseidon2MerkleTree::from_leaves(leaves, depth),
            tree16: Poseidon2NoteTree16::from_commitments(commitments, depth),
        }
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
        assert_eq!(tree.faithful_root(), recovered.faithful_root());
    }

    /// The production wrapper advances the legacy and faithful trees in
    /// lockstep.  This hostile pair aliases in the old scalar tree because one
    /// raw u32 chunk differs by exactly BabyBear p; the wide tree and its
    /// membership authority must still distinguish them.
    #[test]
    fn production_note_tree16_rejects_x_plus_p_membership_alias() {
        let x = 1_000_000u32;
        let x_plus_p = x.checked_add(dregg_circuit::field::BABYBEAR_P).unwrap();
        let mut commitment_x = [0u8; 32];
        let mut commitment_x_plus_p = [0u8; 32];
        commitment_x[..4].copy_from_slice(&x.to_le_bytes());
        commitment_x_plus_p[..4].copy_from_slice(&x_plus_p.to_le_bytes());

        let mut honest = Poseidon2NoteTree::with_depth(4);
        honest.append_blake3_commitment(&commitment_x);
        let legacy_honest_root = honest.root();
        let wide_honest_root = honest.faithful_root();
        let wide_honest_proof = honest.prove_membership16(0).unwrap();

        let mut alias = Poseidon2NoteTree::with_depth(4);
        alias.append_blake3_commitment(&commitment_x_plus_p);
        assert_eq!(
            legacy_honest_root,
            alias.root(),
            "the falsifier must hit the old modulo-p bridge alias"
        );
        assert_ne!(
            wide_honest_root,
            alias.faithful_root(),
            "the production wide twin must preserve all commitment bytes"
        );

        let honest_leaf = commitment_to_lanes16(&commitment_x);
        let alias_leaf = commitment_to_lanes16(&commitment_x_plus_p);
        assert!(Poseidon2NoteTree::verify_membership16(
            wide_honest_root,
            honest_leaf,
            &wide_honest_proof
        ));
        assert!(!Poseidon2NoteTree::verify_membership16(
            wide_honest_root,
            alias_leaf,
            &wide_honest_proof
        ));

        let mut forged = wide_honest_proof;
        forged.leaf = alias_leaf;
        assert!(!Poseidon2NoteTree::verify_membership16(
            wide_honest_root,
            alias_leaf,
            &forged
        ));
    }

    #[test]
    fn production_note_tree16_keeps_positions_and_recovery_aligned() {
        let commitments: Vec<[u8; 32]> = (0..11)
            .map(|i| {
                let mut commitment = [0u8; 32];
                commitment[0] = i;
                commitment[14] = i.wrapping_mul(17);
                commitment[31] = i.wrapping_mul(41);
                commitment
            })
            .collect();
        let mut live = Poseidon2NoteTree::with_depth(4);
        for (expected_position, commitment) in commitments.iter().enumerate() {
            assert_eq!(live.append_blake3_commitment(commitment), expected_position);
        }
        assert_eq!(live.size(), live.leaves16().len());

        let live_root = live.faithful_root();
        let mut recovered = Poseidon2NoteTree::from_blake3_commitments(&commitments, 4);
        assert_eq!(live_root, recovered.faithful_root());
        for (position, commitment) in commitments.iter().enumerate() {
            let proof = recovered.prove_membership16(position).unwrap();
            assert!(Poseidon2NoteTree::verify_membership16(
                live_root,
                commitment_to_lanes16(commitment),
                &proof
            ));
        }
    }
}
