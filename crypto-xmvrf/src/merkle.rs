//! A binary Merkle tree over `2^height` leaves, with authentication paths.
//!
//! The tree is the UNIQUENESS engine. Its leaf hashes and internal nodes are all
//! PUBLIC (no secret material), so a prover can store the whole tree and hand out
//! authentication paths freely; only the leaf pre-images (`y`, `r`) stay secret.
//!
//! **Binding property (this is what UNIQUENESS rests on).** For a fixed `root`
//! and a fixed leaf `index`, at most one leaf value authenticates to `root`:
//! any second leaf value with a verifying path yields two distinct child pairs
//! hashing to a common ancestor somewhere up the path — a collision of
//! [`crate::hash::hash_node`] (blake3). So under collision resistance the
//! authenticated leaf at each position is unique.

use crate::hash::{hash_node, Bytes32};

/// A fully materialised Merkle tree. `levels[0]` is the leaf layer;
/// `levels[height]` is the single root. All values are public.
#[derive(Clone, Debug)]
pub struct MerkleTree {
    height: u8,
    levels: Vec<Vec<Bytes32>>,
}

impl MerkleTree {
    /// Build the tree from exactly `2^height` leaf hashes (bottom-up).
    ///
    /// # Panics
    /// If `leaves.len() != 2^height`.
    pub fn build(height: u8, leaves: Vec<Bytes32>) -> Self {
        let expected = 1usize << height;
        assert_eq!(
            leaves.len(),
            expected,
            "MerkleTree::build expects exactly 2^height = {expected} leaves, got {}",
            leaves.len()
        );
        let mut levels: Vec<Vec<Bytes32>> = Vec::with_capacity(height as usize + 1);
        levels.push(leaves);
        for _ in 0..height {
            let prev = levels.last().unwrap();
            let mut next = Vec::with_capacity(prev.len() / 2);
            let mut i = 0;
            while i < prev.len() {
                next.push(hash_node(&prev[i], &prev[i + 1]));
                i += 2;
            }
            levels.push(next);
        }
        MerkleTree { height, levels }
    }

    /// The Merkle root (the public commitment to all leaves).
    pub fn root(&self) -> Bytes32 {
        self.levels[self.height as usize][0]
    }

    /// Tree height (`log2` of the leaf count).
    pub fn height(&self) -> u8 {
        self.height
    }

    /// The authentication path for leaf `index`: the sibling hash at every level,
    /// from the leaf layer up to (but excluding) the root.
    ///
    /// # Panics
    /// If `index >= 2^height`.
    pub fn auth_path(&self, index: u64) -> Vec<Bytes32> {
        assert!(index < (1u64 << self.height), "leaf index out of range");
        let mut path = Vec::with_capacity(self.height as usize);
        let mut idx = index as usize;
        for level in 0..self.height as usize {
            let sibling = idx ^ 1;
            path.push(self.levels[level][sibling]);
            idx >>= 1;
        }
        path
    }
}

/// Recompute the root implied by `leaf` sitting at `index` under `path`, and
/// compare it to `root`. This is the verifier-side check; it uses only public
/// hashing (no secret, no tree — just the path the prover supplied).
///
/// Returns `false` if the path length disagrees with `height` or the index is
/// out of range.
pub fn verify_path(
    root: &Bytes32,
    height: u8,
    index: u64,
    leaf: &Bytes32,
    path: &[Bytes32],
) -> bool {
    if path.len() != height as usize {
        return false;
    }
    if index >= (1u64 << height) {
        return false;
    }
    let mut acc = *leaf;
    let mut idx = index as usize;
    for sibling in path {
        acc = if idx & 1 == 0 {
            hash_node(&acc, sibling)
        } else {
            hash_node(sibling, &acc)
        };
        idx >>= 1;
    }
    &acc == root
}
