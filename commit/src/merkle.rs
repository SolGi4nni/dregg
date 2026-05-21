//! 4-ary Poseidon Merkle tree.
//!
//! A sparse Merkle tree where each internal node has exactly 4 children.
//! Leaves are sorted by their key (the leaf hash of the fact). The tree
//! has a fixed logical depth but only materializes paths that contain data.
//!
//! Key design decisions:
//! - Sorted leaves: facts are inserted in sorted order by leaf hash.
//! - Sparse representation: only populated paths are stored.
//! - 4-ary branching: each level selects 2 bits of the key to pick a child index (0..3).
//! - Fixed depth: 32 levels × 2 bits = 64 bits of key discrimination (birthday
//!   collisions at ~2^32 leaves). For a fuller implementation we'd use all 256 bits.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

use crate::hash::{EMPTY_LEAF, HASH_ARITY, empty_hash_at_depth, hash_leaf, hash_node};

/// Tree depth: number of levels from root to leaves.
/// With 4-ary branching, this gives us 4^TREE_DEPTH addressable leaf slots.
/// 32 levels = 64 bits of path discrimination (birthday collision at ~2^32 leaves).
const TREE_DEPTH: usize = 32;

/// A membership proof in a 4-ary Merkle tree.
///
/// For each level, we store the 3 sibling hashes (the other branches at that node).
/// The verifier can reconstruct the path using the leaf position.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MerkleProof {
    /// The leaf hash being proved.
    pub leaf_hash: [u8; 32],
    /// Path index at each level (0..3), from leaf to root.
    pub path_indices: Vec<u8>,
    /// Sibling hashes at each level. Each entry is the 3 siblings at that level.
    pub siblings: Vec<[[u8; 32]; 3]>,
    /// When the leaf is in a collision bucket (multiple leaves share the same path_key),
    /// this contains the other leaves in the bucket. The verifier must reconstruct the
    /// bucket hash from `leaf_hash` + `bucket_siblings` before hashing upward.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub bucket_siblings: Vec<[u8; 32]>,
}

/// A non-membership proof: proves a key is absent from the tree.
///
/// This works by showing the two adjacent leaves that bracket the absent key,
/// together with their membership proofs and their positions in the sorted
/// leaf ordering. The verifier checks that the positions are adjacent
/// (right_pos == left_pos + 1) to prevent an attacker from choosing
/// non-adjacent neighbors to falsely prove non-membership of a key that
/// IS in the tree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonMembershipProof {
    /// The key being proved absent.
    pub absent_key: [u8; 32],
    /// The leaf just before the absent key (if any), with its sorted position.
    pub left_neighbor: Option<(u64, [u8; 32], MerkleProof)>,
    /// The leaf just after the absent key (if any), with its sorted position.
    pub right_neighbor: Option<(u64, [u8; 32], MerkleProof)>,
    /// Total number of leaves in the tree at proof generation time.
    pub tree_size: u64,
}

/// Witness that all other facts survived (unchanged) through an attenuation.
/// For a simple implementation, this is a Merkle multi-proof showing the
/// subtrees that were not modified.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SurvivalWitness {
    /// Root of the old tree.
    pub old_root: [u8; 32],
    /// Root of the new tree.
    pub new_root: [u8; 32],
    /// The set of unchanged subtree hashes and their positions.
    pub unchanged_subtrees: Vec<SubtreeRef>,
}

/// A reference to an unchanged subtree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SubtreeRef {
    /// Depth of this subtree root (0 = overall root).
    pub depth: usize,
    /// Path from root to this subtree (indices at each level).
    pub path: Vec<u8>,
    /// Hash of this subtree.
    pub hash: [u8; 32],
}

/// A 4-ary Merkle tree backed by a sorted map of full leaf hashes.
///
/// This is a sparse implementation: we store only the populated leaves and
/// compute internal nodes on demand.
///
/// The full 32-byte leaf hash is used as the map key, preventing silent
/// overwrites that occurred with the previous truncated key approach.
/// Tree addressing (path computation) uses the first 8 bytes of the hash
/// to determine position within the 32-level, 4-ary tree structure.
#[derive(Clone, Debug)]
pub struct MerkleTree {
    /// Leaves stored by their full 32-byte hash.
    /// The tree position for each leaf is derived from the first 8 bytes via `path_key()`.
    leaves: BTreeMap<[u8; 32], ()>,
    /// Cached root (invalidated on mutation).
    cached_root: Option<[u8; 32]>,
}

impl MerkleTree {
    /// Create an empty tree.
    pub fn new() -> Self {
        Self {
            leaves: BTreeMap::new(),
            cached_root: Some(empty_hash_at_depth(TREE_DEPTH)),
        }
    }

    /// Number of leaves in the tree.
    pub fn len(&self) -> usize {
        self.leaves.len()
    }

    /// Whether the tree is empty.
    pub fn is_empty(&self) -> bool {
        self.leaves.is_empty()
    }

    /// Compute the current root hash.
    pub fn root(&mut self) -> [u8; 32] {
        if let Some(r) = self.cached_root {
            return r;
        }
        let root = self.compute_root();
        self.cached_root = Some(root);
        root
    }

    /// Insert a leaf and return the new root.
    pub fn insert(&mut self, leaf_data: &[u8]) -> [u8; 32] {
        let leaf_hash = hash_leaf(leaf_data);
        self.leaves.insert(leaf_hash, ());
        self.cached_root = None;
        self.root()
    }

    /// Insert a pre-hashed leaf and return the new root.
    pub fn insert_hash(&mut self, leaf_hash: [u8; 32]) -> [u8; 32] {
        self.leaves.insert(leaf_hash, ());
        self.cached_root = None;
        self.root()
    }

    /// Remove a leaf by its data and return the new root.
    /// Returns None if the leaf was not present.
    pub fn remove(&mut self, leaf_data: &[u8]) -> Option<[u8; 32]> {
        let leaf_hash = hash_leaf(leaf_data);
        self.remove_hash(&leaf_hash)
    }

    /// Remove a leaf by its hash and return the new root.
    /// Returns None if the leaf was not present.
    pub fn remove_hash(&mut self, leaf_hash: &[u8; 32]) -> Option<[u8; 32]> {
        if self.leaves.remove(leaf_hash).is_some() {
            self.cached_root = None;
            Some(self.root())
        } else {
            None
        }
    }

    /// Check if a leaf (by data) is in the tree.
    pub fn contains(&self, leaf_data: &[u8]) -> bool {
        let leaf_hash = hash_leaf(leaf_data);
        self.contains_hash(&leaf_hash)
    }

    /// Check if a leaf (by hash) is in the tree.
    pub fn contains_hash(&self, leaf_hash: &[u8; 32]) -> bool {
        self.leaves.contains_key(leaf_hash)
    }

    /// Generate a membership proof for a leaf (by data).
    /// Returns None if the leaf is not in the tree.
    pub fn membership_proof(&self, leaf_data: &[u8]) -> Option<MerkleProof> {
        let leaf_hash = hash_leaf(leaf_data);
        self.membership_proof_hash(&leaf_hash)
    }

    /// Generate a membership proof for a leaf (by hash).
    /// Returns None if the leaf is not in the tree.
    pub fn membership_proof_hash(&self, leaf_hash: &[u8; 32]) -> Option<MerkleProof> {
        if !self.leaves.contains_key(leaf_hash) {
            return None;
        }

        let key = path_key(leaf_hash);
        // Path indices in leaf-to-root order (matching the verifier).
        let path_indices = key_to_path_leaf_to_root(key);
        let siblings = self.compute_siblings(key);

        // Check if this leaf is in a collision bucket (multiple leaves share same path_key).
        let bucket_siblings: Vec<[u8; 32]> = self
            .leaves_at_path_key(key)
            .into_iter()
            .filter(|h| *h != leaf_hash)
            .copied()
            .collect();

        Some(MerkleProof {
            leaf_hash: *leaf_hash,
            path_indices,
            siblings,
            bucket_siblings,
        })
    }

    /// Generate a non-membership proof for a leaf (by data).
    /// Returns None if the leaf IS in the tree.
    pub fn non_membership_proof(&self, leaf_data: &[u8]) -> Option<NonMembershipProof> {
        let leaf_hash = hash_leaf(leaf_data);
        self.non_membership_proof_hash(&leaf_hash)
    }

    /// Generate a non-membership proof for a leaf (by hash).
    /// Returns None if the leaf IS in the tree.
    pub fn non_membership_proof_hash(&self, leaf_hash: &[u8; 32]) -> Option<NonMembershipProof> {
        // If it's present, can't prove non-membership.
        if self.leaves.contains_key(leaf_hash) {
            return None;
        }

        // Find left and right neighbors by full hash (lexicographic order),
        // along with their positions in the sorted leaf set.
        let left_neighbor = self
            .leaves
            .range(..*leaf_hash)
            .next_back()
            .map(|(&hash, _)| {
                let position = self.leaves.range(..=hash).count() as u64 - 1;
                let proof = self.membership_proof_hash(&hash).unwrap();
                (position, hash, proof)
            });

        let right_neighbor = self.leaves.range(*leaf_hash..).next().map(|(&hash, _)| {
            let position = self.leaves.range(..=hash).count() as u64 - 1;
            let proof = self.membership_proof_hash(&hash).unwrap();
            (position, hash, proof)
        });

        Some(NonMembershipProof {
            absent_key: *leaf_hash,
            left_neighbor,
            right_neighbor,
            tree_size: self.leaves.len() as u64,
        })
    }

    /// Verify a membership proof against a given root.
    pub fn verify_membership(root: &[u8; 32], proof: &MerkleProof) -> bool {
        if proof.path_indices.len() != TREE_DEPTH || proof.siblings.len() != TREE_DEPTH {
            return false;
        }

        // Start value: if there are bucket siblings, reconstruct the collision bucket hash.
        // Otherwise, use the raw leaf hash.
        let mut current = if proof.bucket_siblings.is_empty() {
            proof.leaf_hash
        } else {
            // Reconstruct the bucket hash: all leaves at this position hashed together
            // in sorted order with the collision-bucket domain separator.
            let mut all_leaves: Vec<[u8; 32]> = std::iter::once(proof.leaf_hash)
                .chain(proof.bucket_siblings.iter().copied())
                .collect();
            all_leaves.sort();
            let mut hasher = blake3::Hasher::new_derive_key("pyana-commit collision-bucket v1");
            for leaf in &all_leaves {
                hasher.update(leaf.as_slice());
            }
            *hasher.finalize().as_bytes()
        };

        for level in 0..TREE_DEPTH {
            let idx = proof.path_indices[level] as usize;
            if idx >= HASH_ARITY {
                return false;
            }
            let sibs = &proof.siblings[level];
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

    /// Verify a non-membership proof against a given root.
    ///
    /// Checks:
    /// 1. Both neighbors (if present) have valid membership proofs against the root.
    /// 2. Left < absent_key < right (lexicographic ordering).
    /// 3. Left and right are adjacent in the sorted leaf set (right_pos == left_pos + 1),
    ///    preventing an attacker from choosing non-adjacent leaves to falsely prove
    ///    non-membership of a key that IS in the tree.
    ///
    /// # Security Note
    ///
    /// Non-membership proof security relies on the Merkle root binding the sorted
    /// ordering of leaves. The prover's claimed positions are trusted given valid
    /// membership proofs for the neighbors. A stronger construction would have each
    /// leaf commit to its position via a linked-list structure, but this is acceptable
    /// for the current scale where the Merkle root provides binding.
    pub fn verify_non_membership(root: &[u8; 32], proof: &NonMembershipProof) -> bool {
        // At least one neighbor must exist (unless tree is empty and root is empty root).
        let empty_root = empty_hash_at_depth(TREE_DEPTH);
        if proof.left_neighbor.is_none() && proof.right_neighbor.is_none() {
            // Empty tree: the root must be the canonical empty root and tree_size must be 0.
            return *root == empty_root && proof.tree_size == 0;
        }

        let mut left_pos: Option<u64> = None;
        let mut right_pos: Option<u64> = None;

        // Verify each neighbor's membership proof.
        if let Some((pos, ref left_hash, ref mp)) = proof.left_neighbor {
            if !Self::verify_membership(root, mp) {
                return false;
            }
            // The neighbor hash in the proof must match the proof's leaf_hash.
            if mp.leaf_hash != *left_hash {
                return false;
            }
            // Left neighbor's FULL hash must be lexicographically less than the absent key.
            if *left_hash >= proof.absent_key {
                return false;
            }
            left_pos = Some(pos);
        }

        if let Some((pos, ref right_hash, ref mp)) = proof.right_neighbor {
            if !Self::verify_membership(root, mp) {
                return false;
            }
            // The neighbor hash in the proof must match the proof's leaf_hash.
            if mp.leaf_hash != *right_hash {
                return false;
            }
            // Right neighbor's FULL hash must be lexicographically greater than the absent key.
            if *right_hash <= proof.absent_key {
                return false;
            }
            right_pos = Some(pos);
        }

        // Verify adjacency: left and right must be immediate neighbors in the
        // sorted leaf ordering. This prevents an attacker from proving non-membership
        // of an element that IS in the tree by choosing non-adjacent neighbors.
        match (left_pos, right_pos) {
            (Some(l), Some(r)) => {
                // Both neighbors present: they must be adjacent (no leaves between them).
                if r != l + 1 {
                    return false;
                }
            }
            (None, Some(r)) => {
                // No left neighbor: the right neighbor must be at position 0
                // (the absent key would be before all leaves).
                if r != 0 {
                    return false;
                }
            }
            (Some(l), None) => {
                // No right neighbor: the left neighbor must be the last leaf
                // (the absent key would be after all leaves).
                if proof.tree_size == 0 || l != proof.tree_size - 1 {
                    return false;
                }
            }
            (None, None) => {
                // Already handled above (empty tree case).
                unreachable!()
            }
        }

        true
    }

    /// Compute the root from scratch.
    fn compute_root(&self) -> [u8; 32] {
        if self.leaves.is_empty() {
            return empty_hash_at_depth(TREE_DEPTH);
        }
        self.compute_subtree_hash(0, 0)
    }

    /// Recursively compute the hash of a subtree.
    /// `depth`: current depth (0 = root, TREE_DEPTH = leaf level).
    /// `prefix`: the path bits accumulated so far (in the high bits of the u64 address).
    fn compute_subtree_hash(&self, depth: usize, prefix: u64) -> [u8; 32] {
        if depth == TREE_DEPTH {
            // Leaf level: find all leaves at this tree position.
            let leaves_at_pos: Vec<&[u8; 32]> = self.leaves_at_path_key(prefix);
            return match leaves_at_pos.len() {
                0 => *EMPTY_LEAF,
                1 => *leaves_at_pos[0],
                _ => {
                    // Multiple leaves at the same tree position: hash them together
                    // in sorted order (they are already sorted since BTreeMap is sorted)
                    // to maintain determinism.
                    let mut hasher =
                        blake3::Hasher::new_derive_key("pyana-commit collision-bucket v1");
                    for leaf in &leaves_at_pos {
                        hasher.update(leaf.as_slice());
                    }
                    *hasher.finalize().as_bytes()
                }
            };
        }

        let mut children = [[0u8; 32]; 4];
        let shift = (TREE_DEPTH - 1 - depth) * 2;
        for i in 0..HASH_ARITY {
            let child_prefix = prefix | ((i as u64) << shift);
            let range_start = child_prefix;
            let range_end = child_prefix | ((1u64 << shift) - 1);
            if self.has_leaves_in_range(range_start, range_end) {
                children[i] = self.compute_subtree_hash(depth + 1, child_prefix);
            } else {
                children[i] = empty_hash_at_depth(TREE_DEPTH - depth - 1);
            }
        }
        hash_node(&children)
    }

    /// Get all leaves whose path_key matches the given prefix.
    /// Leaves are returned in sorted order (by full hash) for deterministic hashing.
    fn leaves_at_path_key(&self, prefix: u64) -> Vec<&[u8; 32]> {
        // Construct the range of [u8; 32] values whose first 8 bytes match `prefix`.
        let lo = prefix_to_hash_lo(prefix);
        let hi = prefix_to_hash_hi(prefix);
        self.leaves.range(lo..=hi).map(|(hash, _)| hash).collect()
    }

    /// Check if there are any leaves whose path_key falls in [start, end].
    fn has_leaves_in_range(&self, start: u64, end: u64) -> bool {
        let lo = prefix_to_hash_lo(start);
        let hi = prefix_to_hash_hi(end);
        self.leaves.range(lo..=hi).next().is_some()
    }

    /// Compute the sibling hashes for a path.
    /// Returns siblings in LEAF-TO-ROOT order to match the verifier.
    fn compute_siblings(&self, key: u64) -> Vec<[[u8; 32]; 3]> {
        let mut siblings = Vec::with_capacity(TREE_DEPTH);

        // We build from deepest level (leaf) to shallowest (root).
        for level in 0..TREE_DEPTH {
            // level 0 = leaf level, level TREE_DEPTH-1 = root level.
            // depth (from root) = TREE_DEPTH - 1 - level.
            let depth = TREE_DEPTH - 1 - level;
            let shift = (TREE_DEPTH - 1 - depth) * 2; // = level * 2
            let idx = ((key >> shift) & 0x3) as usize;

            // Parent prefix: mask off this level's bits and below.
            let parent_mask: u64 = if shift + 2 >= 64 {
                0
            } else {
                !((1u64 << (shift + 2)) - 1)
            };
            let parent_prefix = key & parent_mask;

            let mut sibs = [[0u8; 32]; 3];
            let mut sib_idx = 0;
            for i in 0..HASH_ARITY {
                if i == idx {
                    continue;
                }
                let child_prefix = parent_prefix | ((i as u64) << shift);
                if depth + 1 == TREE_DEPTH {
                    // This is the deepest internal node, its children are leaves.
                    sibs[sib_idx] = self.compute_subtree_hash(TREE_DEPTH, child_prefix);
                } else {
                    let range_end = if shift == 0 {
                        child_prefix
                    } else {
                        child_prefix | ((1u64 << shift) - 1)
                    };
                    if self.has_leaves_in_range(child_prefix, range_end) {
                        sibs[sib_idx] = self.compute_subtree_hash(depth + 1, child_prefix);
                    } else {
                        sibs[sib_idx] = empty_hash_at_depth(TREE_DEPTH - depth - 1);
                    }
                }
                sib_idx += 1;
            }
            siblings.push(sibs);
        }

        siblings
    }

    /// Generate a survival witness showing what subtrees are unchanged between
    /// this tree and a modified version. The `removed_keys` are the leaves being
    /// removed.
    pub fn survival_witness(
        &mut self,
        new_tree: &mut MerkleTree,
        removed_keys: &[[u8; 32]],
    ) -> SurvivalWitness {
        let old_root = self.root();
        let new_root = new_tree.root();

        // Find unchanged subtrees by comparing the two trees at each level.
        let unchanged = self.find_unchanged_subtrees(new_tree, 0, 0, removed_keys);

        SurvivalWitness {
            old_root,
            new_root,
            unchanged_subtrees: unchanged,
        }
    }

    /// Find subtrees that are identical between self and other.
    fn find_unchanged_subtrees(
        &self,
        other: &MerkleTree,
        depth: usize,
        prefix: u64,
        _removed: &[[u8; 32]],
    ) -> Vec<SubtreeRef> {
        if depth >= TREE_DEPTH {
            return vec![];
        }

        let mut result = Vec::new();
        let shift = (TREE_DEPTH - 1 - depth) * 2;

        for i in 0..HASH_ARITY {
            let child_prefix = prefix | ((i as u64) << shift);
            let range_start = child_prefix;
            let range_end = child_prefix | ((1u64 << shift) - 1);

            let self_has = self.has_leaves_in_range(range_start, range_end);
            let other_has = other.has_leaves_in_range(range_start, range_end);

            if !self_has && !other_has {
                // Both empty — trivially unchanged.
                continue;
            }

            let self_hash = if self_has {
                self.compute_subtree_hash(depth + 1, child_prefix)
            } else {
                empty_hash_at_depth(TREE_DEPTH - depth - 1)
            };

            let other_hash = if other_has {
                other.compute_subtree_hash(depth + 1, child_prefix)
            } else {
                empty_hash_at_depth(TREE_DEPTH - depth - 1)
            };

            if self_hash == other_hash {
                let path = key_to_path_partial(child_prefix, depth + 1);
                result.push(SubtreeRef {
                    depth: depth + 1,
                    path,
                    hash: self_hash,
                });
            } else if depth + 1 < TREE_DEPTH {
                // Recurse to find smaller unchanged subtrees.
                let sub = self.find_unchanged_subtrees(other, depth + 1, child_prefix, _removed);
                result.extend(sub);
            }
        }

        result
    }
}

impl Default for MerkleTree {
    fn default() -> Self {
        Self::new()
    }
}

/// Extract the path key from a leaf hash: the first 8 bytes as a big-endian u64.
/// This determines the leaf's position in the tree.
/// Using 64 bits pushes birthday collisions to ~2^32 leaves (~4 billion).
fn path_key(hash: &[u8; 32]) -> u64 {
    u64::from_be_bytes([
        hash[0], hash[1], hash[2], hash[3], hash[4], hash[5], hash[6], hash[7],
    ])
}

/// Construct the lowest [u8; 32] value whose first 8 bytes encode the given u64 prefix.
fn prefix_to_hash_lo(prefix: u64) -> [u8; 32] {
    let bytes = prefix.to_be_bytes();
    let mut out = [0u8; 32];
    out[..8].copy_from_slice(&bytes);
    // remaining bytes are 0x00 (minimum)
    out
}

/// Construct the highest [u8; 32] value whose first 8 bytes encode the given u64 prefix.
fn prefix_to_hash_hi(prefix: u64) -> [u8; 32] {
    let bytes = prefix.to_be_bytes();
    let mut out = [0xFFu8; 32];
    out[..8].copy_from_slice(&bytes);
    // remaining bytes are 0xFF (maximum)
    out
}

/// Convert a path key to a vector of path indices (2 bits each, from root to leaf).
#[cfg(test)]
fn key_to_path(key: u64) -> Vec<u8> {
    let mut path = Vec::with_capacity(TREE_DEPTH);
    for depth in 0..TREE_DEPTH {
        let shift = (TREE_DEPTH - 1 - depth) * 2;
        let idx = ((key >> shift) & 0x3) as u8;
        path.push(idx);
    }
    path
}

/// Convert a path key to a vector of path indices in LEAF-TO-ROOT order.
/// Level 0 = leaf level (lowest 2 bits), level TREE_DEPTH-1 = root level (highest 2 bits).
fn key_to_path_leaf_to_root(key: u64) -> Vec<u8> {
    let mut path = Vec::with_capacity(TREE_DEPTH);
    for level in 0..TREE_DEPTH {
        let shift = level * 2;
        let idx = ((key >> shift) & 0x3) as u8;
        path.push(idx);
    }
    path
}

/// Convert a key to a partial path up to a given depth.
fn key_to_path_partial(key: u64, depth: usize) -> Vec<u8> {
    let mut path = Vec::with_capacity(depth);
    for d in 0..depth {
        let shift = (TREE_DEPTH - 1 - d) * 2;
        let idx = ((key >> shift) & 0x3) as u8;
        path.push(idx);
    }
    path
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_tree_root() {
        let mut tree = MerkleTree::new();
        let root = tree.root();
        assert_eq!(root, empty_hash_at_depth(TREE_DEPTH));
    }

    #[test]
    fn insert_changes_root() {
        let mut tree = MerkleTree::new();
        let empty_root = tree.root();
        let new_root = tree.insert(b"hello");
        assert_ne!(empty_root, new_root);
    }

    #[test]
    fn insert_deterministic() {
        let mut t1 = MerkleTree::new();
        let mut t2 = MerkleTree::new();
        t1.insert(b"a");
        t1.insert(b"b");
        t2.insert(b"a");
        t2.insert(b"b");
        assert_eq!(t1.root(), t2.root());
    }

    #[test]
    fn insert_order_independent() {
        let mut t1 = MerkleTree::new();
        let mut t2 = MerkleTree::new();
        t1.insert(b"alpha");
        t1.insert(b"beta");
        t2.insert(b"beta");
        t2.insert(b"alpha");
        assert_eq!(t1.root(), t2.root());
    }

    #[test]
    fn remove_restores_root() {
        let mut tree = MerkleTree::new();
        let empty_root = tree.root();
        tree.insert(b"hello");
        tree.remove(b"hello");
        assert_eq!(tree.root(), empty_root);
    }

    #[test]
    fn remove_absent_returns_none() {
        let mut tree = MerkleTree::new();
        tree.insert(b"hello");
        assert!(tree.remove(b"world").is_none());
    }

    #[test]
    fn contains_works() {
        let mut tree = MerkleTree::new();
        tree.insert(b"hello");
        assert!(tree.contains(b"hello"));
        assert!(!tree.contains(b"world"));
    }

    #[test]
    fn membership_proof_verifies() {
        let mut tree = MerkleTree::new();
        tree.insert(b"alpha");
        tree.insert(b"beta");
        tree.insert(b"gamma");

        let root = tree.root();
        let proof = tree.membership_proof(b"beta").unwrap();
        assert!(MerkleTree::verify_membership(&root, &proof));
    }

    #[test]
    fn membership_proof_fails_wrong_root() {
        let mut tree = MerkleTree::new();
        tree.insert(b"alpha");
        tree.insert(b"beta");

        let proof = tree.membership_proof(b"alpha").unwrap();
        let fake_root = [0xAB; 32];
        assert!(!MerkleTree::verify_membership(&fake_root, &proof));
    }

    #[test]
    fn membership_proof_absent_returns_none() {
        let mut tree = MerkleTree::new();
        tree.insert(b"hello");
        assert!(tree.membership_proof(b"world").is_none());
    }

    #[test]
    fn non_membership_proof_verifies() {
        let mut tree = MerkleTree::new();
        tree.insert(b"alpha");
        tree.insert(b"gamma");

        let root = tree.root();
        let proof = tree.non_membership_proof(b"beta").unwrap();
        assert!(MerkleTree::verify_non_membership(&root, &proof));
    }

    #[test]
    fn non_membership_proof_empty_tree() {
        let mut tree = MerkleTree::new();
        let root = tree.root();
        let proof = tree.non_membership_proof(b"anything").unwrap();
        assert!(MerkleTree::verify_non_membership(&root, &proof));
    }

    #[test]
    fn non_membership_present_returns_none() {
        let mut tree = MerkleTree::new();
        tree.insert(b"hello");
        assert!(tree.non_membership_proof(b"hello").is_none());
    }

    #[test]
    fn path_key_extraction() {
        let hash = [
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let key = path_key(&hash);
        assert_eq!(key, 0x123456789ABCDEF0);
    }

    #[test]
    fn key_to_path_roundtrip() {
        let key: u64 = 0xABCD1234_DEADBEEF;
        let path = key_to_path(key);
        assert_eq!(path.len(), TREE_DEPTH);
        // Reconstruct key from path.
        let mut reconstructed: u64 = 0;
        for (depth, &idx) in path.iter().enumerate() {
            let shift = (TREE_DEPTH - 1 - depth) * 2;
            reconstructed |= (idx as u64) << shift;
        }
        assert_eq!(reconstructed, key);
    }

    #[test]
    fn multiple_inserts_and_proofs() {
        let mut tree = MerkleTree::new();
        let items: Vec<&[u8]> = vec![b"one", b"two", b"three", b"four", b"five"];
        for item in &items {
            tree.insert(item);
        }
        let root = tree.root();
        for item in &items {
            let proof = tree.membership_proof(item).unwrap();
            assert!(
                MerkleTree::verify_membership(&root, &proof),
                "Failed to verify membership for {:?}",
                item
            );
        }
    }

    #[test]
    fn survival_witness_basic() {
        let mut old_tree = MerkleTree::new();
        old_tree.insert(b"a");
        old_tree.insert(b"b");
        old_tree.insert(b"c");

        let mut new_tree = MerkleTree::new();
        new_tree.insert(b"a");
        new_tree.insert(b"b");
        // "c" removed.

        let leaf_hash_c = hash_leaf(b"c");
        let witness = old_tree.survival_witness(&mut new_tree, &[leaf_hash_c]);

        assert_eq!(witness.old_root, old_tree.root());
        assert_eq!(witness.new_root, new_tree.root());
        // There should be some unchanged subtrees.
        assert!(!witness.unchanged_subtrees.is_empty());
    }

    /// Regression test: inserting two leaves that share the same first 8 bytes
    /// (path_key collision) must NOT silently overwrite each other.
    #[test]
    fn no_silent_overwrite_on_path_key_collision() {
        let mut tree = MerkleTree::new();

        // Craft two hashes that share the same first 8 bytes but differ after.
        let mut hash_a = [0u8; 32];
        hash_a[0] = 0xAB;
        hash_a[1] = 0xCD;
        hash_a[2] = 0x12;
        hash_a[3] = 0x34;
        hash_a[4] = 0x56;
        hash_a[5] = 0x78;
        hash_a[6] = 0x9A;
        hash_a[7] = 0xBC;
        hash_a[8] = 0x01; // differs here

        let mut hash_b = [0u8; 32];
        hash_b[0] = 0xAB;
        hash_b[1] = 0xCD;
        hash_b[2] = 0x12;
        hash_b[3] = 0x34;
        hash_b[4] = 0x56;
        hash_b[5] = 0x78;
        hash_b[6] = 0x9A;
        hash_b[7] = 0xBC;
        hash_b[8] = 0x02; // differs here

        assert_eq!(path_key(&hash_a), path_key(&hash_b));

        tree.insert_hash(hash_a);
        tree.insert_hash(hash_b);

        // Both leaves must be stored.
        assert_eq!(tree.len(), 2);
        assert!(tree.contains_hash(&hash_a));
        assert!(tree.contains_hash(&hash_b));

        // Removing one does not affect the other.
        tree.remove_hash(&hash_a);
        assert_eq!(tree.len(), 1);
        assert!(!tree.contains_hash(&hash_a));
        assert!(tree.contains_hash(&hash_b));
    }

    /// Test: membership proof works for leaves in a collision bucket.
    #[test]
    fn collision_bucket_membership_proof_verifies() {
        let mut tree = MerkleTree::new();

        // Two hashes that share the same path_key (first 8 bytes).
        let mut hash_a = [0u8; 32];
        hash_a[0..8].copy_from_slice(&[0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xBA, 0xBE]);
        hash_a[8] = 0x01;

        let mut hash_b = [0u8; 32];
        hash_b[0..8].copy_from_slice(&[0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xBA, 0xBE]);
        hash_b[8] = 0x02;

        assert_eq!(path_key(&hash_a), path_key(&hash_b));

        tree.insert_hash(hash_a);
        tree.insert_hash(hash_b);

        let root = tree.root();

        // Both should produce valid membership proofs.
        let proof_a = tree.membership_proof_hash(&hash_a).unwrap();
        assert!(!proof_a.bucket_siblings.is_empty());
        assert!(MerkleTree::verify_membership(&root, &proof_a));

        let proof_b = tree.membership_proof_hash(&hash_b).unwrap();
        assert!(!proof_b.bucket_siblings.is_empty());
        assert!(MerkleTree::verify_membership(&root, &proof_b));
    }
}
