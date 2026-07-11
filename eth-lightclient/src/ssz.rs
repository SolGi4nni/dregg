//! Minimal, spec-correct SSZ `hash_tree_root` + Merkle-branch verification for the
//! handful of containers the Altair light client needs.
//!
//! References (ethereum/consensus-specs, ssz/merkle-proofs.md and phase0/beacon-chain.md):
//!   - merkleize(chunks): pad the chunk count up to the next power of two with
//!     all-zero 32-byte chunks, then hash pairwise up to a single root.
//!     hash(a,b) = SHA-256(a || b).
//!   - A `uintN` leaf is little-endian, right-padded to 32 bytes.
//!   - A `bytesN` (N <= 32) leaf is the bytes right-padded to 32.
//!   - A `Container` root = merkleize([htr(field_0), .., htr(field_{k-1})]).
//!   - A `Vector[B, N]` of `bytesM` root = merkleize([htr(elem_0), .., htr(elem_{N-1})]).
//!   - `is_valid_merkle_branch` per phase0/beacon-chain.md.

use sha2::{Digest, Sha256};

/// SHA-256(a || b) — the SSZ merkle hash of two 32-byte chunks.
#[inline]
pub fn hash_pair(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(a);
    h.update(b);
    let out = h.finalize();
    let mut r = [0u8; 32];
    r.copy_from_slice(&out);
    r
}

/// Merkleize a vector of 32-byte chunks: pad up to the next power of two with
/// zero chunks, then hash pairwise up the tree. Returns the root.
///
/// Note: this handles the fixed-length containers/vectors used here (no
/// variable-length list length-mixing, which those types do not need).
pub fn merkleize(mut chunks: Vec<[u8; 32]>) -> [u8; 32] {
    if chunks.is_empty() {
        return [0u8; 32];
    }
    let mut n = 1usize;
    while n < chunks.len() {
        n <<= 1;
    }
    chunks.resize(n, [0u8; 32]);
    while chunks.len() > 1 {
        let mut next = Vec::with_capacity(chunks.len() / 2);
        let mut i = 0;
        while i < chunks.len() {
            next.push(hash_pair(&chunks[i], &chunks[i + 1]));
            i += 2;
        }
        chunks = next;
    }
    chunks[0]
}

/// hash_tree_root of a `uint64` field: little-endian, right-padded to 32 bytes.
#[inline]
pub fn htr_u64(x: u64) -> [u8; 32] {
    let mut c = [0u8; 32];
    c[..8].copy_from_slice(&x.to_le_bytes());
    c
}

/// hash_tree_root of a `BLSPubkey` (bytes48): pack into two chunks (32 | 16+pad)
/// and merkleize them. Equivalent to hash(pk[0..32] || (pk[32..48] ++ 16 zeros)).
pub fn htr_bytes48(pk: &[u8; 48]) -> [u8; 32] {
    let mut c0 = [0u8; 32];
    c0.copy_from_slice(&pk[0..32]);
    let mut c1 = [0u8; 32];
    c1[..16].copy_from_slice(&pk[32..48]);
    hash_pair(&c0, &c1)
}

/// SSZ `is_valid_merkle_branch` (phase0/beacon-chain.md).
///
/// `index` is the SUBTREE index (0-based leaf position within the depth-`branch.len()`
/// subtree), i.e. `generalized_index % 2**depth`, NOT the generalized index itself.
/// `depth` is implied by `branch.len()`.
///
/// ```text
/// value = leaf
/// for i in 0..depth:
///     if (index >> i) & 1: value = hash(branch[i] || value)
///     else:                value = hash(value || branch[i])
/// return value == root
/// ```
pub fn is_valid_merkle_branch(
    leaf: &[u8; 32],
    branch: &[[u8; 32]],
    index: u64,
    root: &[u8; 32],
) -> bool {
    let mut value = *leaf;
    for (i, node) in branch.iter().enumerate() {
        if (index >> i) & 1 == 1 {
            value = hash_pair(node, &value);
        } else {
            value = hash_pair(&value, node);
        }
    }
    &value == root
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merkleize_pads_to_power_of_two() {
        // 5 leaves must pad to 8, giving a 3-level tree.
        let leaves: Vec<[u8; 32]> = (0..5u8).map(|i| [i; 32]).collect();
        let root = merkleize(leaves.clone());
        // Recompute by hand: pad to 8.
        let z = [0u8; 32];
        let mut lv = leaves;
        lv.push(z);
        lv.push(z);
        lv.push(z);
        let a = hash_pair(&lv[0], &lv[1]);
        let b = hash_pair(&lv[2], &lv[3]);
        let c = hash_pair(&lv[4], &lv[5]);
        let d = hash_pair(&lv[6], &lv[7]);
        let ab = hash_pair(&a, &b);
        let cd = hash_pair(&c, &d);
        assert_eq!(root, hash_pair(&ab, &cd));
    }
}
