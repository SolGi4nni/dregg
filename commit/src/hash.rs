//! Hash functions for the commitment scheme.
//!
//! Uses BLAKE3 as a placeholder for algebraic Poseidon hash. The API is designed
//! so that swapping to real Poseidon over a specific field requires changing only
//! this module.
//!
//! # BLAKE3 vs Poseidon2: Architecture Decision
//!
//! This module uses BLAKE3, which is the CORRECT choice for external-facing operations
//! (storage, networking, Ed25519 signature domains, tooling interop). BLAKE3 is:
//! - 10-100x faster than Poseidon2 for non-ZK uses
//! - Widely supported by external tooling and libraries
//! - Appropriate for all paths that never enter a STARK/SNARK circuit
//!
//! The Poseidon2 tree in `poseidon2_tree.rs` provides the ZK-friendly alternative
//! for in-circuit use. These two systems intentionally coexist:
//!
//! - **BLAKE3** (this module): non-ZK paths — storage keys, gossip message hashes,
//!   capability token derivation, general-purpose Merkle commitments.
//! - **Poseidon2** (`poseidon2_tree.rs`): STARK-provable operations — note tree
//!   commitments, nullifier sets, IVC hash chains, anything that must be verified
//!   inside a circuit.
//!
//! This is not a migration TODO — it is the intended dual-hash architecture.

use std::sync::LazyLock;

/// The width of our "Poseidon-like" hash: 4 inputs → 1 output.
pub const HASH_ARITY: usize = 4;

/// Hash a single leaf value (domain-separated).
pub fn hash_leaf(data: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-commit leaf v1");
    hasher.update(data);
    *hasher.finalize().as_bytes()
}

/// Hash 4 children together (simulating 4-ary Poseidon).
/// Domain-separated from leaf hashing to prevent second-preimage attacks.
pub fn hash_node(children: &[[u8; 32]; 4]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-commit node v1");
    for child in children {
        hasher.update(child);
    }
    *hasher.finalize().as_bytes()
}

/// Hash for an empty subtree at a given depth.
/// `depth` 0 = leaf level (empty leaf), depth 1 = one level above leaves, etc.
pub fn empty_hash(depth: usize) -> [u8; 32] {
    if depth == 0 {
        return *EMPTY_LEAF;
    }
    let child = empty_hash(depth - 1);
    hash_node(&[child, child, child, child])
}

/// Precomputed empty leaf hash: domain-separated hash of empty input.
///
/// This MUST be the output of `hash_leaf(b"")` to ensure domain separation
/// from internal node hashes. Using raw `[0u8; 32]` would create a collision
/// risk where an empty leaf could be confused with a node hash output.
///
/// We use `LazyLock` because `blake3::Hasher::new_derive_key` is not `const fn`.
pub static EMPTY_LEAF: LazyLock<[u8; 32]> = LazyLock::new(|| hash_leaf(b""));

/// Maximum depth for cached empty hashes (covers the 16-level tree with margin).
const MAX_CACHED_DEPTH: usize = 32;

/// Precomputed empty hashes at each depth, computed once.
static EMPTY_HASHES: LazyLock<Vec<[u8; 32]>> = LazyLock::new(|| {
    let mut hashes = Vec::with_capacity(MAX_CACHED_DEPTH + 1);
    hashes.push(*EMPTY_LEAF);
    for i in 1..=MAX_CACHED_DEPTH {
        let prev = hashes[i - 1];
        hashes.push(hash_node(&[prev, prev, prev, prev]));
    }
    hashes
});

/// Compute the empty hash for a given depth iteratively (avoids deep recursion).
/// Results are cached for depths up to 32 (the typical maximum tree depth).
pub fn empty_hash_at_depth(depth: usize) -> [u8; 32] {
    if depth <= MAX_CACHED_DEPTH {
        return EMPTY_HASHES[depth];
    }
    // Fallback for unexpectedly deep trees (should not happen in practice).
    let mut h = EMPTY_HASHES[MAX_CACHED_DEPTH];
    for _ in MAX_CACHED_DEPTH..depth {
        h = hash_node(&[h, h, h, h]);
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leaf_and_node_differ() {
        let data = b"hello";
        let leaf = hash_leaf(data);
        // Node of 4 copies of the leaf.
        let node = hash_node(&[leaf, leaf, leaf, leaf]);
        assert_ne!(leaf, node);
    }

    #[test]
    fn domain_separation() {
        // Same input bytes, but leaf vs node should differ.
        let bytes = [0u8; 32];
        let leaf = hash_leaf(&bytes);
        let node = hash_node(&[bytes, bytes, bytes, bytes]);
        assert_ne!(leaf, node);
    }

    #[test]
    fn empty_hash_consistency() {
        let h0 = empty_hash_at_depth(0);
        assert_eq!(h0, *EMPTY_LEAF);

        let h1 = empty_hash_at_depth(1);
        let el = *EMPTY_LEAF;
        assert_eq!(h1, hash_node(&[el, el, el, el]));

        let h2 = empty_hash_at_depth(2);
        assert_eq!(h2, hash_node(&[h1, h1, h1, h1]));
    }
}
