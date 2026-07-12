//! The grain's private data = a dregg cell's **umem heap**.
//!
//! In Sandstorm a grain's `/var` is a read-write bind-mount, private to that grain,
//! that the app stores its database/state in. On dregg that `/var` *is* the cell's
//! umem heap: a keyed byte store that commits to a content-addressed **`data_root`**.
//! The difference Sandstorm cannot offer: the root is a commitment, so a checkpoint
//! is re-witnessable (a backup that proves what it contains), and the transitions —
//! not just a snapshot — are what get committed.
//!
//! ## The commitment is the REAL dregg heap-root scheme (not an ad-hoc sha256 tree)
//!
//! This module commits a grain's `/var` through the **same** openable sorted-Poseidon2
//! binary Merkle tree the kernel commits a cell's heap with:
//! [`dregg_circuit::heap_root`] (`CanonicalHeapTree` / `compute_heap_root`, the exact
//! primitive `dregg_cell::compute_heap_root` wraps). Each `/var` entry `(key, value)`
//! becomes a [`dregg_circuit::heap_root::HeapLeaf`] `{ addr, value }`:
//!
//! * `addr = var_addr(key)` — a Poseidon2 felt over the domain-tagged key bytes (the
//!   real heap keys `(collection_id, key)` u32 pairs via `heap_addr`; a grain's `/var`
//!   keys are strings, so its sort key is the Poseidon2 image of the key — the same
//!   sorted-tree sort key, the same `CanonicalHeapTree`, same sentinels, same depth);
//! * `value = var_value_felt(value)` — a Poseidon2 felt digest of the value bytes
//!   (the real heap folds a 32-byte `FieldElement`; a grain value is arbitrary-length,
//!   so its committed value is the Poseidon2 digest, binding under Poseidon2 CR).
//!
//! So `Umem::commit_root_bytes()` == `dregg_circuit::heap_root::compute_heap_root` of
//! the grain's leaves, encoded to 32 bytes exactly as `dregg_cell` encodes a heap-root
//! felt (`babybear_to_bytes32` / `felt_to_bytes32`). This is the value a real
//! deployment's ledger carries for a cell's heap — NOT a bespoke sha256 root the
//! federation never stores. A single entry's inclusion under the root is provable
//! *without the rest of the heap*: [`Umem::prove`] emits an [`InclusionProof`] (the
//! `CanonicalHeapTree` sibling path, a Poseidon2/felt path), and the host-state-free
//! [`verify_inclusion`] checks `{key, value, proof, root}` alone — a visitor re-hashes
//! just the served card and confirms it is the value at `key` under a heap-root it
//! obtains independently.

use std::collections::BTreeMap;

use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{
    compute_heap_root as heap_compute_root, CanonicalHeapTree, HeapLeaf, HEAP_TREE_DEPTH,
};
use dregg_circuit::poseidon2::{hash_bytes, hash_fact};

use crate::spk::base32;

/// Domain tag for the `/var` heap ADDRESS (sort-key) felt — keeps a key-derived
/// address from ever aliasing a value-derived felt, and separates a grain `/var`
/// address from any other Poseidon2 image.
const VAR_ADDR_DOMAIN: &[u8] = b"grain/var/addr:v1\0";

/// Domain tag for the `/var` heap VALUE felt.
const VAR_VALUE_DOMAIN: &[u8] = b"grain/var/value:v1\0";

/// The canonical heap ADDRESS (sort key) of a `/var` string key: a domain-separated
/// Poseidon2 felt. The string-keyed analog of [`dregg_circuit::heap_root::heap_addr`]
/// (which addresses a `(collection_id, key)` u32 pair): a grain's `/var` is keyed by
/// strings, so the sort key is the Poseidon2 image of the domain-tagged key bytes —
/// the SAME sorted-tree sort key the real heap tree places leaves by.
pub fn var_addr(key: &str) -> BabyBear {
    let mut buf = Vec::with_capacity(VAR_ADDR_DOMAIN.len() + key.len());
    buf.extend_from_slice(VAR_ADDR_DOMAIN);
    buf.extend_from_slice(key.as_bytes());
    hash_bytes(&buf)
}

/// The heap-leaf VALUE felt committing a `/var` value blob: a domain-separated
/// Poseidon2 image of the value bytes. The real heap stores a folded 32-byte
/// `FieldElement`; a grain value is arbitrary-length, so its committed value is the
/// Poseidon2 digest of the bytes — binding under Poseidon2 collision-resistance. The
/// visitor recomputes it from the served card bytes to check inclusion.
pub fn var_value_felt(value: &[u8]) -> BabyBear {
    let mut buf = Vec::with_capacity(VAR_VALUE_DOMAIN.len() + value.len());
    buf.extend_from_slice(VAR_VALUE_DOMAIN);
    buf.extend_from_slice(value);
    hash_bytes(&buf)
}

/// The [`HeapLeaf`] for one `/var` entry — the leaf both [`Umem::commit_root_bytes`]
/// and [`Umem::prove`] build the `CanonicalHeapTree` over.
fn var_leaf(key: &str, value: &[u8]) -> HeapLeaf {
    HeapLeaf::entry(var_addr(key), var_value_felt(value))
}

/// Encode a BabyBear heap-root felt as the raw 32 bytes the federation ledger carries:
/// the felt's 4 little-endian bytes in the low positions, the rest zero — byte-identical
/// to `dregg_cell`'s `babybear_to_bytes32` / `felt_to_bytes32` (the encoding
/// `dregg_cell::compute_heap_root` returns and the canonical state commitment absorbs
/// for the `heap_root` register). Deterministic and injective on canonical BabyBear
/// values (`< p`).
pub fn felt_to_bytes32(felt: BabyBear) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0..4].copy_from_slice(&felt.as_u32().to_le_bytes());
    out
}

/// Encode a 32-byte heap root as the `heap1…` [`DataRoot`] wire string.
fn root_string(root: &[u8; 32]) -> String {
    format!("heap1{}", base32(root))
}

/// A Merkle inclusion proof that a single key's value is a leaf under a committed
/// heap-root — the [`CanonicalHeapTree`] sibling path from that leaf to the root (a
/// Poseidon2/felt path, NOT a sha256 tree). Log-sized in the tree depth, and verified
/// with [`verify_inclusion`] against `{key, value, root}` alone; no heap needed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InclusionProof {
    /// Sibling digests along the path from the leaf to the root (bottom-up), in the
    /// real `dregg_circuit::heap_root` scheme.
    pub siblings: Vec<BabyBear>,
    /// Direction bits: `directions[i] == 0` when the running node is the LEFT child at
    /// level `i` (sibling on the right), `1` otherwise. Same convention as
    /// [`CanonicalHeapTree::prove_membership`].
    pub directions: Vec<u8>,
}

/// **Verify a single-leaf inclusion proof — host-state-free.** Given only the served
/// `{key, value}`, the `proof`, and a `root` the caller trusts (obtained independently —
/// e.g. the cell's heap-root from the ledger, NOT from the serving host), recompute the
/// leaf digest `hash[addr, value]` and fold the sibling path through the heap-tree node
/// hash ([`hash_fact`], the `heap_node` the real tree folds with), then check it matches.
/// `true` iff `value` is exactly the value at `key` under `root`. A light client runs
/// this against just the card bytes.
pub fn verify_inclusion(root: &DataRoot, key: &str, value: &[u8], proof: &InclusionProof) -> bool {
    if proof.siblings.len() != proof.directions.len() {
        return false;
    }
    let mut acc = var_leaf(key, value).digest();
    for (sib, &dir) in proof.siblings.iter().zip(proof.directions.iter()) {
        // `heap_node(l, r) = hash_fact(l, &[r])`; dir 0 ⇒ acc is LEFT, dir 1 ⇒ RIGHT —
        // the exact fold `CanonicalHeapTree::update_witness` recomposes with.
        acc = if dir == 0 {
            hash_fact(acc, &[*sib])
        } else {
            hash_fact(*sib, &[acc])
        };
    }
    DataRoot::from_root_bytes(felt_to_bytes32(acc)) == *root
}

/// A content commitment to a umem heap state (`data_root`). Deterministic in the
/// heap contents, order-free. The raw 32 bytes behind it are the cell's real
/// heap-root felt (the `heap_root` the canonical state commitment absorbs).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DataRoot(pub String);

impl DataRoot {
    /// Reconstruct the wire `data_root` from the raw 32-byte heap root — the inverse of
    /// the encoding [`Umem::commit`] applies. The value the ledger stores for a cell's
    /// heap is the `dregg_cell` heap-root felt encoded to 32 bytes (the `heap_root`
    /// register the canonical state commitment absorbs); a visitor that obtains those
    /// bytes rebuilds the `DataRoot` this way to run [`verify_inclusion`] / check an
    /// owner attestation against that heap-root. `DataRoot::from_root_bytes(u.commit_root_bytes())
    /// == u.commit()` (the wire form and the raw form are the same commitment).
    pub fn from_root_bytes(root: [u8; 32]) -> Self {
        DataRoot(root_string(&root))
    }
}

/// The grain's read-write `/var`, realized as a dregg cell's umem heap.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Umem {
    entries: BTreeMap<String, Vec<u8>>,
}

impl Umem {
    pub fn new() -> Self {
        Umem::default()
    }

    pub fn get(&self, key: &str) -> Option<&[u8]> {
        self.entries.get(key).map(|v| v.as_slice())
    }

    pub fn put(&mut self, key: impl Into<String>, value: impl Into<Vec<u8>>) {
        self.entries.insert(key.into(), value.into());
    }

    pub fn remove(&mut self, key: &str) -> bool {
        self.entries.remove(key).is_some()
    }

    /// Drop every entry — used when a workload returns a fresh `/var` image.
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Iterate the heap entries (`key -> bytes`) in sorted key order.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &[u8])> {
        self.entries.iter().map(|(k, v)| (k.as_str(), v.as_slice()))
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Total stored bytes — the storage meter's input (per-MB billing).
    pub fn stored_bytes(&self) -> usize {
        self.entries.values().map(|v| v.len()).sum()
    }

    /// The [`HeapLeaf`] set committing this `/var`, in the real
    /// [`dregg_circuit::heap_root`] scheme — the leaves both [`commit_root_bytes`](Self::commit_root_bytes)
    /// and [`prove`](Self::prove) fold the `CanonicalHeapTree` over.
    pub fn heap_leaves(&self) -> Vec<HeapLeaf> {
        self.entries.iter().map(|(k, v)| var_leaf(k, v)).collect()
    }

    /// Commit to the current heap state — the `data_root` a checkpoint records.
    /// Content-addressed as the openable sorted-Poseidon2 heap root over the `/var`
    /// leaves (the SAME [`dregg_circuit::heap_root`] scheme the kernel commits a cell's
    /// heap with), so two heaps with the same contents commit to the same root
    /// regardless of insert order — AND a single entry's inclusion is provable under
    /// this root via [`prove`](Self::prove) without disclosing the rest of the heap.
    pub fn commit(&self) -> DataRoot {
        DataRoot(root_string(&self.commit_root_bytes()))
    }

    /// The **raw 32-byte `/var` heap root** — the 1-felt sorted-Poseidon2 root
    /// [`dregg_circuit::heap_root::compute_heap_root`] over the grain's leaves,
    /// encoded lane-0 via [`felt_to_bytes32`]. This is the grain's OWN `/var`
    /// commitment (the root its inclusion proofs open against), the value
    /// [`crate::grain::grain_cell_commitment`] publishes, so "the grain's committed
    /// `/var` root" == "the root the served card is a leaf under".
    ///
    /// NOTE: this is the 1-felt LANE-0 root; the cell's off-chain `heap_root`
    /// register has since widened to the faithful 8-felt `node8` root
    /// (`dregg_cell::state::compute_heap_root`), so the two schemes no longer
    /// coincide — see `commit_is_the_real_dregg_heap_root_scheme` for the residual.
    /// [`commit`](Self::commit) wraps this in the `heap1…` wire form, so the two are
    /// the same commitment ([`DataRoot::from_root_bytes`]).
    pub fn commit_root_bytes(&self) -> [u8; 32] {
        felt_to_bytes32(heap_compute_root(self.heap_leaves()))
    }

    /// **Prove one key's value is included under [`commit`](Self::commit)'s root** — the
    /// [`CanonicalHeapTree`] sibling path from that leaf to the root, so a visitor can
    /// verify the served value is the value at `key` under a trusted root with only
    /// `{key, value, proof, root}` (see [`verify_inclusion`]) — never the whole heap.
    /// `None` if `key` is absent.
    ///
    /// This is what makes the serve path witnessable for a *real, stateful* `/var`: a
    /// light client re-hashing just the served card, with this proof, reproduces the
    /// whole-heap root — it does not need (and never sees) the grain's other keys.
    pub fn prove(&self, key: &str) -> Option<InclusionProof> {
        if !self.entries.contains_key(key) {
            return None;
        }
        let tree = CanonicalHeapTree::new(self.heap_leaves(), HEAP_TREE_DEPTH);
        let pos = tree.position_of(var_addr(key))?;
        let (siblings, directions) = tree.prove_membership(pos)?;
        Some(InclusionProof {
            siblings,
            directions,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn commit_is_order_free_and_content_addressed() {
        let mut a = Umem::new();
        a.put("notes/1", b"hello".to_vec());
        a.put("notes/2", b"world".to_vec());

        let mut b = Umem::new();
        // Insert in the opposite order.
        b.put("notes/2", b"world".to_vec());
        b.put("notes/1", b"hello".to_vec());

        assert_eq!(a.commit(), b.commit());

        // A different value → a different root.
        b.put("notes/2", b"WORLD".to_vec());
        assert_ne!(a.commit(), b.commit());
    }

    #[test]
    fn empty_commit_is_stable() {
        assert_eq!(Umem::new().commit(), Umem::new().commit());
        assert!(Umem::new().commit().0.starts_with("heap1"));
    }

    /// **THE SCHEME IS THE REAL POSEIDON2 ONE (not a bespoke sha256 tree).** The
    /// `/var` root commits through `dregg_circuit::heap_root::compute_heap_root`
    /// (the 1-felt sorted-Poseidon2 tree), encoded lane-0 via [`felt_to_bytes32`].
    ///
    /// NOTE (off-chain lane-0 residual): this grain `/var` root is the 1-felt
    /// LANE-0 projection — the SAME ~31-bit off-chain forge class the cell's
    /// `heap_root` / `fields_root` / `cap_root` closed by widening to the faithful
    /// 8-felt `node8` root (`dregg_cell::state::compute_heap_root` et al., now
    /// `digest8_to_bytes32(compute_canonical_heap_root_8(..))`). The grain's `/var`
    /// commitment + its inclusion proofs (`prove` / `verify_inclusion`) still ride
    /// the 1-felt scheme, so it no longer equals `dregg_cell::empty_heap_root()`
    /// (which is now the node8 wide root). Widening the grain `/var` root to the
    /// node8 8-felt scheme (with 8-felt inclusion paths) is a SEPARATE lane.
    #[test]
    fn commit_is_the_real_dregg_heap_root_scheme() {
        // Empty heap → exactly the 1-felt circuit empty heap-root, lane-0 encoded
        // (the grain's own scheme — NOT the cell's now-wide `empty_heap_root`).
        assert_eq!(
            Umem::new().commit_root_bytes(),
            felt_to_bytes32(dregg_circuit::heap_root::empty_heap_root()),
            "empty /var root == the 1-felt circuit empty heap-root (grain lane-0 scheme)"
        );

        // Non-empty heap → the dregg_circuit heap-root primitive (the exact function
        // `dregg_cell::compute_heap_root` wraps) over the grain's leaves, encoded as the
        // real heap-root felt — NOT a sha256 Merkle root.
        let mut u = Umem::new();
        u.put("card/", b"<!doctype html>hello".to_vec());
        u.put("notes/a", b"alpha".to_vec());
        let expect = felt_to_bytes32(dregg_circuit::heap_root::compute_heap_root(u.heap_leaves()));
        assert_eq!(
            u.commit_root_bytes(),
            expect,
            "grain_cell_commitment IS the dregg heap-root over the /var leaves"
        );
    }

    /// The inclusion proof works for a **non-degenerate** heap: put several keys, prove one,
    /// and verify it against the WHOLE-heap root with only `{key, value, proof, root}` — the
    /// rest of `/var` is neither needed nor disclosed.
    #[test]
    fn inclusion_proof_verifies_against_the_whole_heap_root() {
        let mut u = Umem::new();
        for i in 0..7 {
            u.put(format!("k{i}"), format!("value-{i}").into_bytes());
        }
        let root = u.commit();
        // Prove the middle key against the full root.
        let key = "k3";
        let value = u.get(key).unwrap().to_vec();
        let proof = u.prove(key).expect("key present → a proof");
        assert!(
            verify_inclusion(&root, key, &value, &proof),
            "the card verifies as the leaf at k3 under the whole-heap root"
        );
        // Also holds for the first and last keys (proof-path edge cases).
        for key in ["k0", "k6"] {
            let value = u.get(key).unwrap().to_vec();
            let proof = u.prove(key).unwrap();
            assert!(verify_inclusion(&root, key, &value, &proof));
        }
    }

    /// The proof binds the exact `(key, value)` under the exact root: a wrong value, a wrong
    /// key, or a stale root all fail. This is the tooth a tampering host cannot beat without
    /// finding a Poseidon2 collision.
    #[test]
    fn inclusion_proof_rejects_wrong_value_key_or_root() {
        let mut u = Umem::new();
        u.put("a", b"one".to_vec());
        u.put("b", b"two".to_vec());
        u.put("c", b"three".to_vec());
        let root = u.commit();
        let proof = u.prove("b").unwrap();
        assert!(verify_inclusion(&root, "b", b"two", &proof));
        // Wrong value at the proven key.
        assert!(!verify_inclusion(&root, "b", b"TWO", &proof));
        // Right value+proof but claimed under the wrong key.
        assert!(!verify_inclusion(&root, "a", b"two", &proof));
        // Right leaf+proof but against a different (stale) root.
        let mut u2 = u.clone();
        u2.put("b", b"two!".to_vec());
        let stale = u2.commit();
        assert!(!verify_inclusion(&stale, "b", b"two", &proof));
        // An absent key has no proof.
        assert!(u.prove("zzz").is_none());
    }

    /// A single-entry heap: the sorted tree still opens the leaf against the whole-heap
    /// root (the path is the full-depth sentinel/empty-subtree path — the degenerate
    /// case is handled by the same sorted-Merkle machinery, not special-cased away).
    #[test]
    fn inclusion_proof_for_a_single_entry_heap() {
        let mut u = Umem::new();
        u.put("only", b"solo".to_vec());
        let root = u.commit();
        let proof = u.prove("only").unwrap();
        // The real sorted-tree opening is a full depth-16 path (sentinels + padding),
        // not an empty step list.
        assert_eq!(proof.siblings.len(), HEAP_TREE_DEPTH);
        assert_eq!(proof.directions.len(), HEAP_TREE_DEPTH);
        assert!(verify_inclusion(&root, "only", b"solo", &proof));
        // A tampered value still fails under the single-entry root.
        assert!(!verify_inclusion(&root, "only", b"SOLO", &proof));
    }
}
