//! The grain's private data = a dregg cell's **umem heap**.
//!
//! In Sandstorm a grain's `/var` is a read-write bind-mount, private to that grain,
//! that the app stores its database/state in. On dregg that `/var` *is* the cell's
//! umem heap: a keyed byte store that commits to a content-addressed **`data_root`**.
//! The difference Sandstorm cannot offer: the root is a commitment, so a checkpoint
//! is re-witnessable (a backup that proves what it contains), and the transitions —
//! not just a snapshot — are what get committed.
//!
//! ## The commitment is the REAL dregg heap-root scheme, at EIGHT LANES
//!
//! This module commits a grain's `/var` through the **same** openable sorted-Poseidon2
//! binary Merkle tree the kernel commits a cell's heap with — the faithful 8-felt one:
//! [`dregg_circuit::heap_root::CanonicalHeapTree8`] / [`compute_canonical_heap_root_8`],
//! every node a [`heap_node8`](dregg_circuit::heap_root::heap_node8) and every leaf a
//! [`HeapLeaf::digest8`], the same primitive `dregg_cell::state::compute_heap_root`
//! commits a cell's heap register with.
//!
//! ### Why ONE entry becomes EIGHT leaves
//!
//! A [`HeapLeaf`] is the arity-3 IMT node `(addr, value, next_addr)` — three felts. Its
//! `digest8` is eight lanes wide, but that width is the *node* fold's; the leaf's own
//! `value` field is **one** felt, and a `/var` value is arbitrary-length bytes. So a
//! one-leaf-per-entry `/var` binds its value at `log2 p = 30.906891` bits no matter how
//! wide the tree above it is: a served card can be swapped for a colliding one found in
//! `2^15.4534` evaluations. That was the state of this module until 2026-08-03, and
//! `tests/var_leaf_wide_old_admits_new_rejects.rs` exhibits the collision.
//!
//! The repair is the one the sink shape allows: **spread the wide digest across eight
//! leaves**, one per lane — byte-for-byte the shape `storage::bucket_commitment::
//! fold_leaves` already uses, and the shape its own `(B)` note prescribes for exactly
//! this case ("if a future opening ever serves a MERKLE PATH through this heap instead
//! of the full leaf list … migrate it to `hash_bytes_8` spread over eight
//! `(coll_lane_i, …)` entries at that moment"). This module IS the site that serves a
//! Merkle path.
//!
//! So one `/var` entry `(key, value)` becomes eight [`HeapLeaf`]s:
//!
//! * `addr_i = heap_addr(var_coll(key), i)` — the lane's sort key, `i ∈ 0..8`;
//! * `value_i = var_leaf_digest8(key, value)[i]` — lane `i` of the ONE 8-felt Poseidon2
//!   image over the length-prefixed `DOMAIN ‖ len(key) ‖ key ‖ value`.
//!
//! **The key is bound inside the leaf VALUES, not by the address.** That is what makes
//! the one-felt `var_coll` non-load-bearing: an attacker who collides two `/var` keys on
//! `var_coll` gets eight identical *addresses* and still cannot open one key's card at
//! the other, because `var_leaf_digest8` absorbs the key and must match in all eight
//! lanes. `var_coll` decides only WHERE a leaf sits; the eight lane values decide WHAT
//! it says.
//!
//! ### The bound, derived
//!
//! `p = 2013265921`, `log2 p = 30.906891`. Eight lanes carry `8 · 30.906891 = 247.2551`
//! bits, so forging a `/var` opening — the attacker chooses BOTH the honest card and the
//! swap, i.e. a **collision** — costs `2^123.6276`. (Against a card someone else already
//! committed it is a second preimage, `2^247.2551`; that is the flattering number of the
//! pair and it is NOT the governing one here, because a hostile *host* chooses both
//! sides.) The retired one-felt leaf was `2^15.4534` / `2^30.9069`.
//!
//! ⚠ **The residual this does NOT close, with its price.** `var_coll` is one felt, so two
//! `/var` keys in the SAME heap can share all eight lane addresses at `2^15.4534`. That is
//! not a forgery (see above) — [`dregg_circuit::heap_root::assert_addr_unique`] PANICS on
//! it, refusing to commit an ambiguous root, which is fail-closed. It is an AVAILABILITY
//! bound, and the eight-fold leaf count moves it: an accidental collision becomes likely
//! near `2^15.4534 / 8 ≈ 5,793` entries rather than `≈ 46,341`, and the depth-16 tree's
//! capacity is now `8191` entries rather than `65535`. Closing it needs an address space
//! wider than one felt, which is `HeapLeaf`'s shape and therefore the deployed IMT gate's
//! — the same Lean/emit item named at `exec_lean::nullifier::addr_of`.
//!
//! ## Opening one key without the rest of the heap
//!
//! [`Umem::prove`] emits an [`InclusionProof`]: eight [`LaneOpening`]s, one per lane, each
//! an 8-felt sibling path. The host-state-free [`verify_inclusion`] recomputes all eight
//! leaves from `{key, value}` alone, folds each path through `heap_node8`, and requires
//! **all eight to recompose to the same root** and that root to equal the trusted one. A
//! visitor re-hashes just the served card and confirms it is the value at `key` under a
//! heap-root it obtains independently.

use std::collections::BTreeMap;

use dregg_cell::commitment::digest8_to_bytes32;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{
    compute_canonical_heap_root_8, heap_addr, recompose_membership_8, CanonicalHeapTree8, HeapLeaf,
    HEAP_DIGEST_W, HEAP_TREE_DEPTH,
};
use dregg_circuit::poseidon2::{hash_bytes, hash_bytes_8};

use crate::spk::base32;

/// Domain tag for the `/var` heap ADDRESS COLLECTION felt — keeps a key-derived
/// collection from ever aliasing a leaf-digest felt, and separates a grain `/var`
/// address from any other Poseidon2 image. `:v2` because the whole `/var` commitment
/// changed shape on 2026-08-03; a `:v1` root can never be reproduced by this code.
const VAR_COLL_DOMAIN: &[u8] = b"grain/var/coll:v2\0";

/// Domain tag for the `/var` LEAF digest — the ONE image that binds key AND value.
const VAR_LEAF_DOMAIN: &[u8] = b"grain/var/leaf:v2\0";

/// The number of heap leaves ONE `/var` entry occupies: one per lane of the 8-felt
/// leaf digest. See the module doc for why the spread is what the sink shape allows.
pub const VAR_LANES: usize = HEAP_DIGEST_W;

/// The `/var` COLLECTION felt of a string key — the address base the entry's eight lane
/// leaves hang off, the string-keyed analog of the `collection_id` in
/// [`dregg_circuit::heap_root::heap_addr`]'s `(collection_id, key)` pair.
///
/// ⓘ **One felt, and that is sound here** — deliberately, and for a reason that is written
/// down rather than assumed. This felt decides only WHERE a leaf sits in the sorted tree.
/// The key is bound a second time, at full width, INSIDE the leaf values by
/// [`var_leaf_digest8`], and [`verify_inclusion`] recomputes those from the claimed key —
/// so two keys colliding here cannot open each other's cards. The residual is availability
/// only (`assert_addr_unique` panics, fail-closed) and it is priced in the module doc.
///
/// ⚠ The condition that would flip this to a wound: if `verify_inclusion` ever stopped
/// absorbing the key into the leaf digest and relied on the address to identify the entry,
/// this felt would become the whole key binding at `2^15.4534`. It does not; do not make it.
pub fn var_coll(key: &str) -> BabyBear {
    let mut buf = Vec::with_capacity(VAR_COLL_DOMAIN.len() + key.len());
    buf.extend_from_slice(VAR_COLL_DOMAIN);
    buf.extend_from_slice(key.as_bytes());
    hash_bytes(&buf)
}

/// The eight heap ADDRESSES of a `/var` key's lane leaves: `heap_addr(var_coll(key), i)`.
pub fn var_lane_addrs(key: &str) -> [BabyBear; VAR_LANES] {
    let coll = var_coll(key);
    core::array::from_fn(|i| heap_addr(coll, BabyBear::new(i as u32)))
}

/// **The wide `/var` leaf digest** — the single 8-felt Poseidon2 image binding the key AND
/// the value bytes as ONE preimage, `VAR_LEAF_DOMAIN ‖ len(key) ‖ key ‖ value`.
///
/// The 8-byte little-endian key length is what makes the concatenation parse uniquely: it
/// is the only thing separating `("ab", b"c")` from `("a", b"bc")`, and without it the
/// split point would be attacker-chosen at zero cost — a real collision needing no search
/// at all, which is a strictly worse failure than the birthday one this function exists to
/// fix. `hash_bytes_8`'s own preimage (`BabyBear::bytes_to_lanes`) is length-prefixed and
/// injective on byte strings, so the composite preimage is injective on `(key, value)`.
///
/// The eight lanes are `2^123.6276` collision-resistant over `p^8` (`8 · log2 p = 247.2551`
/// bits); see the module doc for the derivation and for why COLLISION, not second preimage,
/// is the governing figure at this site.
pub fn var_leaf_digest8(key: &str, value: &[u8]) -> [BabyBear; VAR_LANES] {
    let mut buf = Vec::with_capacity(VAR_LEAF_DOMAIN.len() + 8 + key.len() + value.len());
    buf.extend_from_slice(VAR_LEAF_DOMAIN);
    buf.extend_from_slice(&(key.len() as u64).to_le_bytes());
    buf.extend_from_slice(key.as_bytes());
    buf.extend_from_slice(value);
    hash_bytes_8(&buf)
}

/// The eight [`HeapLeaf`]s one `/var` entry contributes — the leaves both
/// [`Umem::commit_root_bytes`] and [`Umem::prove`] build the [`CanonicalHeapTree8`] over.
/// Lane `i` is `(addr = heap_addr(var_coll(key), i), value = var_leaf_digest8(key, value)[i])`.
fn var_leaves(key: &str, value: &[u8]) -> [HeapLeaf; VAR_LANES] {
    let addrs = var_lane_addrs(key);
    let d8 = var_leaf_digest8(key, value);
    core::array::from_fn(|i| HeapLeaf::entry(addrs[i], d8[i]))
}

/// One lane's opening: the committed IMT pointer of that lane's leaf plus its 8-felt
/// sibling path to the root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaneOpening {
    /// The committed IMT POINTER of the opened leaf: the address of the next-larger
    /// present leaf, or `heap_root::SENTINEL_MAX` for the largest one.
    ///
    /// The heap leaf is the arity-3 `hash[addr, value, next_addr]` — the heap tree
    /// retired its stored MAX sentinel LEAF in favour of this pointer (2026-07-12,
    /// `919b2b0b8d`), so the pointer is INSIDE the committed digest and a verifier
    /// that assumes the unlinked `SENTINEL_MAX` can only ever check the
    /// largest-addressed leaf. Not a disclosure the path did not already make: the
    /// sibling digests are served anyway, and the pointer is one Poseidon2 image of
    /// another lane's address, never anyone's value.
    pub next_addr: BabyBear,
    /// Sibling 8-felt digests along the path from the leaf to the root (bottom-up).
    pub siblings: Vec<[BabyBear; HEAP_DIGEST_W]>,
    /// Direction bits: `directions[i] == 0` when the running node is the LEFT child at
    /// level `i` (sibling on the right), `1` otherwise. Same convention as
    /// [`CanonicalHeapTree8::prove_membership`].
    pub directions: Vec<u8>,
}

/// A Merkle inclusion proof that a single key's value is committed under a heap-root —
/// the eight [`LaneOpening`]s of the entry's eight lane leaves, each an 8-felt
/// [`CanonicalHeapTree8`] sibling path (a Poseidon2/`heap_node8` path, NOT a sha256 tree).
/// Log-sized in the tree depth, and verified with [`verify_inclusion`] against
/// `{key, value, root}` alone; no heap needed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InclusionProof {
    /// Lane `i`'s opening. All eight must recompose to the SAME root, and that root must
    /// be the trusted one — [`verify_inclusion`] enforces both.
    pub lanes: [LaneOpening; VAR_LANES],
}

/// **Verify a single-leaf inclusion proof — host-state-free.** Given only the served
/// `{key, value}`, the `proof`, and a `root` the caller trusts (obtained independently —
/// e.g. the cell's heap-root from the ledger, NOT from the serving host), recompute all
/// eight committed lane leaves `hash[addr_i, digest8_i, next_addr_i]`
/// ([`HeapLeaf::digest8`], the ONE place that schema is written), fold each sibling path
/// through [`recompose_membership_8`], and require every lane to land on the same root as
/// the trusted one. `true` iff `value` is exactly the value at `key` under `root`. A light
/// client runs this against just the card bytes.
///
/// Fails closed on a mismatched path length, on a pointer no committed leaf could carry
/// (`addr >= next_addr` — the `ImtSorted` well-linked invariant the tree builder itself
/// refuses to violate), and on ANY lane disagreeing with the others.
pub fn verify_inclusion(root: &DataRoot, key: &str, value: &[u8], proof: &InclusionProof) -> bool {
    let addrs = var_lane_addrs(key);
    let d8 = var_leaf_digest8(key, value);
    let mut folded: Option<[BabyBear; HEAP_DIGEST_W]> = None;
    for (lane, opening) in proof.lanes.iter().enumerate() {
        if opening.siblings.len() != opening.directions.len() {
            return false;
        }
        // The COMMITTED leaf: the address and value are recomputed from `{key, value}`;
        // only the tree-managed pointer is taken from the proof — never assumed.
        let mut leaf = HeapLeaf::entry(addrs[lane], d8[lane]);
        leaf.next_addr = opening.next_addr;
        if leaf.addr.as_u32() >= leaf.next_addr.as_u32() {
            return false;
        }
        let r = recompose_membership_8(leaf.digest8(), &opening.siblings, &opening.directions);
        match folded {
            None => folded = Some(r),
            Some(prev) if prev != r => return false,
            Some(_) => {}
        }
    }
    match folded {
        Some(r) => DataRoot::from_root_bytes(digest8_to_bytes32(r)) == *root,
        // An empty lane array cannot occur (`[LaneOpening; VAR_LANES]`), but fail closed
        // rather than accept on a vacuous fold.
        None => false,
    }
}

/// A content commitment to a umem heap state (`data_root`). Deterministic in the
/// heap contents, order-free. The raw 32 bytes behind it are the cell's real
/// 8-felt heap-root (the `heap_root` the canonical state commitment absorbs),
/// encoded lane-for-lane by [`digest8_to_bytes32`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DataRoot(pub String);

impl DataRoot {
    /// Reconstruct the wire `data_root` from the raw 32-byte heap root — the inverse of
    /// the encoding [`Umem::commit`] applies. The value the ledger stores for a cell's
    /// heap is the 8-felt heap root encoded to 32 bytes (the `heap_root` register the
    /// canonical state commitment absorbs); a visitor that obtains those bytes rebuilds
    /// the `DataRoot` this way to run [`verify_inclusion`] / check an owner attestation
    /// against that heap-root.
    /// `DataRoot::from_root_bytes(u.commit_root_bytes()) == u.commit()` (the wire form and
    /// the raw form are the same commitment).
    pub fn from_root_bytes(root: [u8; 32]) -> Self {
        DataRoot(root_string(&root))
    }
}

/// Encode a 32-byte heap root as the `heap8…` [`DataRoot`] wire string. The prefix moved
/// from `heap1…` on 2026-08-03: the bytes behind it are now the full 8-felt root, and an
/// old `heap1…` string must never compare equal to a new one for the same `/var`.
fn root_string(root: &[u8; 32]) -> String {
    format!("heap8{}", base32(root))
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

    /// The [`HeapLeaf`] set committing this `/var` — EIGHT per entry, one per lane of the
    /// wide leaf digest (see the module doc). The leaves both
    /// [`commit_root_bytes`](Self::commit_root_bytes) and [`prove`](Self::prove) fold the
    /// [`CanonicalHeapTree8`] over.
    pub fn heap_leaves(&self) -> Vec<HeapLeaf> {
        self.entries
            .iter()
            .flat_map(|(k, v)| var_leaves(k, v))
            .collect()
    }

    /// Commit to the current heap state — the `data_root` a checkpoint records.
    /// Content-addressed as the openable sorted-Poseidon2 8-felt heap root over the `/var`
    /// leaves (the SAME [`dregg_circuit::heap_root`] scheme the kernel commits a cell's
    /// heap with), so two heaps with the same contents commit to the same root
    /// regardless of insert order — AND a single entry's inclusion is provable under
    /// this root via [`prove`](Self::prove) without disclosing the rest of the heap.
    pub fn commit(&self) -> DataRoot {
        DataRoot(root_string(&self.commit_root_bytes()))
    }

    /// The **raw 32-byte `/var` heap root** — the faithful 8-felt sorted-Poseidon2 root
    /// [`compute_canonical_heap_root_8`] over the grain's lane leaves, encoded by
    /// [`digest8_to_bytes32`] (lane `i` in bytes `[4i..4i+4]`, little-endian; injective on
    /// the full 8-felt digest). This is the grain's OWN `/var` commitment (the root its
    /// inclusion proofs open against), the value [`crate::grain::grain_cell_commitment`]
    /// publishes, so "the grain's committed `/var` root" == "the root the served card is a
    /// leaf under". [`commit`](Self::commit) wraps this in the `heap8…` wire form, so the
    /// two are the same commitment ([`DataRoot::from_root_bytes`]).
    ///
    /// This is the SAME node8 scheme the cell's `heap_root` register carries
    /// (`dregg_cell::state::compute_heap_root`); the 1-felt lane-0 projection this used to
    /// be is gone, and with it the residual `commit_is_the_real_dregg_heap_root_scheme`
    /// used to record.
    pub fn commit_root_bytes(&self) -> [u8; 32] {
        digest8_to_bytes32(compute_canonical_heap_root_8(self.heap_leaves()).limbs())
    }

    /// **Prove one key's value is included under [`commit`](Self::commit)'s root** — the
    /// eight [`CanonicalHeapTree8`] sibling paths from that entry's lane leaves to the
    /// root, so a visitor can verify the served value is the value at `key` under a trusted
    /// root with only `{key, value, proof, root}` (see [`verify_inclusion`]) — never the
    /// whole heap. `None` if `key` is absent.
    ///
    /// This is what makes the serve path witnessable for a *real, stateful* `/var`: a
    /// light client re-hashing just the served card, with this proof, reproduces the
    /// whole-heap root — it does not need (and never sees) the grain's other keys.
    pub fn prove(&self, key: &str) -> Option<InclusionProof> {
        if !self.entries.contains_key(key) {
            return None;
        }
        let tree = CanonicalHeapTree8::new(self.heap_leaves(), HEAP_TREE_DEPTH);
        let mut lanes = Vec::with_capacity(VAR_LANES);
        for addr in var_lane_addrs(key) {
            let pos = tree.position_of(addr)?;
            let (siblings, directions) = tree.prove_membership(pos)?;
            lanes.push(LaneOpening {
                // The COMMITTED pointer the tree builder linked, not the unlinked
                // `HeapLeaf::entry` seed — the leaf digest absorbs it.
                next_addr: tree.sorted_leaves()[pos].next_addr,
                siblings,
                directions,
            });
        }
        let lanes: [LaneOpening; VAR_LANES] = lanes.try_into().ok()?;
        Some(InclusionProof { lanes })
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
        assert!(Umem::new().commit().0.starts_with("heap8"));
    }

    /// **THE SCHEME IS THE REAL 8-FELT POSEIDON2 ONE** (not a bespoke sha256 tree, and no
    /// longer the 1-felt lane-0 projection). The `/var` root commits through
    /// `dregg_circuit::heap_root::compute_canonical_heap_root_8` — the same node8 primitive
    /// `dregg_cell::state::compute_heap_root` commits a cell's heap register with — encoded
    /// by `digest8_to_bytes32`.
    #[test]
    fn commit_is_the_real_dregg_heap_root_scheme() {
        // Empty heap → exactly the 8-felt circuit empty heap-root.
        assert_eq!(
            Umem::new().commit_root_bytes(),
            digest8_to_bytes32(dregg_circuit::heap_root::empty_heap_root_8().limbs()),
            "empty /var root == the 8-felt circuit empty heap-root"
        );

        // Non-empty heap → the dregg_circuit 8-felt heap-root primitive over the grain's
        // lane leaves — NOT a sha256 Merkle root, and NOT the lane-0 projection.
        let mut u = Umem::new();
        u.put("card/", b"<!doctype html>hello".to_vec());
        u.put("notes/a", b"alpha".to_vec());
        let expect = digest8_to_bytes32(compute_canonical_heap_root_8(u.heap_leaves()).limbs());
        assert_eq!(
            u.commit_root_bytes(),
            expect,
            "grain_cell_commitment IS the 8-felt dregg heap-root over the /var lane leaves"
        );

        // ANTI-VACUITY: the completion lanes are genuinely non-zero, i.e. the eight bytes
        // beyond lane 0 are not a zero-fill dressed up as width.
        let root = compute_canonical_heap_root_8(u.heap_leaves()).limbs();
        assert!(
            root[1..8].iter().any(|f| *f != BabyBear::ZERO),
            "a non-empty /var root must fill the completion lanes"
        );
    }

    /// Each `/var` entry occupies exactly [`VAR_LANES`] leaves, and the leaves of distinct
    /// entries are distinct — the structural fact the spread rests on.
    #[test]
    fn one_entry_is_eight_lane_leaves() {
        let mut u = Umem::new();
        u.put("a", b"one".to_vec());
        assert_eq!(u.heap_leaves().len(), VAR_LANES);
        u.put("b", b"two".to_vec());
        assert_eq!(u.heap_leaves().len(), 2 * VAR_LANES);

        let mut addrs: Vec<u32> = u.heap_leaves().iter().map(|l| l.addr.as_u32()).collect();
        addrs.sort_unstable();
        let n = addrs.len();
        addrs.dedup();
        assert_eq!(addrs.len(), n, "the lane addresses must be distinct");
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
    /// finding a Poseidon2 collision — now an eight-lane one at `2^123.63`.
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

        // ── THE IMT POINTER BINDS (the 2026-07-12 leaf-schema retirement's tooth) ──
        // The leaf digest is arity-3 `hash[addr, value, next_addr]`. Find a LANE whose
        // committed pointer is a REAL successor (not the terminal SENTINEL_MAX) and check
        // that swapping the pointer for the unlinked `HeapLeaf::entry` seed — exactly what
        // a pre-IMT verifier assumed — is REFUSED.
        let max = dregg_circuit::heap_root::SENTINEL_MAX;
        let mut forged = u.prove("b").unwrap();
        let interior = forged
            .lanes
            .iter()
            .position(|l| l.next_addr != max)
            .expect("with 24 lane leaves at least one lane is interior");
        assert!(verify_inclusion(&root, "b", b"two", &forged));
        forged.lanes[interior].next_addr = max;
        assert!(
            !verify_inclusion(&root, "b", b"two", &forged),
            "an UNLINKED (SENTINEL_MAX) leaf must not open at an interior lane — the \
             committed pointer is part of the digest"
        );

        // ── EVERY LANE IS LOAD-BEARING ── corrupting any single lane's path must refuse,
        // so no lane is decorative width.
        for lane in 0..VAR_LANES {
            let mut tampered = u.prove("b").unwrap();
            tampered.lanes[lane].siblings[0][0] =
                tampered.lanes[lane].siblings[0][0] + BabyBear::ONE;
            assert!(
                !verify_inclusion(&root, "b", b"two", &tampered),
                "lane {lane} is not load-bearing — its path can be corrupted undetected"
            );
        }
    }

    /// A single-entry heap: the sorted tree still opens all eight lane leaves against the
    /// whole-heap root (each path is the full-depth sentinel/empty-subtree path — the
    /// degenerate case is handled by the same sorted-Merkle machinery, not special-cased).
    #[test]
    fn inclusion_proof_for_a_single_entry_heap() {
        let mut u = Umem::new();
        u.put("only", b"solo".to_vec());
        let root = u.commit();
        let proof = u.prove("only").unwrap();
        for lane in &proof.lanes {
            // The real sorted-tree opening is a full depth-16 path (sentinels + padding),
            // not an empty step list.
            assert_eq!(lane.siblings.len(), HEAP_TREE_DEPTH);
            assert_eq!(lane.directions.len(), HEAP_TREE_DEPTH);
        }
        assert!(verify_inclusion(&root, "only", b"solo", &proof));
        // A tampered value still fails under the single-entry root.
        assert!(!verify_inclusion(&root, "only", b"SOLO", &proof));
    }

    /// **ANTI-VACUITY: the wide leaf digest DEPENDS ON EVERY INPUT.** A hash node's fix is
    /// only real if every byte of the preimage reaches every lane's determination — a
    /// widening that ignored the key, or the value, or the length prefix, would be eight
    /// lanes of nothing. Each perturbation must move at least one lane (in practice all
    /// eight); the length prefix is checked by the split-point pair it exists to separate.
    #[test]
    fn wide_leaf_digest_depends_on_every_input() {
        let base = var_leaf_digest8("cfg", b"hello");
        // The KEY reaches the digest.
        assert_ne!(base, var_leaf_digest8("cfh", b"hello"));
        // The VALUE reaches the digest.
        assert_ne!(base, var_leaf_digest8("cfg", b"hellp"));
        // The VALUE LENGTH reaches the digest (append and truncate both move it).
        assert_ne!(base, var_leaf_digest8("cfg", b"hello\0"));
        assert_ne!(base, var_leaf_digest8("cfg", b"hell"));
        // THE LENGTH PREFIX: the two splits of the same concatenation must differ.
        assert_ne!(
            var_leaf_digest8("ab", b"c"),
            var_leaf_digest8("a", b"bc"),
            "the key-length prefix must separate the two splits of `abc`"
        );
        // Every lane is live: no lane is a constant across distinct inputs.
        for lane in 0..VAR_LANES {
            let moved = (0u8..64).any(|n| var_leaf_digest8("cfg", &[n])[lane] != base[lane]);
            assert!(moved, "lane {lane} never moves — it is not a real lane");
        }
    }
}
