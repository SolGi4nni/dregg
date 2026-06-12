//! The canonical, **openable** heap commitment: a SORTED Poseidon2 binary
//! Merkle map over a cell's `(collection_id, key) → value` entries.
//!
//! ## Why this module exists (REFINEMENT-DESIGN Decision 1 / THE ROTATION)
//!
//! THE HEAP is the generalization of the proven capability root
//! ([`crate::cap_root`]) with a **generic leaf**: where the cap tree stores the
//! 7-field capability leaf keyed by `slot_hash`, the heap tree stores
//! `hash[addr, value]` keyed by `addr = hash[collection_id, key]`. Same sorted
//! discipline, same sentinels, same `hash_fact` nodes, same depth — reuse of
//! verified machinery, not invention.
//!
//! This module is the **single** heap-root scheme, computed byte-identically
//! wherever it runs:
//!
//!   * the executor computes the post-write root here and carries it on the
//!     wire (`FullActionA.heapWriteA`'s `newRoot` / `WireAction::HeapWrite`),
//!     pinned into the `heap_root` register;
//!   * the cell recomputes the same root over its heap entries and refuses a
//!     mismatch (the cap Phase-A discipline);
//!   * the circuit's heap-write descriptor gadget recomputes `addr` and the
//!     leaf **in-row** (`Dregg2/Circuit/Emit/EffectVmEmitHeapRoot.lean`:
//!     `siteHeapAddr` / `siteHeapLeaf` are arity-2 hash sites over exactly
//!     `[coll, key]` and `[addr, value]` — the same images [`heap_addr`] and
//!     [`HeapLeaf::digest`] compute here).
//!
//! The hash shapes are pinned by the Lean model (`Dregg2/Substrate/Heap.lean`
//! `addrOf` / `leafOf`): **arity-2, no domain tag** — the circuit hash sites
//! recompute these exact images, so adding a tag here would fork cell from
//! circuit. The differential test
//! `circuit/tests/heap_root_cell_circuit_differential.rs` pins the scheme
//! against an independently hand-built tree (the A2-gate shape).
//!
//! ## Phase A scope
//!
//! Phase A makes the `heap_root` VALUE this sorted-Merkle root. The per-write
//! root ADVANCE stays pinned-as-digest at the tree layer (the circuit pins the
//! executor's computed new root and recomputes the address + leaf in-row); the
//! genuine in-circuit sorted-tree update/insert gates (membership-open +
//! leaf-update + bracketed sorted-insert, mirroring the revocation circuit)
//! are the Phase-E lane.

use crate::field::BabyBear;
use crate::poseidon2::{hash_fact, hash_many};

pub use crate::dsl::revocation::{SENTINEL_MAX, SENTINEL_MIN};

/// Tree depth for the canonical heap tree. Matches
/// [`crate::cap_root::CAP_TREE_DEPTH`]: a binary tree of depth 16 holds
/// `2^16 - 2 = 65534` entries (two positions reserved for the MIN/MAX
/// sentinels). Per-cell heaps never re-rotate the tree in practice.
pub const HEAP_TREE_DEPTH: usize = 16;

/// The canonical heap ADDRESS of a `(collection_id, key)` pair: the arity-2
/// Poseidon2 image `hash[coll, key]` — the sorted-tree sort key. This is the
/// exact image the descriptor gadget's `siteHeapAddr` recomputes in-row
/// (`EffectVmEmitHeapRoot.addrOf`); NO domain tag, or cell and circuit fork.
pub fn heap_addr(coll: BabyBear, key: BabyBear) -> BabyBear {
    hash_many(&[coll, key])
}

/// One heap entry: the sorted-tree leaf `(addr, value)`. The leaf digest is
/// the arity-2 image `hash[addr, value]` (`EffectVmEmitHeapRoot.leafOf` /
/// `Substrate.Heap.leafOf`), recomputed in-row by `siteHeapLeaf`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HeapLeaf {
    /// The sort key: [`heap_addr`] of the entry's `(collection_id, key)`.
    pub addr: BabyBear,
    /// The stored value felt.
    pub value: BabyBear,
}

impl HeapLeaf {
    /// The arity-2 Poseidon2 leaf digest `hash[addr, value]`. This is the
    /// value the sorted Merkle tree stores at the leaf position; the leaf is
    /// *placed* by its `addr` ordering.
    pub fn digest(&self) -> BabyBear {
        hash_many(&[self.addr, self.value])
    }
}

/// The sentinel leaf for a given sort key (MIN or MAX). The value is zero;
/// the sentinel exists only to bracket the sorted key range so a
/// non-membership proof can place an absent address between two adjacent
/// present addresses (`Crypto.NonMembership.sorted_gap_excludes`, reused by
/// `Substrate.Heap.get_none_of_gap`).
fn sentinel_leaf(key: BabyBear) -> HeapLeaf {
    HeapLeaf {
        addr: key,
        value: BabyBear::ZERO,
    }
}

/// The canonical heap tree: a sorted binary Poseidon2 Merkle tree over the
/// heap entries, keyed by `addr` and sentinel-bracketed. Mirrors
/// [`crate::cap_root::CanonicalCapTree`] with the generic 2-field leaf.
#[derive(Clone, Debug)]
pub struct CanonicalHeapTree {
    /// All levels, bottom-up. `levels[0]` = leaf digests (padded);
    /// `levels[depth]` = `[root]`.
    levels: Vec<Vec<BabyBear>>,
    /// The leaves in sorted-by-`addr` order, including sentinels (before
    /// padding). Retained for membership / non-membership witnessing.
    sorted_leaves: Vec<HeapLeaf>,
    /// Tree depth.
    depth: usize,
}

impl CanonicalHeapTree {
    /// Build the canonical heap tree from a cell's heap entries.
    ///
    /// Sorts the leaves by `addr`, brackets with the MIN/MAX sentinels,
    /// deduplicates by key (the executor's `Heap.set` is insert-or-update, so
    /// duplicate addresses never occur; belt-and-suspenders), then builds the
    /// padded binary tree.
    pub fn new(mut leaves: Vec<HeapLeaf>, depth: usize) -> Self {
        leaves.push(sentinel_leaf(SENTINEL_MIN));
        leaves.push(sentinel_leaf(SENTINEL_MAX));
        // Sort by the canonical sort key (addr). Deterministic, total.
        leaves.sort_by_key(|l| l.addr.as_u32());
        leaves.dedup_by_key(|l| l.addr.as_u32());

        let capacity = 1usize << depth;
        // The heap must fit (minus the two sentinels). Fail loudly rather
        // than silently truncate.
        assert!(
            leaves.len() <= capacity,
            "heap ({} entries incl. sentinels) exceeds tree capacity 2^{depth}",
            leaves.len()
        );

        let mut leaf_digests: Vec<BabyBear> = leaves.iter().map(HeapLeaf::digest).collect();
        // Pad with the zero felt (the empty-position marker), exactly like
        // the cap + revocation trees.
        leaf_digests.resize(capacity, BabyBear::ZERO);

        let mut levels = vec![leaf_digests];
        for _ in 0..depth {
            let prev = levels.last().unwrap();
            let mut next_level = Vec::with_capacity(prev.len() / 2);
            for chunk in prev.chunks(2) {
                next_level.push(hash_fact(chunk[0], &[chunk[1]]));
            }
            levels.push(next_level);
        }

        Self {
            levels,
            sorted_leaves: leaves,
            depth,
        }
    }

    /// The Merkle root.
    pub fn root(&self) -> BabyBear {
        self.levels[self.depth][0]
    }

    /// The sorted leaves (including sentinels). For membership witnessing.
    pub fn sorted_leaves(&self) -> &[HeapLeaf] {
        &self.sorted_leaves
    }

    /// Number of real (non-sentinel) entries.
    pub fn num_entries(&self) -> usize {
        self.sorted_leaves
            .iter()
            .filter(|l| l.addr != SENTINEL_MIN && l.addr != SENTINEL_MAX)
            .count()
    }

    /// The tree depth.
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// All level vectors, bottom-up (`levels[0]` = padded leaf digests,
    /// `levels[depth] = [root]`). Exposed for membership witnessing.
    pub fn levels(&self) -> &[Vec<BabyBear>] {
        &self.levels
    }

    /// The leaf-array position (0-based, in the padded bottom level) of the
    /// leaf whose `addr == key`, or `None` if no such (non-padding) leaf
    /// exists.
    pub fn position_of(&self, key: BabyBear) -> Option<usize> {
        self.sorted_leaves.iter().position(|l| l.addr == key)
    }

    /// Generate a Merkle **membership** path for the leaf at the given padded
    /// position: `(siblings, directions)` where `directions[i] == 0` if the
    /// current node is the LEFT child at level `i` (sibling on the right),
    /// `1` otherwise. Mirrors [`crate::cap_root::CanonicalCapTree::prove_membership`].
    pub fn prove_membership(&self, position: usize) -> Option<(Vec<BabyBear>, Vec<u8>)> {
        let capacity = 1usize << self.depth;
        if position >= capacity {
            return None;
        }
        let mut siblings = Vec::with_capacity(self.depth);
        let mut directions = Vec::with_capacity(self.depth);
        let mut idx = position;
        for level in 0..self.depth {
            let sibling_idx = idx ^ 1;
            siblings.push(self.levels[level][sibling_idx]);
            directions.push((idx & 1) as u8);
            idx >>= 1;
        }
        Some((siblings, directions))
    }
}

/// A heap **update** witness for an in-place value write at an EXISTING
/// address: membership-open the OLD leaf against the old `heap_root` and
/// carry the NEW leaf so a Phase-E AIR can recompute `new_heap_root` over the
/// SAME sibling path — a genuine sorted-tree leaf-update, not a pinned
/// digest. (A fresh-address write is a sorted INSERT, which shifts positions;
/// its bracketed-insert witness rides the Phase-E lane with the
/// non-membership gates.)
///
/// Because the tree is sorted by `addr` and a value update holds the address
/// fixed, the old and new leaves occupy the SAME position and share the SAME
/// sibling path; the only difference is the leaf digest. Mirrors
/// [`crate::cap_root::CapAttenuationWitness`].
#[derive(Clone, Debug)]
pub struct HeapUpdateWitness {
    /// The OLD (pre-write) leaf — the committed value.
    pub old_leaf: HeapLeaf,
    /// The NEW (post-write) leaf — same `addr`, new value.
    pub new_leaf: HeapLeaf,
    /// Sibling digests along the path from the leaf to the root (bottom-up).
    pub siblings: Vec<BabyBear>,
    /// Direction bits along the path (0 = current is left child, 1 = right).
    pub directions: Vec<u8>,
    /// The authenticated old root (= the old leaf's path top).
    pub old_root: BabyBear,
    /// The recomputed new root (= the new leaf's path top, same siblings).
    pub new_root: BabyBear,
}

/// A heap **insert** witness for a FRESH address: the new leaf is spliced into
/// its unique sorted position in the leaf list and the tree is rebuilt. The
/// returned path is a membership opening of the NEW leaf against the NEW root;
/// freshness is proved separately (e.g. by a paired `MapKind::Absent` gap
/// opening against `old_root`).
#[derive(Clone, Debug)]
pub struct HeapInsertWitness {
    /// The inserted leaf.
    pub new_leaf: HeapLeaf,
    /// Sibling digests along the path from the new leaf to the new root.
    pub siblings: Vec<BabyBear>,
    /// Direction bits along the path (0 = new leaf is left child, 1 = right).
    pub directions: Vec<u8>,
    /// The authenticated pre-insert root.
    pub old_root: BabyBear,
    /// The recomputed post-insert root.
    pub new_root: BabyBear,
}

impl CanonicalHeapTree {
    /// Build a [`HeapUpdateWitness`] that rewrites the value at
    /// `new_leaf.addr` to `new_leaf.value`. Returns `None` if no leaf with
    /// that address is present (a fabricated old leaf has no authenticated
    /// position; fresh-address inserts use [`CanonicalHeapTree::insert_witness`]).
    /// The returned `old_root` equals this tree's root; `new_root` is the root
    /// after the single-leaf replacement (recomputed over the shared sibling path).
    pub fn update_witness(&self, new_leaf: HeapLeaf) -> Option<HeapUpdateWitness> {
        let pos = self.position_of(new_leaf.addr)?;
        let old_leaf = self.sorted_leaves[pos];
        let (siblings, directions) = self.prove_membership(pos)?;

        // Recompute the new root over the SAME siblings with the new leaf
        // digest swapped in at the leaf position.
        let mut cur = new_leaf.digest();
        for level in 0..self.depth {
            let sib = siblings[level];
            cur = if directions[level] == 0 {
                hash_fact(cur, &[sib])
            } else {
                hash_fact(sib, &[cur])
            };
        }
        Some(HeapUpdateWitness {
            old_leaf,
            new_leaf,
            siblings,
            directions,
            old_root: self.root(),
            new_root: cur,
        })
    }

    /// Build a sorted INSERT witness for a FRESH address: the new leaf is
    /// spliced into its unique sorted position, the tree is rebuilt, and a
    /// membership path for the new leaf against the NEW root is returned.
    /// Returns `None` if the address is already present (use `update_witness`)
    /// or collides with the sentinels.
    pub fn insert_witness(&self, new_leaf: HeapLeaf) -> Option<HeapInsertWitness> {
        let key = new_leaf.addr;
        if key == SENTINEL_MIN || key.as_u32() >= SENTINEL_MAX.as_u32() {
            return None;
        }
        if self.position_of(key).is_some() {
            return None;
        }
        // Insertion position in the sentinel-bracketed sorted leaf list.
        let pos = self.sorted_leaves.iter().position(|l| l.addr > key)?;
        let new_real: Vec<HeapLeaf> = self.sorted_leaves[..pos]
            .iter()
            .chain(std::iter::once(&new_leaf))
            .chain(&self.sorted_leaves[pos..])
            .filter(|l| l.addr != SENTINEL_MIN && l.addr != SENTINEL_MAX)
            .copied()
            .collect();
        let new_tree = CanonicalHeapTree::new(new_real, self.depth);
        let new_pos = new_tree.position_of(key)?;
        let (siblings, directions) = new_tree.prove_membership(new_pos)?;
        Some(HeapInsertWitness {
            new_leaf,
            siblings,
            directions,
            old_root: self.root(),
            new_root: new_tree.root(),
        })
    }
}

/// Compute the canonical heap root over a set of `(addr, value)` leaves at
/// the canonical depth ([`HEAP_TREE_DEPTH`]). THE function the executor (and,
/// when the cell-state splice lands, the cell) calls; the circuit's
/// `heap_root` register is seeded/advanced against this same value.
pub fn compute_heap_root(leaves: Vec<HeapLeaf>) -> BabyBear {
    CanonicalHeapTree::new(leaves, HEAP_TREE_DEPTH).root()
}

/// Compute the canonical heap root over raw `((coll, key), value)` entries:
/// addresses each entry via [`heap_addr`] then builds the sorted tree.
pub fn compute_heap_root_entries(entries: &[((BabyBear, BabyBear), BabyBear)]) -> BabyBear {
    compute_heap_root(
        entries
            .iter()
            .map(|((coll, key), value)| HeapLeaf {
                addr: heap_addr(*coll, *key),
                value: *value,
            })
            .collect(),
    )
}

/// The canonical heap root of the EMPTY heap (only the two sentinels). This
/// is the value a fresh cell's `heap_root` register seeds with. Deterministic
/// and cell-independent.
pub fn empty_heap_root() -> BabyBear {
    compute_heap_root(Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(coll: u32, key: u32, value: u32) -> HeapLeaf {
        HeapLeaf {
            addr: heap_addr(BabyBear::new(coll), BabyBear::new(key)),
            value: BabyBear::new(value),
        }
    }

    /// The empty root is deterministic and non-zero (the sentinels hash into
    /// a real value, not the all-zero default — the cap-root disjoint-seed
    /// bug class).
    #[test]
    fn empty_root_deterministic_and_nonzero() {
        let a = empty_heap_root();
        let b = empty_heap_root();
        assert_eq!(a, b, "empty root is deterministic");
        assert_ne!(a, BabyBear::ZERO, "empty root is NOT the ZERO default");
        // And distinct from the empty CAP root (different leaf shapes must
        // not make the two map families alias on empty).
        assert_ne!(
            a,
            crate::cap_root::empty_capability_root(),
            "empty heap root must not alias the empty capability root"
        );
    }

    /// Writing an entry moves the root (the commitment is load-bearing).
    #[test]
    fn write_moves_root() {
        let empty = empty_heap_root();
        let with_one = compute_heap_root(vec![entry(3, 4, 42)]);
        assert_ne!(empty, with_one, "a written entry must move the root");
    }

    /// The root is order-independent in the INPUT (the tree sorts by addr),
    /// so the same heap presented in any order yields the same root —
    /// `Substrate.Heap.root_deterministic`'s Rust face.
    #[test]
    fn root_is_input_order_independent() {
        let a = compute_heap_root(vec![entry(1, 1, 10), entry(1, 2, 20), entry(2, 1, 30)]);
        let b = compute_heap_root(vec![entry(2, 1, 30), entry(1, 1, 10), entry(1, 2, 20)]);
        assert_eq!(a, b, "sorted tree: input order must not change the root");
    }

    /// ANTI-GHOST (value): the same `(coll, key)` with a different value
    /// yields a different root — `tampered_value_moves_root`'s Rust face.
    #[test]
    fn tampered_value_moves_root() {
        let a = compute_heap_root(vec![entry(3, 4, 42)]);
        let b = compute_heap_root(vec![entry(3, 4, 99)]);
        assert_ne!(a, b, "the written value must bind the root");
    }

    /// ANTI-GHOST (address): the same value at a different `(coll, key)`
    /// yields a different root — `tampered_addr_moves_root`'s Rust face. Both
    /// the collection and the key bind.
    #[test]
    fn tampered_addr_moves_root() {
        let base = compute_heap_root(vec![entry(3, 4, 42)]);
        let other_key = compute_heap_root(vec![entry(3, 5, 42)]);
        let other_coll = compute_heap_root(vec![entry(5, 4, 42)]);
        assert_ne!(base, other_key, "the key must bind the root");
        assert_ne!(base, other_coll, "the collection must bind the root");
    }

    /// An in-place update witness authenticates the old leaf and recomputes
    /// the post-write root over the shared path: `new_root` equals the root
    /// of the independently rebuilt post-write tree.
    #[test]
    fn update_witness_recomputes_post_root() {
        let tree = CanonicalHeapTree::new(
            vec![entry(1, 1, 10), entry(1, 2, 20), entry(2, 1, 30)],
            HEAP_TREE_DEPTH,
        );
        let new_leaf = HeapLeaf {
            addr: heap_addr(BabyBear::new(1), BabyBear::new(2)),
            value: BabyBear::new(77),
        };
        let w = tree.update_witness(new_leaf).expect("addr is present");
        assert_eq!(w.old_leaf.value, BabyBear::new(20));
        assert_eq!(w.old_root, tree.root());
        let rebuilt =
            compute_heap_root(vec![entry(1, 1, 10), entry(1, 2, 77), entry(2, 1, 30)]);
        assert_eq!(
            w.new_root, rebuilt,
            "path-recomputed post-root must equal the rebuilt tree root"
        );
        // A fabricated (absent) address has no authenticated witness.
        let absent = HeapLeaf {
            addr: heap_addr(BabyBear::new(9), BabyBear::new(9)),
            value: BabyBear::new(1),
        };
        assert!(tree.update_witness(absent).is_none());
    }

    /// A sorted INSERT witness authenticates the new leaf against the new root,
    /// and the new root equals the root of the independently rebuilt tree.
    #[test]
    fn insert_witness_recomputes_post_root() {
        let tree = CanonicalHeapTree::new(
            vec![entry(1, 1, 10), entry(1, 3, 30)],
            HEAP_TREE_DEPTH,
        );
        let new_leaf = HeapLeaf {
            addr: heap_addr(BabyBear::new(1), BabyBear::new(2)),
            value: BabyBear::new(20),
        };
        let w = tree.insert_witness(new_leaf).expect("addr is fresh");
        assert_eq!(w.old_root, tree.root());
        let rebuilt = compute_heap_root(vec![
            entry(1, 1, 10),
            entry(1, 2, 20),
            entry(1, 3, 30),
        ]);
        assert_eq!(
            w.new_root, rebuilt,
            "insert-witness new root must equal the rebuilt tree root"
        );
        // Recompute the path top from the witness to cross-check.
        let mut cur = new_leaf.digest();
        for level in 0..HEAP_TREE_DEPTH {
            cur = if w.directions[level] == 0 {
                hash_fact(cur, &[w.siblings[level]])
            } else {
                hash_fact(w.siblings[level], &[cur])
            };
        }
        assert_eq!(cur, w.new_root, "witness path must open to the new root");
        // A present address has no insert witness.
        assert!(tree.insert_witness(entry(1, 1, 99)).is_none());
    }
}
