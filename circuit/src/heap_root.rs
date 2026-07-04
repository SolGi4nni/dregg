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

use crate::faithful8::Faithful8;
use crate::field::BabyBear;
use crate::poseidon2::{hash_fact, hash_many};
use std::sync::LazyLock;

pub use crate::dsl::revocation::{SENTINEL_MAX, SENTINEL_MIN};

/// Tree depth for the canonical heap tree. Matches
/// [`crate::cap_root::CAP_TREE_DEPTH`]: a binary tree of depth 16 holds
/// `2^16 - 2 = 65534` entries (two positions reserved for the MIN/MAX
/// sentinels). Per-cell heaps never re-rotate the tree in practice.
pub const HEAP_TREE_DEPTH: usize = 16;

/// The heap tree's internal node hash: `hash_fact(l, [r])` — the SAME node hash
/// [`CanonicalHeapTree::new`] folds with and the witness paths recompose with.
/// Factored out so the sparse fold and the empty-subtree precompute share it.
fn heap_node(l: BabyBear, r: BabyBear) -> BabyBear {
    hash_fact(l, &[r])
}

/// The precomputed **empty-subtree roots** for the canonical heap tree at every
/// level `0..=HEAP_TREE_DEPTH`. `EMPTY_SUBTREE_ROOTS[0]` is the empty-leaf
/// digest (`BabyBear::ZERO`, the padding marker [`CanonicalHeapTree::new`] uses);
/// `EMPTY_SUBTREE_ROOTS[k]` is `heap_node(empty[k-1], empty[k-1])` — the root a
/// node whose entire subtree is padding folds to.
///
/// These are the values the DENSE build placed at any node covering only
/// padding positions. The sparse fold reads them in place of folding 65k zeros,
/// and a membership path whose sibling subtree is all-padding reports the same
/// constant the dense build would — so roots and witnesses stay byte-identical.
static EMPTY_SUBTREE_ROOTS: LazyLock<[BabyBear; HEAP_TREE_DEPTH + 1]> = LazyLock::new(|| {
    let mut roots = [BabyBear::ZERO; HEAP_TREE_DEPTH + 1];
    for level in 1..=HEAP_TREE_DEPTH {
        roots[level] = heap_node(roots[level - 1], roots[level - 1]);
    }
    roots
});

/// The empty-subtree root at `level` (`0` = the ZERO leaf digest, `depth` = the
/// root of an all-padding tree). Used both by the sparse fold and by
/// `prove_membership` to report all-padding siblings.
fn heap_empty_subtree_root(level: usize) -> BabyBear {
    EMPTY_SUBTREE_ROOTS[level]
}

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
    /// All levels, bottom-up, stored **sparsely** as the non-empty PREFIX of
    /// each level. `levels[k]` holds exactly the real-bearing nodes at level `k`
    /// (positions `0..levels[k].len()`); every node at an index `>= levels[k].len()`
    /// covers only padding and equals [`heap_empty_subtree_root`]`(k)`.
    ///
    /// The real leaves are placed contiguously at the start of the bottom level
    /// (sorted, then padded), so each level's non-empty nodes are themselves a
    /// contiguous prefix — this prefix is all the dense build ever computed to a
    /// non-empty value. `node(level, idx)` reconstructs any position byte-
    /// identically to the old dense `levels[level][idx]`.
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

        let _ = capacity; // (asserted above; the sparse fold never materializes padding)
        // The real leaf digests (positions `0..n`); every position `>= n` is the
        // ZERO padding leaf the dense build `resize`d in. We never materialize
        // those zeros — the sparse fold folds only this prefix against the
        // precomputed empty-subtree roots.
        let leaf_digests: Vec<BabyBear> = leaves.iter().map(HeapLeaf::digest).collect();
        debug_assert!(leaf_digests.len() <= capacity);

        // Fold ONLY the non-empty prefix at each level (see CanonicalCapTree::new
        // for the contiguous-prefix argument): a parent at index `i` covers
        // children `2i`, `2i+1`; a child outside the stored prefix is the
        // empty-subtree root for the child's level. O(n·depth) node hashes for
        // `n` real leaves, not the dense `2^depth - 1`.
        let mut levels: Vec<Vec<BabyBear>> = Vec::with_capacity(depth + 1);
        levels.push(leaf_digests);
        for level in 0..depth {
            let prev = levels.last().unwrap();
            let prev_len = prev.len();
            let next_len = prev_len.div_ceil(2);
            let mut next_level = Vec::with_capacity(next_len);
            for i in 0..next_len {
                let l = prev[2 * i];
                let r = prev
                    .get(2 * i + 1)
                    .copied()
                    .unwrap_or_else(|| heap_empty_subtree_root(level));
                next_level.push(heap_node(l, r));
            }
            levels.push(next_level);
        }

        Self {
            levels,
            sorted_leaves: leaves,
            depth,
        }
    }

    /// The value at `(level, idx)`, reconstructing the dense node byte-
    /// identically: the stored prefix value if `idx` is within it, else the
    /// precomputed empty-subtree root for `level` (an all-padding node).
    fn node(&self, level: usize, idx: usize) -> BabyBear {
        self.levels[level]
            .get(idx)
            .copied()
            .unwrap_or_else(|| heap_empty_subtree_root(level))
    }

    /// The Merkle root. `levels[depth]` always holds exactly the single root
    /// node (the two sentinels guarantee `2 <= n <= 2^depth`, so the top-level
    /// prefix length is `ceil(n / 2^depth) == 1`).
    pub fn root(&self) -> BabyBear {
        self.node(self.depth, 0)
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

    /// All level vectors, bottom-up, stored SPARSELY: `levels[k]` is the
    /// non-empty PREFIX of level `k` (positions `0..levels[k].len()`); any node
    /// at index `>= levels[k].len()` is the all-padding [`heap_empty_subtree_root`]`(k)`.
    /// `levels[0]` is the real (unpadded) leaf-digest prefix; `levels[depth]` is
    /// `[root]`. Exposed for membership witnessing.
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
            siblings.push(self.node(level, sibling_idx));
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

// ============================================================================
// FAITHFUL 8-FELT HEAP ROOT (Phase H-HEAP-8) — the SECOND faithful root.
//
// The lossy 1-felt `heap_node` / `HeapLeaf::digest` above project the sorted-
// Merkle heap to a single BabyBear (~2^31), well below the deployed FRI/STARK
// ~124-bit soundness floor: two GENUINELY-different heaps can collide on the
// 1-felt root while topping different 8-felt roots (the heap GENTIAN tooth
// `circuit/tests/heap_root_gentian_weld.rs` exhibits a concrete pair). The
// native 8-felt heap tree closes that hole, EXACTLY mirroring the cap tree's
// `cap_node8` / `CAP_DIGEST_W` weld: every node absorbs full 8-felt children
// through the arity-16 `node8` chip and emits a full 8-felt digest, so the
// per-node collision floor is the full ~124-bit width. Reuses the SAME
// `descriptor_ir2::chip_absorb_all_lanes` compression the cap tree commits.
// ============================================================================

/// The number of felts in a native heap-tree digest (Phase H-HEAP-8: the heap
/// tree is 8-felt, faithful to the FRI ~124-bit soundness floor, no longer the
/// lossy 1-felt `heap_node`). A leaf / node / root is `[BabyBear; HEAP_DIGEST_W]`.
/// The twin of [`crate::cap_root::CAP_DIGEST_W`].
pub const HEAP_DIGEST_W: usize = 8;

/// The all-zero 8-felt digest — the PADDING / empty-leaf marker (the 8-felt
/// twin of the `BabyBear::ZERO` the 1-felt tree padded with).
/// `EMPTY_SUBTREE_ROOTS_8[0]` is this. Twin of [`crate::cap_root::CAP_ZERO8`].
pub const HEAP_ZERO8: [BabyBear; HEAP_DIGEST_W] = [BabyBear::ZERO; HEAP_DIGEST_W];

/// **`heap_node8`** — the native 8-felt heap-tree internal node: the arity-16
/// `node8` chip compression `perm(L8 ‖ R8)[0..8]`
/// (`descriptor_ir2::chip_absorb_all_lanes` at `CHIP_NODE8_ARITY = 16`).
/// Replaces the lossy 1-felt `heap_node` for the canonical heap tree; EQUALITY-
/// binds all 8 output lanes to both 8-felt children, so the per-node collision
/// floor is full 8-felt width (~124-bit), matching the deployed FRI/STARK
/// soundness. The IDENTICAL compression [`crate::cap_root::cap_node8`] commits —
/// cap/heap/fields all share this ONE node8 lane.
///
/// PUBLIC so the heap-open trace scaffold fills its per-level `cur8/sib8/node8`
/// columns from the SAME compression the heap tree commits.
pub fn heap_node8(
    l: [BabyBear; HEAP_DIGEST_W],
    r: [BabyBear; HEAP_DIGEST_W],
) -> [BabyBear; HEAP_DIGEST_W] {
    let mut ins = [BabyBear::ZERO; 16];
    ins[..HEAP_DIGEST_W].copy_from_slice(&l);
    ins[HEAP_DIGEST_W..].copy_from_slice(&r);
    crate::descriptor_ir2::chip_absorb_all_lanes(crate::descriptor_ir2::CHIP_NODE8_ARITY, &ins)
}

impl HeapLeaf {
    /// The native 8-felt leaf digest: the SINGLE arity-2 chip absorb of
    /// `[addr, value]`, squeezing ALL 8 output lanes (Phase H-HEAP-8), byte-
    /// identical to the IR-v2 Poseidon2 chip's `BUS_P2` leaf absorb
    /// (`descriptor_ir2` `chip_absorb_tuple([addr, value], out0, lanes 1..7)`).
    /// Lane 0 equals the lossy [`HeapLeaf::digest`] (`hash_many[addr, value]` is
    /// the same permutation's out0); lanes 1..7 are the faithful completion the
    /// 1-felt chain dropped. Twin of [`crate::cap_root::CapLeaf::digest`].
    pub fn digest8(&self) -> [BabyBear; HEAP_DIGEST_W] {
        crate::descriptor_ir2::chip_absorb_all_lanes(2, &[self.addr, self.value])
    }
}

/// The precomputed 8-felt **empty-subtree roots** at every level `0..=DEPTH`.
/// `EMPTY_SUBTREE_ROOTS_8[0]` is the ZERO8 padding-leaf digest;
/// `EMPTY_SUBTREE_ROOTS_8[k] = heap_node8(empty8[k-1], empty8[k-1])`. Twin of
/// [`crate::cap_root`]'s `EMPTY_SUBTREE_ROOTS` at 8-felt width.
static EMPTY_SUBTREE_ROOTS_8: LazyLock<[[BabyBear; HEAP_DIGEST_W]; HEAP_TREE_DEPTH + 1]> =
    LazyLock::new(|| {
        let mut roots = [HEAP_ZERO8; HEAP_TREE_DEPTH + 1];
        for level in 1..=HEAP_TREE_DEPTH {
            roots[level] = heap_node8(roots[level - 1], roots[level - 1]);
        }
        roots
    });

/// The 8-felt empty-subtree root at `level`. Twin of [`heap_empty_subtree_root`].
pub fn heap_empty_subtree_root_8(level: usize) -> [BabyBear; HEAP_DIGEST_W] {
    EMPTY_SUBTREE_ROOTS_8[level]
}

/// **`compute_canonical_heap_root_8`** — the faithful 8-felt heap root over a
/// set of `(addr, value)` leaves at the canonical depth. THE producer the cell
/// recomputes (`compute_canonical_heap_root_8` in `dregg-cell`) and the rotated
/// commitment absorbs at limb 28 (lane 0) ‖ limbs 58..64 (lanes 1..7). The
/// 8-felt twin of [`compute_heap_root`] and of
/// [`crate::cap_root::compute_capability_root`]: same sorted+sentinel+padded
/// discipline, but every node folds through [`heap_node8`] and every leaf is
/// [`HeapLeaf::digest8`], so the whole commit is faithful to the ~124-bit floor.
///
/// The sparse fold (only the non-empty prefix per level, all-padding siblings
/// read from [`heap_empty_subtree_root_8`]) is byte-identical to the dense
/// build — the SAME contiguous-prefix argument the 1-felt [`CanonicalHeapTree::new`]
/// rests on, at 8-felt width.
///
/// Returns [`Faithful8`] — a genuine `node8` tree root, one of the named
/// faithful constructors of the commitment TYPE WALL
/// (`docs/FAITHFUL-COMMITMENT-LAW.md`).
pub fn compute_canonical_heap_root_8(leaves: Vec<HeapLeaf>) -> Faithful8 {
    let mut leaves = leaves;
    leaves.push(sentinel_leaf(SENTINEL_MIN));
    leaves.push(sentinel_leaf(SENTINEL_MAX));
    leaves.sort_by_key(|l| l.addr.as_u32());
    leaves.dedup_by_key(|l| l.addr.as_u32());

    let depth = HEAP_TREE_DEPTH;
    let capacity = 1usize << depth;
    assert!(
        leaves.len() <= capacity,
        "heap ({} entries incl. sentinels) exceeds tree capacity 2^{depth}",
        leaves.len()
    );

    // Sparse 8-felt fold: only the non-empty prefix per level; a child outside
    // the stored prefix is the 8-felt empty-subtree root for the child's level.
    let mut cur: Vec<[BabyBear; HEAP_DIGEST_W]> = leaves.iter().map(HeapLeaf::digest8).collect();
    for level in 0..depth {
        let prev_len = cur.len();
        let next_len = prev_len.div_ceil(2);
        let mut next_level = Vec::with_capacity(next_len);
        for i in 0..next_len {
            let l = cur[2 * i];
            let r = cur
                .get(2 * i + 1)
                .copied()
                .unwrap_or_else(|| heap_empty_subtree_root_8(level));
            next_level.push(heap_node8(l, r));
        }
        cur = next_level;
    }
    debug_assert_eq!(cur.len(), 1);
    Faithful8::from_root8(cur[0])
}

/// Compute the faithful 8-felt heap root over raw `((coll, key), value)`
/// entries: addresses each via [`heap_addr`] then folds the sorted 8-felt tree.
/// The 8-felt twin of [`compute_heap_root_entries`].
pub fn compute_canonical_heap_root_8_entries(
    entries: &[((BabyBear, BabyBear), BabyBear)],
) -> Faithful8 {
    compute_canonical_heap_root_8(
        entries
            .iter()
            .map(|((coll, key), value)| HeapLeaf {
                addr: heap_addr(*coll, *key),
                value: *value,
            })
            .collect(),
    )
}

/// The faithful 8-felt root of the EMPTY heap (only the two sentinels). The
/// 8-felt twin of [`empty_heap_root`]; the value the rotated commit absorbs for
/// a cell with no heap entries.
pub fn empty_heap_root_8() -> Faithful8 {
    compute_canonical_heap_root_8(Vec::new())
}

/// **`recompose_membership_8`** — fold a held leaf's 8-felt digest up the
/// `(sibling, direction)` path through [`heap_node8`], mixing `(cur, sib)` by
/// the direction bit (`dir = 0` ⇒ `cur` LEFT: `heap_node8(cur, sib)`; `dir = 1`
/// ⇒ `cur` RIGHT: `heap_node8(sib, cur)`). The producer-side twin of the
/// deployed in-circuit `node8` heap recompose (the MapOps chain, unified onto
/// `BUS_P2`) and of Lean `recomposeUp8`. Used by the 8-felt update/insert
/// witnesses and the circuit trace scaffold.
pub fn recompose_membership_8(
    leaf: [BabyBear; HEAP_DIGEST_W],
    siblings: &[[BabyBear; HEAP_DIGEST_W]],
    directions: &[u8],
) -> [BabyBear; HEAP_DIGEST_W] {
    let mut cur = leaf;
    for (sib, &dir) in siblings.iter().zip(directions.iter()) {
        cur = if dir == 0 {
            heap_node8(cur, *sib)
        } else {
            heap_node8(*sib, cur)
        };
    }
    cur
}

/// The canonical heap root of the EMPTY heap (only the two sentinels). This
/// is the value a fresh cell's `heap_root` register seeds with. Deterministic
/// and cell-independent.
pub fn empty_heap_root() -> BabyBear {
    compute_heap_root(Vec::new())
}

// ============================================================================
// FAITHFUL 8-FELT WITNESSES (Phase H-HEAP-8, step 2) — the 8-felt twin of the
// 1-felt `CanonicalHeapTree` + `HeapUpdateWitness` / `HeapInsertWitness`. The
// stored-levels sparse tree at 8-felt width feeds the in-circuit MapOps node8
// chains (`descriptor_ir2`, unified onto `BUS_P2`); every leaf is
// [`HeapLeaf::digest8`] and every node folds through [`heap_node8`], so the
// witnessed opening is faithful to the ~124-bit floor. Mirrors
// [`crate::cap_root::CanonicalCapTree`]'s 8-felt path.
// ============================================================================

/// The canonical heap tree at 8-felt width: the stored-levels sparse twin of
/// [`CanonicalHeapTree`], but each node is an 8-felt [`heap_node8`] digest and
/// each leaf is [`HeapLeaf::digest8`]. `root8()` equals
/// [`compute_canonical_heap_root_8`] over the same leaves.
#[derive(Clone, Debug)]
pub struct CanonicalHeapTree8 {
    /// All levels, bottom-up, stored SPARSELY as the non-empty PREFIX of each
    /// level (see [`CanonicalHeapTree`] for the contiguous-prefix argument),
    /// at 8-felt width. A node at index `>= levels[k].len()` is the all-padding
    /// [`heap_empty_subtree_root_8`]`(k)`.
    levels: Vec<Vec<[BabyBear; HEAP_DIGEST_W]>>,
    /// The leaves in sorted-by-`addr` order, including sentinels (pre-padding).
    sorted_leaves: Vec<HeapLeaf>,
    /// Tree depth.
    depth: usize,
}

impl CanonicalHeapTree8 {
    /// Build the canonical 8-felt heap tree from a cell's heap entries. Same
    /// sorted+sentinel+dedup+sparse-fold discipline as [`CanonicalHeapTree::new`],
    /// at 8-felt width.
    pub fn new(mut leaves: Vec<HeapLeaf>, depth: usize) -> Self {
        leaves.push(sentinel_leaf(SENTINEL_MIN));
        leaves.push(sentinel_leaf(SENTINEL_MAX));
        leaves.sort_by_key(|l| l.addr.as_u32());
        leaves.dedup_by_key(|l| l.addr.as_u32());

        let capacity = 1usize << depth;
        assert!(
            leaves.len() <= capacity,
            "heap ({} entries incl. sentinels) exceeds tree capacity 2^{depth}",
            leaves.len()
        );

        let leaf_digests: Vec<[BabyBear; HEAP_DIGEST_W]> =
            leaves.iter().map(HeapLeaf::digest8).collect();
        let mut levels: Vec<Vec<[BabyBear; HEAP_DIGEST_W]>> = Vec::with_capacity(depth + 1);
        levels.push(leaf_digests);
        for level in 0..depth {
            let prev = levels.last().unwrap();
            let prev_len = prev.len();
            let next_len = prev_len.div_ceil(2);
            let mut next_level = Vec::with_capacity(next_len);
            for i in 0..next_len {
                let l = prev[2 * i];
                let r = prev
                    .get(2 * i + 1)
                    .copied()
                    .unwrap_or_else(|| heap_empty_subtree_root_8(level));
                next_level.push(heap_node8(l, r));
            }
            levels.push(next_level);
        }

        Self {
            levels,
            sorted_leaves: leaves,
            depth,
        }
    }

    /// The 8-felt value at `(level, idx)`: the stored prefix value if in-prefix,
    /// else the all-padding [`heap_empty_subtree_root_8`]`(level)`.
    fn node8(&self, level: usize, idx: usize) -> [BabyBear; HEAP_DIGEST_W] {
        self.levels[level]
            .get(idx)
            .copied()
            .unwrap_or_else(|| heap_empty_subtree_root_8(level))
    }

    /// The 8-felt Merkle root. Returns [`Faithful8`] — a genuine `node8` tree
    /// root, one of the named faithful constructors of the commitment TYPE
    /// WALL (`docs/FAITHFUL-COMMITMENT-LAW.md`).
    pub fn root8(&self) -> Faithful8 {
        Faithful8::from_root8(self.node8(self.depth, 0))
    }

    /// The sorted leaves (including sentinels).
    pub fn sorted_leaves(&self) -> &[HeapLeaf] {
        &self.sorted_leaves
    }

    /// The padded-level position of the leaf whose `addr == key`, or `None`.
    pub fn position_of(&self, key: BabyBear) -> Option<usize> {
        self.sorted_leaves.iter().position(|l| l.addr == key)
    }

    /// The 8-felt membership path `(siblings8, directions)` for the leaf at
    /// `position`. Same direction convention as [`CanonicalHeapTree::prove_membership`].
    pub fn prove_membership(
        &self,
        position: usize,
    ) -> Option<(Vec<[BabyBear; HEAP_DIGEST_W]>, Vec<u8>)> {
        let capacity = 1usize << self.depth;
        if position >= capacity {
            return None;
        }
        let mut siblings = Vec::with_capacity(self.depth);
        let mut directions = Vec::with_capacity(self.depth);
        let mut idx = position;
        for level in 0..self.depth {
            let sibling_idx = idx ^ 1;
            siblings.push(self.node8(level, sibling_idx));
            directions.push((idx & 1) as u8);
            idx >>= 1;
        }
        Some((siblings, directions))
    }

    /// Build an 8-felt [`HeapUpdateWitness8`] for an in-place value write at an
    /// EXISTING address. The 8-felt twin of [`CanonicalHeapTree::update_witness`]:
    /// `new_root8` is recomposed over the SAME sibling path via [`heap_node8`].
    pub fn update_witness(&self, new_leaf: HeapLeaf) -> Option<HeapUpdateWitness8> {
        let pos = self.position_of(new_leaf.addr)?;
        let old_leaf = self.sorted_leaves[pos];
        let (siblings, directions) = self.prove_membership(pos)?;
        let new_root = recompose_membership_8(new_leaf.digest8(), &siblings, &directions);
        Some(HeapUpdateWitness8 {
            old_leaf,
            new_leaf,
            siblings,
            directions,
            old_root: self.root8().limbs(),
            new_root,
        })
    }

    /// Build an 8-felt sorted INSERT witness for a FRESH address. The 8-felt
    /// twin of [`CanonicalHeapTree::insert_witness`].
    pub fn insert_witness(&self, new_leaf: HeapLeaf) -> Option<HeapInsertWitness8> {
        let key = new_leaf.addr;
        if key == SENTINEL_MIN || key.as_u32() >= SENTINEL_MAX.as_u32() {
            return None;
        }
        if self.position_of(key).is_some() {
            return None;
        }
        let pos = self.sorted_leaves.iter().position(|l| l.addr > key)?;
        let new_real: Vec<HeapLeaf> = self.sorted_leaves[..pos]
            .iter()
            .chain(std::iter::once(&new_leaf))
            .chain(&self.sorted_leaves[pos..])
            .filter(|l| l.addr != SENTINEL_MIN && l.addr != SENTINEL_MAX)
            .copied()
            .collect();
        let new_tree = CanonicalHeapTree8::new(new_real, self.depth);
        let new_pos = new_tree.position_of(key)?;
        let (siblings, directions) = new_tree.prove_membership(new_pos)?;
        Some(HeapInsertWitness8 {
            new_leaf,
            siblings,
            directions,
            old_root: self.root8().limbs(),
            new_root: new_tree.root8().limbs(),
        })
    }
}

/// The 8-felt twin of [`HeapUpdateWitness`]: 8-felt siblings and roots. The
/// old leaf opens against `old_root` (8-felt); the new leaf recomposes to
/// `new_root` over the SAME sibling path.
#[derive(Clone, Debug)]
pub struct HeapUpdateWitness8 {
    /// The OLD (pre-write) leaf.
    pub old_leaf: HeapLeaf,
    /// The NEW (post-write) leaf — same `addr`, new value.
    pub new_leaf: HeapLeaf,
    /// 8-felt sibling digests bottom-up.
    pub siblings: Vec<[BabyBear; HEAP_DIGEST_W]>,
    /// Direction bits (0 = current is left child).
    pub directions: Vec<u8>,
    /// The authenticated old 8-felt root.
    pub old_root: [BabyBear; HEAP_DIGEST_W],
    /// The recomposed new 8-felt root.
    pub new_root: [BabyBear; HEAP_DIGEST_W],
}

/// The 8-felt twin of [`HeapInsertWitness`].
#[derive(Clone, Debug)]
pub struct HeapInsertWitness8 {
    /// The inserted leaf.
    pub new_leaf: HeapLeaf,
    /// 8-felt sibling digests bottom-up.
    pub siblings: Vec<[BabyBear; HEAP_DIGEST_W]>,
    /// Direction bits.
    pub directions: Vec<u8>,
    /// The authenticated pre-insert 8-felt root.
    pub old_root: [BabyBear; HEAP_DIGEST_W],
    /// The recomposed post-insert 8-felt root.
    pub new_root: [BabyBear; HEAP_DIGEST_W],
}

/// Compute the 8-felt canonical heap tree over a cell's entries — the
/// stored-levels object the circuit trace scaffold witnesses against. Twin of
/// [`compute_canonical_heap_root_8`] but retains the levels for openings.
pub fn canonical_heap_tree_8(leaves: Vec<HeapLeaf>) -> CanonicalHeapTree8 {
    CanonicalHeapTree8::new(leaves, HEAP_TREE_DEPTH)
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
            crate::cap_root::empty_capability_root()[0],
            "empty heap root must not alias the empty capability root (lane 0)"
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
        let rebuilt = compute_heap_root(vec![entry(1, 1, 10), entry(1, 2, 77), entry(2, 1, 30)]);
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
        let tree = CanonicalHeapTree::new(vec![entry(1, 1, 10), entry(1, 3, 30)], HEAP_TREE_DEPTH);
        let new_leaf = HeapLeaf {
            addr: heap_addr(BabyBear::new(1), BabyBear::new(2)),
            value: BabyBear::new(20),
        };
        let w = tree.insert_witness(new_leaf).expect("addr is fresh");
        assert_eq!(w.old_root, tree.root());
        let rebuilt = compute_heap_root(vec![entry(1, 1, 10), entry(1, 2, 20), entry(1, 3, 30)]);
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

    // ---- SPARSE-FOLD BYTE-IDENTITY DIFFERENTIAL (temp; pins step 1 of INCREMENTAL-COMMITMENT.md) ----

    struct Rng(u64);
    impl Rng {
        fn next_u64(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn below(&mut self, n: u32) -> u32 {
            (self.next_u64() % n as u64) as u32
        }
    }

    /// The OLD DENSE build, kept verbatim as the in-test oracle: assemble the
    /// sorted/deduped leaf list EXACTLY as `new`, then `resize` to the full
    /// `2^depth` with ZERO padding and fold ALL levels. Returns `(sorted_leaves,
    /// levels)` so membership can be cross-checked against the dense arrays.
    fn dense_build(leaves: Vec<HeapLeaf>, depth: usize) -> (Vec<HeapLeaf>, Vec<Vec<BabyBear>>) {
        let mut leaves = leaves;
        leaves.push(sentinel_leaf(SENTINEL_MIN));
        leaves.push(sentinel_leaf(SENTINEL_MAX));
        leaves.sort_by_key(|l| l.addr.as_u32());
        leaves.dedup_by_key(|l| l.addr.as_u32());
        let capacity = 1usize << depth;
        assert!(leaves.len() <= capacity);
        let mut leaf_digests: Vec<BabyBear> = leaves.iter().map(HeapLeaf::digest).collect();
        leaf_digests.resize(capacity, BabyBear::ZERO);
        let mut levels = vec![leaf_digests];
        for _ in 0..depth {
            let prev = levels.last().unwrap();
            let mut next = Vec::with_capacity(prev.len() / 2);
            for chunk in prev.chunks(2) {
                next.push(hash_fact(chunk[0], &[chunk[1]]));
            }
            levels.push(next);
        }
        (leaves, levels)
    }

    fn rand_entry(rng: &mut Rng) -> HeapLeaf {
        entry(rng.below(64), rng.below(64), rng.next_u64() as u32)
    }

    /// THE DIFFERENTIAL: 10k random heaps (varying size incl. empty); the SPARSE
    /// `new` must produce the byte-identical root AND byte-identical membership
    /// paths for every present leaf, vs the dense oracle. Small depth keeps the
    /// dense oracle affordable; the fold is depth-independent.
    #[test]
    fn sparse_matches_dense_root_and_membership() {
        const CASES: usize = 10_000;
        const DEPTH: usize = 8;
        let mut rng = Rng(0x4EAB_F00D_1234_0001);
        let mut mismatches = 0usize;
        let mut total_leaves = 0usize;
        for _ in 0..CASES {
            let n = rng.below(60) as usize;
            let leaves: Vec<HeapLeaf> = (0..n).map(|_| rand_entry(&mut rng)).collect();
            let sparse = CanonicalHeapTree::new(leaves.clone(), DEPTH);
            let (oracle_leaves, oracle_levels) = dense_build(leaves, DEPTH);

            if sparse.root() != oracle_levels[DEPTH][0] {
                mismatches += 1;
                continue;
            }
            assert_eq!(sparse.sorted_leaves(), oracle_leaves.as_slice());
            for pos in 0..oracle_leaves.len() {
                total_leaves += 1;
                let (s_sib, s_dir) = sparse.prove_membership(pos).unwrap();
                let mut d_sib = Vec::with_capacity(DEPTH);
                let mut d_dir = Vec::with_capacity(DEPTH);
                let mut idx = pos;
                for level in 0..DEPTH {
                    d_sib.push(oracle_levels[level][idx ^ 1]);
                    d_dir.push((idx & 1) as u8);
                    idx >>= 1;
                }
                if s_sib != d_sib || s_dir != d_dir {
                    mismatches += 1;
                    break;
                }
            }
        }
        assert_eq!(
            mismatches, 0,
            "sparse heap-tree fold must be byte-identical to the dense build over {CASES} cases ({total_leaves} membership paths checked)"
        );
    }

    /// Byte-identity at the CANONICAL depth-16 too: root + every membership path
    /// for a handful of heaps match the dense depth-16 oracle.
    #[test]
    fn sparse_matches_dense_at_depth_16() {
        let cases: Vec<Vec<HeapLeaf>> = vec![
            vec![],
            vec![entry(3, 4, 42)],
            vec![entry(1, 1, 10), entry(1, 2, 20), entry(2, 1, 30)],
            (0..50)
                .map(|i| entry(i, i + 1, i.wrapping_mul(11)))
                .collect(),
        ];
        for leaves in cases {
            let sparse = CanonicalHeapTree::new(leaves.clone(), HEAP_TREE_DEPTH);
            let (oracle_leaves, oracle_levels) = dense_build(leaves, HEAP_TREE_DEPTH);
            assert_eq!(
                sparse.root(),
                oracle_levels[HEAP_TREE_DEPTH][0],
                "depth-16 root"
            );
            assert_eq!(sparse.sorted_leaves(), oracle_leaves.as_slice());
            for pos in 0..oracle_leaves.len() {
                let (s_sib, s_dir) = sparse.prove_membership(pos).unwrap();
                let mut idx = pos;
                for level in 0..HEAP_TREE_DEPTH {
                    assert_eq!(
                        s_sib[level],
                        oracle_levels[level][idx ^ 1],
                        "sibling@{level} pos {pos}"
                    );
                    assert_eq!(s_dir[level], (idx & 1) as u8);
                    idx >>= 1;
                }
            }
        }
    }
}
