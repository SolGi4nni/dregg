//! The canonical, **openable** capability-set commitment: a SORTED Poseidon2
//! binary Merkle tree over a cell's c-list.
//!
//! ## Why this module exists (audit P0-3 / cap Phase A)
//!
//! The cell crate's `compute_canonical_capability_root` was a BLAKE3 XOR-fold,
//! while the EffectVM circuit's `cap_root` column was a Poseidon2 fold
//! initialized to `BabyBear::ZERO` and advanced by per-effect edge-mutations.
//! The two were **disjoint**: the prover seeded the circuit's `cap_root` from
//! ZERO, never from the cell's real capability root, so nothing tied the
//! circuit-side capability digest to the authoritative c-list. An openable
//! membership proof (Phase B: in-circuit non-amplification / authority gates)
//! had no shared root to open against.
//!
//! This module supplies the **single** capability-root scheme, computed
//! byte-identically wherever it runs:
//!
//!   * `dregg-cell`'s `compute_canonical_capability_root` calls
//!     [`compute_capability_root`] (cell → circuit, the only direction the
//!     dependency graph permits — circuit's dep on cell is dev-only).
//!   * The EffectVM circuit seeds its `cap_root` column from the same value
//!     (`CellState::new` / the node + cipherclerk prover paths).
//!
//! Because there is exactly ONE implementation, the cell-side root and the
//! circuit-side seed are identical by construction; the differential test
//! `circuit/tests/cap_root_cell_circuit_differential.rs` is the guard that pins
//! it (the A2 gate).
//!
//! ## The scheme (mirrors the proven [`crate::dsl::revocation::DslRevocationTree`])
//!
//! A SORTED binary Merkle tree over the c-list, **keyed by `slot_hash`** (the
//! slot is unique per c-list — the executor's `validate_capability_uniqueness`
//! enforces it — so the key is injective: exactly one leaf per slot). The
//! keys are sorted, deduplicated, and bracketed by the
//! [`SENTINEL_MIN`](crate::dsl::revocation::SENTINEL_MIN) /
//! [`SENTINEL_MAX`](crate::dsl::revocation::SENTINEL_MAX) sentinels (so a
//! Phase-B non-membership proof can bracket any absent key). The tree is
//! padded to `2^DEPTH` positions; internal nodes are
//! `hash_fact(left, [right])` — the SAME node hash the revocation tree uses.
//!
//! Each leaf is `Poseidon2(slot_hash, target, auth_tag, mask_lo, mask_hi,
//! expiry, breadstuff)` — the 7 [`CapLeaf`] fields:
//!
//!   * `slot_hash`  — the sort key, a Poseidon2 image of the c-list slot.
//!   * `target`     — the capability's target cell id, folded to one felt.
//!   * `auth_tag`   — the `AuthRequired` tier byte (None=0…Custom=5) with the
//!     8 vk_hash limbs absorbed for the `Custom` case (mirrors the cell's
//!     `hash_auth_required_into`), so two `Custom`s with distinct vk_hashes
//!     yield distinct leaves.
//!   * `mask_lo` / `mask_hi` — the `EffectMask` (u32) split low-16 / high-16
//!     (two 16-bit limbs, NOT one 30-bit limb — `EFFECT_ALL = 0xFFFF_FFFF`
//!     needs the full 32 bits).
//!   * `expiry`     — the optional expiry height (`None` is a reserved sentinel
//!     distinct from any finite height).
//!   * `breadstuff` — the optional capability-token hash, folded to one felt
//!     (`None` reserved). Included because two caps differing only in
//!     breadstuff must not collide.
//!
//! ## Phase A scope
//!
//! Phase A makes the `cap_root` VALUE this sorted-Merkle root and seeds the
//! circuit column from the real cell root. The per-effect `cap_root` ADVANCE
//! stays pinned-as-digest (the circuit pins the executor's computed new root;
//! it does NOT yet recompute the sorted-tree update in-circuit), and there are
//! NO in-circuit membership-open / submask / non-amplification gates yet —
//! those are Phase B.

use crate::faithful8::Faithful8;
use crate::field::BabyBear;
use crate::poseidon2::{Poseidon2State, hash_many};
use std::sync::LazyLock;

pub use crate::dsl::revocation::{SENTINEL_MAX, SENTINEL_MIN};

/// The `hash_fact` domain-separation marker (`poseidon2.rs::hash_fact` state[5]),
/// here absorbed as the FIRST RATE input of the cap node's arity-3 chip absorb
/// (`descriptor_ir2.rs::FACT_MARK`, `DeployedCapTree.FACT_MARK`). Used as a rate
/// input so the node is ONE chip-realizable absorb, not the capacity-tagged
/// `hash_fact` permute.
///
/// PUBLIC so the standalone cap-membership DSL AIR's `Hash3Cap` node form
/// (`dsl_p3_air::hash_input_state`) seeds the SAME `FACT_MARK` rate input.
pub const CAP_FACT_MARK: u32 = 0xFACF;

/// **`cap_chip_absorb`** — the SINGLE in-circuit chip hash the cap-tree commits to,
/// byte-identical to the IR-v2 Poseidon2 chip's BUS_P2 absorb (`descriptor_ir2.rs`
/// `Ir2Air::Chip`). One width-16 Poseidon2 permutation; squeeze state[0].
///
/// The chip distinguishes two seedings by `big = [arity == 7]`:
///   * `arity ≤ 4` (rate-4): `state[0..len] = ins`, `state[4] = len` (the arity tag),
///     `state[5..] = 0`.
///   * `arity == 7` (rate-8 leaf): `state[0..7] = ins`, no tag lane (`state[7..] = 0`).
///
/// The cap NODE is the arity-3 absorb of `[CAP_FACT_MARK, l, r]`; the cap LEAF is the
/// arity-7 absorb of the 7 leaf fields. Both ride this one hash — the unification that
/// discharges Lean's `SchemeRealizedByChip`.
///
/// PUBLIC so the cap-open trace scaffold (`effect_vm::trace_rotated`) fills its leaf /
/// node columns from the SAME hash the cap-tree commits — one cap hash across the whole
/// crate (the unification's Rust invariant).
pub fn cap_chip_absorb(ins: &[BabyBear]) -> BabyBear {
    let len = ins.len();
    debug_assert!(
        len == 3 || len == 7,
        "cap_chip_absorb only commits the arity-3 node / arity-7 leaf shapes"
    );
    let mut st = [BabyBear::ZERO; crate::poseidon2::WIDTH];
    for (i, &x) in ins.iter().enumerate() {
        st[i] = x;
    }
    if len != 7 {
        // Rate-4 seeding: the length tag rides state[4] (the `big = 0` branch).
        st[4] = BabyBear::new(len as u32);
    }
    // (arity 7 ⇒ `big = 1`: state[4..7] are the genuine inputs in4..in6, no tag.)
    let mut state = Poseidon2State { state: st };
    state.permute();
    state.state[0]
}

/// The cap-tree internal node hash: the arity-3 chip absorb of `[CAP_FACT_MARK, l, r]`
/// (`DeployedCapTree.nodeOf` = `sponge [FACT_MARK, l, r]`). Replaces the deployed
/// capacity-tagged `hash_fact(l, [r])` — one in-circuit hash everywhere.
///
/// PUBLIC so the standalone cap-membership DSL AIR (`dsl::cap_membership`, via the
/// `ConstraintExpr::Hash3Cap` node form) folds with the SAME node hash the tree commits.
pub fn cap_node(l: BabyBear, r: BabyBear) -> BabyBear {
    cap_chip_absorb(&[BabyBear::new(CAP_FACT_MARK), l, r])
}

/// The number of felts in a native cap-tree digest (Phase H-CAP-8: the cap tree is
/// 8-felt, faithful to the FRI ~124-bit soundness floor, no longer the lossy 1-felt
/// `cap_node`). A leaf / node / root is `[BabyBear; CAP_DIGEST_W]`.
pub const CAP_DIGEST_W: usize = 8;

/// The all-zero 8-felt digest — the PADDING / empty-leaf marker (the 8-felt twin of the
/// `BabyBear::ZERO` the 1-felt tree padded with). `EMPTY_SUBTREE_ROOTS[0]` and every
/// tombstone-ghost digest is this.
pub const CAP_ZERO8: [BabyBear; CAP_DIGEST_W] = [BabyBear::ZERO; CAP_DIGEST_W];

/// **`cap_node8`** — the native 8-felt cap-tree internal node: the arity-16 `node8` chip
/// compression `perm(L8 ‖ R8)[0..8]` (`descriptor_ir2::chip_absorb_all_lanes` at
/// `CHIP_NODE8_ARITY = 16`). Replaces the lossy 1-felt `cap_node` for the canonical cap tree;
/// EQUALITY-binds all 8 output lanes to both 8-felt children, so the per-node collision floor is
/// full 8-felt width (~124-bit), matching the deployed FRI/STARK soundness.
///
/// PUBLIC so the cap-open trace scaffold (`effect_vm::trace_rotated`) fills its per-level
/// `cur8/sib8/node8` columns from the SAME compression the cap-tree commits.
pub fn cap_node8(
    l: [BabyBear; CAP_DIGEST_W],
    r: [BabyBear; CAP_DIGEST_W],
) -> [BabyBear; CAP_DIGEST_W] {
    let mut ins = [BabyBear::ZERO; 16];
    ins[..CAP_DIGEST_W].copy_from_slice(&l);
    ins[CAP_DIGEST_W..].copy_from_slice(&r);
    crate::descriptor_ir2::chip_absorb_all_lanes(crate::descriptor_ir2::CHIP_NODE8_ARITY, &ins)
}

/// Tree depth for the canonical capability tree. A binary tree of depth 16
/// holds `2^16 - 2 = 65534` capabilities (two positions reserved for the
/// MIN/MAX sentinels). Chosen large enough that a c-list never re-rotates
/// the tree in practice.
pub const CAP_TREE_DEPTH: usize = 16;

/// The precomputed **empty-subtree roots** for the canonical capability tree at
/// every level `0..=CAP_TREE_DEPTH`. `EMPTY_SUBTREE_ROOTS[0]` is the empty-leaf
/// digest (`BabyBear::ZERO`, the padding marker [`CanonicalCapTree::new`] uses);
/// `EMPTY_SUBTREE_ROOTS[k]` is `cap_node8(empty[k-1], empty[k-1])` — the root a
/// node whose entire subtree is padding folds to.
///
/// These are the values the DENSE build placed at any node covering only
/// padding positions. The sparse fold reads them in place of folding 65k zeros,
/// and a membership path whose sibling subtree is all-padding reports the same
/// constant the dense build would — so roots and witnesses stay byte-identical.
static EMPTY_SUBTREE_ROOTS: LazyLock<[[BabyBear; CAP_DIGEST_W]; CAP_TREE_DEPTH + 1]> =
    LazyLock::new(|| {
        let mut roots = [CAP_ZERO8; CAP_TREE_DEPTH + 1];
        for level in 1..=CAP_TREE_DEPTH {
            roots[level] = cap_node8(roots[level - 1], roots[level - 1]);
        }
        roots
    });

/// The empty-subtree root at `level` (`0` = the ZERO leaf digest, `depth` = the
/// root of an all-padding tree). Used both by the sparse fold and by
/// `prove_membership` to report all-padding siblings.
fn cap_empty_subtree_root(level: usize) -> [BabyBear; CAP_DIGEST_W] {
    EMPTY_SUBTREE_ROOTS[level]
}

/// Domain-separation tag absorbed into a `slot_hash` so the sort key is a
/// well-distributed Poseidon2 image (not the raw slot integer). Keeps the
/// sorted-tree balanced and gives the key the "hash" character its name
/// implies. The same constant is used cell-side (one implementation).
const SLOT_HASH_TAG: u32 = 0x0CAB_5107; // "cap slot"

/// Sentinel felt encoding `None` for the optional `expiry` / `breadstuff`
/// leaf fields. `BABYBEAR_P - 1` (= [`SENTINEL_MAX`]) cannot be a real folded
/// value collision risk for `expiry` (heights are small) and is a fixed,
/// cell-independent reserved marker, so `Some` vs `None` never alias.
const NONE_SENTINEL: BabyBear = SENTINEL_MAX;

/// The 7 canonical leaf fields for one capability. Each is a single BabyBear
/// felt; the leaf digest is `Poseidon2` of these seven in order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CapLeaf {
    /// The sort key: a Poseidon2 image of the (unique) c-list slot.
    pub slot_hash: BabyBear,
    /// The capability's target cell id, folded to one felt.
    pub target: BabyBear,
    /// The `AuthRequired` tier (+ absorbed vk_hash for `Custom`), one felt.
    pub auth_tag: BabyBear,
    /// `EffectMask` low 16 bits.
    pub mask_lo: BabyBear,
    /// `EffectMask` high 16 bits.
    pub mask_hi: BabyBear,
    /// Optional expiry height (`NONE_SENTINEL` when absent).
    pub expiry: BabyBear,
    /// Optional breadstuff hash folded to one felt (`NONE_SENTINEL` when absent).
    pub breadstuff: BabyBear,
}

impl CapLeaf {
    /// The 7-field Poseidon2 leaf digest, in canonical field order. This is the
    /// value the sorted Merkle tree stores at the leaf position; the leaf is
    /// *placed* by its `slot_hash` ordering.
    pub fn digest(&self) -> [BabyBear; CAP_DIGEST_W] {
        // The SINGLE rate-8 chip absorb of the 7 fields (arity 7), squeezing ALL 8 output
        // lanes (Phase H-CAP-8: native 8-felt leaf digest), byte-identical to the IR-v2
        // Poseidon2 chip's BUS_P2 leaf absorb and the Lean `capLeafDigest8` (= the 8 lanes
        // of `sponge ∘ leafFields`). One in-circuit hash, so the chip realizes the cap-leaf
        // as one row; the 8-felt squeeze is faithful to the FRI ~124-bit floor.
        crate::descriptor_ir2::chip_absorb_all_lanes(
            7,
            &[
                self.slot_hash,
                self.target,
                self.auth_tag,
                self.mask_lo,
                self.mask_hi,
                self.expiry,
                self.breadstuff,
            ],
        )
    }
}

/// Fold 32 bytes into a single BabyBear felt: `hash_many` over the 8 4-byte
/// little-endian limbs (`BabyBear::encode_hash`). Used for `target` and
/// `breadstuff`. The fold is collision-resistant under the Poseidon2 sponge
/// (up to the per-limb mod-p wrap on 4-byte chunks whose raw u32 exceeds `p`,
/// a deterministic total mapping identical for cell and circuit since this is
/// the single shared implementation).
pub fn fold_bytes32(bytes: &[u8; 32]) -> BabyBear {
    hash_many(&BabyBear::encode_hash(bytes))
}

/// The canonical `slot_hash` key for a c-list slot: a domain-separated
/// Poseidon2 image of the slot integer. Injective in practice for the slot
/// range a c-list uses (the executor enforces slot uniqueness).
pub fn slot_hash(slot: u32) -> BabyBear {
    hash_many(&[BabyBear::new(SLOT_HASH_TAG), BabyBear::new(slot)])
}

/// Encode an `EffectMask` (u32) into its low-16 / high-16 limbs.
pub fn split_effect_mask(mask: u32) -> (BabyBear, BabyBear) {
    (
        BabyBear::new(mask & 0xFFFF),
        BabyBear::new((mask >> 16) & 0xFFFF),
    )
}

/// Encode an optional expiry height into one felt: `Some(h)` folds the full
/// 64-bit height through `hash_many` (binding all 64 bits), `None` is the
/// reserved [`NONE_SENTINEL`].
pub fn encode_expiry(expiry: Option<u64>) -> BabyBear {
    match expiry {
        Some(h) => hash_many(&[BabyBear::new(h as u32), BabyBear::new((h >> 32) as u32)]),
        None => NONE_SENTINEL,
    }
}

/// Encode an optional breadstuff hash into one felt: `Some(b)` folds the 32
/// bytes via [`fold_bytes32`], `None` is the reserved [`NONE_SENTINEL`].
pub fn encode_breadstuff(breadstuff: Option<&[u8; 32]>) -> BabyBear {
    match breadstuff {
        Some(b) => fold_bytes32(b),
        None => NONE_SENTINEL,
    }
}

/// The sentinel leaf for a given sort key (MIN or MAX). All non-key fields are
/// zero; the sentinel exists only to bracket the sorted key range so a
/// Phase-B non-membership proof can place an absent key between two adjacent
/// present keys.
fn sentinel_leaf(key: BabyBear) -> CapLeaf {
    CapLeaf {
        slot_hash: key,
        target: BabyBear::ZERO,
        auth_tag: BabyBear::ZERO,
        mask_lo: BabyBear::ZERO,
        mask_hi: BabyBear::ZERO,
        expiry: BabyBear::ZERO,
        breadstuff: BabyBear::ZERO,
    }
}

/// The canonical capability tree: a sorted binary Poseidon2 Merkle tree over
/// the c-list leaves, keyed by `slot_hash` and sentinel-bracketed. Mirrors
/// [`crate::dsl::revocation::DslRevocationTree`] (sorted, sentinel-bracketed,
/// `hash_fact` nodes) but stores the 7-field capability leaf at each position.
#[derive(Clone, Debug)]
pub struct CanonicalCapTree {
    /// All levels, bottom-up, stored **sparsely** as the non-empty PREFIX of
    /// each level. `levels[k]` holds exactly the real-bearing nodes at level `k`
    /// (positions `0..levels[k].len()`); every node at an index `>= levels[k].len()`
    /// covers only padding and equals [`cap_empty_subtree_root`]`(k)`.
    ///
    /// The real leaves are placed contiguously at the start of the bottom level
    /// (sorted, then padded), so each level's non-empty nodes are themselves a
    /// contiguous prefix — this prefix is all the dense build ever computed to a
    /// non-empty value. `node(level, idx)` reconstructs any position byte-
    /// identically to the old dense `levels[level][idx]`.
    levels: Vec<Vec<[BabyBear; CAP_DIGEST_W]>>,
    /// The leaves in sorted-by-`slot_hash` order, including sentinels (before
    /// padding). Retained for Phase-B membership / non-membership witnessing.
    sorted_leaves: Vec<CapLeaf>,
    /// Tree depth.
    depth: usize,
}

impl CanonicalCapTree {
    /// Build the canonical capability tree from a cell's c-list leaves.
    ///
    /// Sorts the leaves by `slot_hash`, brackets with the MIN/MAX sentinels,
    /// deduplicates by key (the executor enforces slot uniqueness, so this is
    /// belt-and-suspenders), then builds the padded binary tree.
    pub fn new(leaves: Vec<CapLeaf>, depth: usize) -> Self {
        Self::new_with_tombstones(leaves, &[], depth)
    }

    /// Build the canonical capability tree from a cell's LIVE c-list leaves plus
    /// a set of TOMBSTONED slot keys (the `slot_hash`es of revoked slots).
    ///
    /// ## Tombstone semantics (the cap-crown revoke reconciliation)
    ///
    /// A revoke does NOT compact (re-index) the sorted tree — it leaves the
    /// revoked slot's POSITION occupied by the `BabyBear::ZERO` padding leaf,
    /// so every OTHER capability's membership witness stays valid across an
    /// unrelated revoke. This is the EXACT semantics
    /// [`Self::revocation_witness`] realizes (membership-open the held leaf, then
    /// fold `BabyBear::ZERO` up the SAME sibling path) and the in-circuit
    /// sel-24 revoke gate enforces.
    ///
    /// A tombstone is modeled as a "ghost leaf": it keeps the revoked slot's
    /// `slot_hash` as its SORT KEY (so it occupies the same sorted position the
    /// live leaf held — positions do NOT shift) but contributes a ZERO leaf
    /// DIGEST (the same value [`Self::new`] pads empty positions with). So
    /// building this tree from `[remaining live leaves] + [tombstone ghosts]`
    /// yields the byte-identical root to revoking each tombstoned slot from the
    /// live tree one at a time via the zero-fold witness. (The
    /// `cell_cap_root == circuit_cap_root` revoke differential pins this.)
    ///
    /// Tombstone keys that collide with a live leaf's key are ignored for that
    /// key (a live leaf shadows a stale tombstone — re-granting the same slot
    /// resurrects it). Tombstone keys are deduplicated.
    pub fn new_with_tombstones(
        mut leaves: Vec<CapLeaf>,
        tombstone_keys: &[BabyBear],
        depth: usize,
    ) -> Self {
        leaves.push(sentinel_leaf(SENTINEL_MIN));
        leaves.push(sentinel_leaf(SENTINEL_MAX));
        // Sort by the canonical sort key (slot_hash). Deterministic, total.
        leaves.sort_by_key(|l| l.slot_hash.as_u32());
        leaves.dedup_by_key(|l| l.slot_hash.as_u32());

        // A tombstone is a GHOST leaf: a sentinel-style `CapLeaf` keyed at the
        // revoked slot's `slot_hash` (so it occupies that sorted POSITION) but
        // whose stored leaf DIGEST is forced to `BabyBear::ZERO` (the padding
        // value `new` uses for empty positions). We keep `sorted_leaves` and the
        // `levels[0]` digest array INDEX-ALIGNED — both built from the SAME
        // sorted `(leaf, digest)` order — so `position_of` / `prove_membership`
        // remain consistent on a tombstoned tree (a survivor's membership path
        // still opens to the post-revoke root).
        //
        // A tombstone whose key already names a live leaf is dropped (live
        // shadows tombstone); tombstone keys are deduplicated. So after the
        // merge the keys are still unique.
        let live_keys: std::collections::HashSet<u32> =
            leaves.iter().map(|l| l.slot_hash.as_u32()).collect();
        // (leaf, digest) pairs: live leaves carry their real digest; ghosts
        // carry ZERO. `sorted_leaves` stores the leaf, `levels[0]` the digest.
        let mut keyed: Vec<(CapLeaf, [BabyBear; CAP_DIGEST_W])> =
            leaves.into_iter().map(|l| (l, l.digest())).collect();
        let mut seen_tomb: std::collections::HashSet<u32> = std::collections::HashSet::new();
        for &k in tombstone_keys {
            let ku = k.as_u32();
            if live_keys.contains(&ku) || !seen_tomb.insert(ku) {
                continue;
            }
            // Ghost: keyed at `k`, all other fields zero, stored digest ZERO.
            keyed.push((sentinel_leaf(k), CAP_ZERO8));
        }
        // Re-sort by key so the ghost positions interleave with the live leaves
        // exactly where their `slot_hash` orders (positions do not shift).
        keyed.sort_by_key(|(l, _)| l.slot_hash.as_u32());

        let capacity = 1usize << depth;
        // The c-list (live + tombstones, incl. the two sentinels) must fit. A
        // c-list this large never occurs in practice; fail loudly rather than
        // silently truncate.
        assert!(
            keyed.len() <= capacity,
            "capability c-list ({} entries incl. sentinels + tombstones) exceeds tree capacity 2^{depth}",
            keyed.len()
        );

        let sorted_leaves: Vec<CapLeaf> = keyed.iter().map(|(l, _)| *l).collect();
        // The real leaf digests (positions `0..n`); every position `>= n` is the
        // ZERO padding leaf the dense build `resize`d in. We never materialize
        // those zeros — the sparse fold folds only this prefix against the
        // precomputed empty-subtree roots.
        let leaf_digests: Vec<[BabyBear; CAP_DIGEST_W]> = keyed.iter().map(|(_, d)| *d).collect();
        debug_assert!(leaf_digests.len() <= capacity);

        // Fold ONLY the non-empty prefix at each level. A parent at index `i`
        // (level `k+1`) covers children `2i`, `2i+1` at level `k`; a child index
        // outside the stored prefix is the empty-subtree root `empty[k]`. The
        // non-empty prefix at level `k+1` is `ceil(prev_len / 2)` — a parent is
        // non-empty iff it has at least one non-empty child, and the non-empty
        // children form a `0..prev_len` prefix, so the non-empty parents form a
        // `0..ceil(prev_len/2)` prefix. This is O(n·depth) node hashes for `n`
        // real leaves, not the dense `2^depth - 1`.
        let mut levels: Vec<Vec<[BabyBear; CAP_DIGEST_W]>> = Vec::with_capacity(depth + 1);
        levels.push(leaf_digests);
        for level in 0..depth {
            let prev = levels.last().unwrap();
            let prev_len = prev.len();
            let next_len = prev_len.div_ceil(2);
            let mut next_level = Vec::with_capacity(next_len);
            for i in 0..next_len {
                let l = prev[2 * i];
                // The right child may fall outside the stored prefix (odd
                // boundary) — then it is the all-padding empty-subtree root.
                let r = prev
                    .get(2 * i + 1)
                    .copied()
                    .unwrap_or_else(|| cap_empty_subtree_root(level));
                next_level.push(cap_node8(l, r));
            }
            levels.push(next_level);
        }

        Self {
            levels,
            sorted_leaves,
            depth,
        }
    }

    /// The value at `(level, idx)`, reconstructing the dense node byte-
    /// identically: the stored prefix value if `idx` is within it, else the
    /// precomputed empty-subtree root for `level` (an all-padding node).
    fn node(&self, level: usize, idx: usize) -> [BabyBear; CAP_DIGEST_W] {
        self.levels[level]
            .get(idx)
            .copied()
            .unwrap_or_else(|| cap_empty_subtree_root(level))
    }

    /// The Merkle root. `levels[depth]` always holds exactly the single root
    /// node (the prefix length at the top is `ceil(n / 2^depth) == 1` for any
    /// `2 <= n <= 2^depth`, since the two sentinels are always present).
    pub fn root(&self) -> [BabyBear; CAP_DIGEST_W] {
        self.node(self.depth, 0)
    }

    /// The sorted leaves (including sentinels). For Phase-B witnessing.
    pub fn sorted_leaves(&self) -> &[CapLeaf] {
        &self.sorted_leaves
    }

    /// Number of real (non-sentinel, non-tombstone) capabilities.
    ///
    /// A TOMBSTONE ghost (a revoked slot's position, stored digest
    /// `BabyBear::ZERO`) is NOT a live capability, so it is excluded — both the
    /// MIN/MAX sentinels (by key) and any ghost position (by its ZERO leaf
    /// digest in `levels[0]`) are filtered out.
    pub fn num_caps(&self) -> usize {
        self.sorted_leaves
            .iter()
            .enumerate()
            .filter(|(i, l)| {
                l.slot_hash != SENTINEL_MIN
                    && l.slot_hash != SENTINEL_MAX
                    // A ghost (tombstone) position carries a ZERO leaf digest.
                    && self.node(0, *i) != CAP_ZERO8
            })
            .count()
    }

    /// The tree depth.
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// All level vectors, bottom-up, stored SPARSELY: `levels[k]` is the
    /// non-empty PREFIX of level `k` (positions `0..levels[k].len()`); any node
    /// at index `>= levels[k].len()` is the all-padding [`cap_empty_subtree_root`]`(k)`.
    /// `levels[0]` is the real (unpadded) leaf-digest prefix; `levels[depth]` is
    /// `[root]`. Exposed for Phase-B membership witnessing.
    pub fn levels(&self) -> &[Vec<[BabyBear; CAP_DIGEST_W]>] {
        &self.levels
    }

    /// The leaf-array position (0-based, in the padded bottom level) of the
    /// leaf whose `slot_hash == key`, or `None` if no such (non-padding) leaf
    /// exists. The sorted-tree placement is by `slot_hash` ordering, so this
    /// is the canonical position the membership path opens.
    pub fn position_of(&self, key: BabyBear) -> Option<usize> {
        // `sorted_leaves` is ordered by `slot_hash.as_u32()`. Binary-search for
        // the first leaf with that key (O(log n)); returns its index only on an
        // exact hit — identical to the former first-match linear scan.
        let needle = key.as_u32();
        let i = self
            .sorted_leaves
            .partition_point(|l| l.slot_hash.as_u32() < needle);
        if i < self.sorted_leaves.len() && self.sorted_leaves[i].slot_hash.as_u32() == needle {
            Some(i)
        } else {
            None
        }
    }

    /// Generate a Merkle **membership** path for the leaf at the given padded
    /// position: `(siblings, directions)` where `directions[i] == 0` if the
    /// current node is the LEFT child at level `i` (sibling on the right), `1`
    /// otherwise. Mirrors [`crate::dsl::revocation::DslRevocationTree::prove_membership`].
    pub fn prove_membership(
        &self,
        position: usize,
    ) -> Option<(Vec<[BabyBear; CAP_DIGEST_W]>, Vec<u8>)> {
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

/// A Phase-B capability membership + leaf-replacement witness for the
/// AttenuateCapability AIR row. It authenticates the HELD leaf against the old
/// `cap_root` (the seeded sorted tree) AND carries the narrowed GRANTED leaf so
/// the AIR can recompute `new_cap_root` over the SAME sibling path — a genuine
/// sorted-tree leaf-update, not a pinned digest.
///
/// Because the tree is sorted by `slot_hash` and the slot is held FIXED across
/// an attenuation (only the rights narrow), the held and granted leaves occupy
/// the SAME position and share the SAME sibling path; the only difference is the
/// leaf digest. So one set of siblings authenticates both roots.
#[derive(Clone, Debug)]
pub struct CapAttenuationWitness {
    /// The HELD (pre-attenuation) leaf — the real committed rights.
    pub held: CapLeaf,
    /// The GRANTED (post-attenuation, narrowed) leaf — same slot/target/breadstuff,
    /// narrowed auth_tag/mask/expiry.
    pub granted: CapLeaf,
    /// Sibling digests along the path from the leaf to the root (bottom-up).
    pub siblings: Vec<[BabyBear; CAP_DIGEST_W]>,
    /// Direction bits along the path (0 = current is left child, 1 = right).
    pub directions: Vec<u8>,
    /// The authenticated old root (= the held leaf's path top).
    pub old_root: [BabyBear; CAP_DIGEST_W],
    /// The recomputed new root (= the granted leaf's path top, same siblings).
    pub new_root: [BabyBear; CAP_DIGEST_W],
}

impl CanonicalCapTree {
    /// Build a [`CapAttenuationWitness`] that narrows the leaf at `held.slot_hash`
    /// to the `granted` leaf. Returns `None` if no leaf with that slot is present
    /// (a fabricated held leaf has no authenticated position). The returned
    /// `old_root` equals this tree's root; `new_root` is the root after the
    /// single-leaf replacement (recomputed over the shared sibling path).
    pub fn attenuation_witness(&self, granted: CapLeaf) -> Option<CapAttenuationWitness> {
        let pos = self.position_of(granted.slot_hash)?;
        let held = self.sorted_leaves[pos];
        let (siblings, directions) = self.prove_membership(pos)?;

        // Recompute the new root over the SAME siblings with the granted leaf
        // digest swapped in at the leaf position.
        let mut cur = granted.digest();
        for level in 0..self.depth {
            let sib = siblings[level];
            cur = if directions[level] == 0 {
                cap_node8(cur, sib)
            } else {
                cap_node8(sib, cur)
            };
        }
        Some(CapAttenuationWitness {
            held,
            granted,
            siblings,
            directions,
            old_root: self.root(),
            new_root: cur,
        })
    }

    /// Build a **Phase B revocation** witness: membership-open the held leaf at
    /// `held_key` (its `slot_hash`) in THIS tree, then recompute `new_root` by
    /// folding the ZERO/padding leaf (the empty-position marker) up the SAME
    /// sibling path — a genuine sorted-tree leaf DELETION (the slot collapses to
    /// the padding leaf), not a pinned digest. This is the one-variant
    /// simplification of [`Self::attenuation_witness`]: revoke does NOT install a
    /// narrowed leaf (no rights logic), it removes the slot, so the new leaf
    /// digest is `BabyBear::ZERO` (the same value `CanonicalCapTree::new` pads
    /// empty positions with). Returns `None` if no leaf with `held_key` is
    /// present (a fabricated held leaf has no authenticated position — Forgery 3
    /// for revoke).
    ///
    /// The returned `granted` field carries the SENTINEL/zero CapLeaf at the
    /// revoked slot purely as a placeholder; the load-bearing output is
    /// `new_root` (the ZERO-folded path top). `held` is the genuine committed
    /// leaf the membership opens.
    pub fn revocation_witness(&self, held_key: BabyBear) -> Option<CapAttenuationWitness> {
        let pos = self.position_of(held_key)?;
        let held = self.sorted_leaves[pos];
        let (siblings, directions) = self.prove_membership(pos)?;

        // Recompute the new root over the SAME siblings with the ZERO padding
        // leaf swapped in at the revoked position (the slot is deleted; the
        // position becomes an empty/padding leaf, digest `BabyBear::ZERO`).
        let mut cur = CAP_ZERO8;
        for level in 0..self.depth {
            let sib = siblings[level];
            cur = if directions[level] == 0 {
                cap_node8(cur, sib)
            } else {
                cap_node8(sib, cur)
            };
        }
        Some(CapAttenuationWitness {
            held,
            // Placeholder: the revoked position carries the zero/padding leaf.
            granted: sentinel_leaf(BabyBear::ZERO),
            siblings,
            directions,
            old_root: self.root(),
            new_root: cur,
        })
    }

    /// Build a **Phase B2 delegation** witness: membership-open the GRANTER's
    /// held leaf at `held_key` (its `slot_hash`) in THIS tree (the granter's
    /// c-list), carrying the `granted` leaf that lands in the RECIPIENT's
    /// c-list. Unlike [`Self::attenuation_witness`], the granted leaf has its
    /// OWN `slot_hash` (the recipient's new slot) and `breadstuff`, and the
    /// granter's tree is UNCHANGED by the delegation — so `new_root ==
    /// old_root` (the granter row's cap_root passes through). Returns `None`
    /// if no leaf with `held_key` is present (a fabricated held leaf has no
    /// authenticated position).
    pub fn delegation_witness(
        &self,
        held_key: BabyBear,
        granted: CapLeaf,
    ) -> Option<CapAttenuationWitness> {
        let pos = self.position_of(held_key)?;
        let held = self.sorted_leaves[pos];
        let (siblings, directions) = self.prove_membership(pos)?;
        Some(CapAttenuationWitness {
            held,
            granted,
            siblings,
            directions,
            old_root: self.root(),
            new_root: self.root(),
        })
    }
}

/// A **sorted-tree INSERT witness** for a FRESH capability edge — the cap-tree
/// twin of [`crate::heap_root::CanonicalHeapTree8::insert_witness`], over the
/// arity-7 [`CapLeaf`] / 8-felt [`cap_node8`] canonical tree. Carries:
///   * the NON-MEMBERSHIP bracket of the fresh key in the BEFORE tree — the
///     `pred`/`succ` neighbor leaves (`pred.slot_hash < key < succ.slot_hash`,
///     adjacent in the sorted BEFORE tree; the sentinels guarantee both exist) —
///     the Rust realization of the Lean `SortedTreeNonMembership.GapOpen`
///     carrier `CapInsertEmit.effCapInsertV3_forces_write8` consumes;
///   * the spliced leaf's MEMBERSHIP path in the REBUILT AFTER tree
///     (`siblings`/`directions`/`new_root`) — the trace-forced part (b) of the
///     honest insert (the cap-open appendix the deployed `effCapInsertV3`
///     welds to the committed AFTER cap-root group);
///   * the BEFORE/AFTER 8-felt roots.
///
/// The AFTER tree is the full sorted REBUILD over `[live BEFORE leaves] +
/// [new_leaf]` with the BEFORE tombstones preserved — byte-identical to what
/// `dregg-cell` commits after the grant (`compute_capability_root_with_tombstones`).
#[derive(Clone, Debug)]
pub struct CapInsertWitness {
    /// The inserted (spliced) 7-field leaf.
    pub new_leaf: CapLeaf,
    /// The PREDECESSOR bracket leaf (greatest BEFORE key `< new_leaf.slot_hash`).
    pub pred: CapLeaf,
    /// The SUCCESSOR bracket leaf (least BEFORE key `> new_leaf.slot_hash`).
    pub succ: CapLeaf,
    /// The spliced leaf's membership path in the AFTER tree (8-felt siblings, bottom-up).
    pub siblings: Vec<[BabyBear; CAP_DIGEST_W]>,
    /// Direction bits for the AFTER path (0 = current is LEFT child).
    pub directions: Vec<u8>,
    /// The authenticated BEFORE 8-felt cap-root.
    pub old_root: [BabyBear; CAP_DIGEST_W],
    /// The recomposed AFTER 8-felt cap-root (the rebuilt tree's root).
    pub new_root: [BabyBear; CAP_DIGEST_W],
}

/// A **sorted-tree REMOVE witness** — the deployed TOMBSTONE remove (the revoked
/// slot's position collapses to the ZERO/padding digest; positions do NOT shift,
/// matching [`CanonicalCapTree::new_with_tombstones`] / the cell-side
/// `compute_capability_root_with_tombstones` byte-for-byte). Carries:
///   * the removed leaf's MEMBERSHIP path in the BEFORE tree — the trace-forced
///     part (a) of the honest remove (the cap-open appendix the deployed
///     `effCapRemoveV3` welds to the committed BEFORE cap-root group);
///   * the AFTER 8-felt root — the ZERO leaf folded up the SAME sibling path
///     (the removed key's non-membership in AFTER rides the same bracket
///     neighbors, now adjacent).
#[derive(Clone, Debug)]
pub struct CapRemoveWitness {
    /// The removed (genuine, committed) 7-field leaf.
    pub removed: CapLeaf,
    /// The removed leaf's membership path in the BEFORE tree (8-felt siblings, bottom-up).
    pub siblings: Vec<[BabyBear; CAP_DIGEST_W]>,
    /// Direction bits (0 = current is LEFT child).
    pub directions: Vec<u8>,
    /// The authenticated BEFORE 8-felt cap-root.
    pub old_root: [BabyBear; CAP_DIGEST_W],
    /// The recomposed AFTER 8-felt cap-root (the ZERO-fold tombstone top).
    pub new_root: [BabyBear; CAP_DIGEST_W],
}

impl CanonicalCapTree {
    /// The LIVE (non-sentinel, non-tombstone) leaves + the tombstoned keys of
    /// THIS tree — the `(live, tombstones)` pair `new_with_tombstones` rebuilds
    /// byte-identically from. A ghost position is recognized by its ZERO stored
    /// digest (exactly as [`Self::num_caps`] filters).
    fn live_and_tombstones(&self) -> (Vec<CapLeaf>, Vec<BabyBear>) {
        let mut live = Vec::new();
        let mut tombs = Vec::new();
        for (i, l) in self.sorted_leaves.iter().enumerate() {
            if l.slot_hash == SENTINEL_MIN || l.slot_hash == SENTINEL_MAX {
                continue;
            }
            if self.node(0, i) == CAP_ZERO8 {
                tombs.push(l.slot_hash);
            } else {
                live.push(*l);
            }
        }
        (live, tombs)
    }

    /// Build a [`CapInsertWitness`] splicing `new_leaf` (a FRESH key) into this
    /// tree. Fails closed (`None`) when the key is a sentinel / sentinel-range
    /// collision or ALREADY PRESENT (live or tombstoned — the sorted insert
    /// refuses an occupied position; re-granting a tombstoned slot is the
    /// resurrect path, not a fresh splice). The AFTER tree is the full sorted
    /// rebuild (`new_with_tombstones` over live + new, tombstones preserved),
    /// so `new_root` matches the cell-side post-grant root byte-for-byte and
    /// `siblings`/`directions` open the spliced leaf against it.
    pub fn insert_witness(&self, new_leaf: CapLeaf) -> Option<CapInsertWitness> {
        let key = new_leaf.slot_hash;
        if key.as_u32() <= SENTINEL_MIN.as_u32() || key.as_u32() >= SENTINEL_MAX.as_u32() {
            return None;
        }
        if self.position_of(key).is_some() {
            return None; // present (live or ghost) — no fresh splice (fail closed).
        }
        // The non-membership bracket: the sentinels guarantee a strict predecessor
        // and successor exist in the sorted BEFORE leaves.
        let succ_pos = self
            .sorted_leaves
            .partition_point(|l| l.slot_hash.as_u32() <= key.as_u32());
        if succ_pos == self.sorted_leaves.len() {
            return None;
        }
        if succ_pos == 0 {
            return None; // unreachable (MIN sentinel sorts first) — defensive.
        }
        let pred = self.sorted_leaves[succ_pos - 1];
        let succ = self.sorted_leaves[succ_pos];
        debug_assert!(pred.slot_hash.as_u32() < key.as_u32());
        debug_assert!(key.as_u32() < succ.slot_hash.as_u32());
        // The AFTER tree: the full sorted rebuild with the fresh leaf spliced in
        // (tombstones preserved — cell-side byte-identity).
        let (mut live, tombs) = self.live_and_tombstones();
        live.push(new_leaf);
        let after = CanonicalCapTree::new_with_tombstones(live, &tombs, self.depth);
        let pos = after.position_of(key)?;
        let (siblings, directions) = after.prove_membership(pos)?;
        debug_assert_eq!(
            recompose_membership(new_leaf.digest(), &siblings, &directions),
            after.root(),
            "cap insert witness: the spliced leaf's AFTER path must recompose the rebuilt root"
        );
        Some(CapInsertWitness {
            new_leaf,
            pred,
            succ,
            siblings,
            directions,
            old_root: self.root(),
            new_root: after.root(),
        })
    }

    /// Build a [`CapRemoveWitness`] tombstoning the leaf at `key`. Fails closed
    /// (`None`) when no LIVE leaf with that key is present (a fabricated removed
    /// leaf has no authenticated position; a sentinel/ghost cannot be removed).
    /// The AFTER root is the ZERO/padding leaf folded up the SAME sibling path —
    /// the deployed tombstone semantics ([`Self::revocation_witness`] /
    /// `new_with_tombstones`), byte-identical to the cell-side post-revoke root.
    pub fn remove_witness(&self, key: BabyBear) -> Option<CapRemoveWitness> {
        if key == SENTINEL_MIN || key == SENTINEL_MAX {
            return None;
        }
        let pos = self.position_of(key)?;
        if self.node(0, pos) == CAP_ZERO8 {
            return None; // already a ghost — nothing live to remove (fail closed).
        }
        let removed = self.sorted_leaves[pos];
        let (siblings, directions) = self.prove_membership(pos)?;
        debug_assert_eq!(
            recompose_membership(removed.digest(), &siblings, &directions),
            self.root(),
            "cap remove witness: the removed leaf's BEFORE path must recompose this root"
        );
        // The tombstone zero-fold: the AFTER root over the SAME path.
        let new_root = recompose_membership(CAP_ZERO8, &siblings, &directions);
        Some(CapRemoveWitness {
            removed,
            siblings,
            directions,
            old_root: self.root(),
            new_root,
        })
    }
}

/// Compute the canonical capability root over a set of leaves at the canonical
/// depth ([`CAP_TREE_DEPTH`]). This is THE function `dregg-cell` calls; the
/// circuit seeds its `cap_root` column from this same value.
///
/// Returns [`Faithful8`] — a genuine `node8` tree root, one of the named
/// faithful constructors of the commitment TYPE WALL
/// (`docs/FAITHFUL-COMMITMENT-LAW.md`).
pub fn compute_capability_root(leaves: Vec<CapLeaf>) -> Faithful8 {
    Faithful8::from_root8(CanonicalCapTree::new(leaves, CAP_TREE_DEPTH).root())
}

/// Compute the canonical capability root over a set of LIVE leaves plus a set
/// of TOMBSTONED slot keys (revoked slots' `slot_hash`es), at the canonical
/// depth ([`CAP_TREE_DEPTH`]). This is the function `dregg-cell` calls once a
/// cell has revoked any capability: the revoked slot's position stays occupied
/// by the ZERO/padding leaf (tombstone), matching the in-circuit sel-24 revoke
/// gate's zero-fold deletion byte-for-byte. See
/// [`CanonicalCapTree::new_with_tombstones`].
pub fn compute_capability_root_with_tombstones(
    leaves: Vec<CapLeaf>,
    tombstone_keys: &[BabyBear],
) -> Faithful8 {
    Faithful8::from_root8(
        CanonicalCapTree::new_with_tombstones(leaves, tombstone_keys, CAP_TREE_DEPTH).root(),
    )
}

/// The canonical capability root of the EMPTY c-list (only the two sentinels).
/// This is the value `CellState::new` seeds `cap_root` with, and the value a
/// fresh cell's `compute_canonical_capability_root` returns. Deterministic and
/// cell-independent.
pub fn empty_capability_root() -> Faithful8 {
    compute_capability_root(Vec::new())
}

/// The EMPTY record digest — the cell-independent constant a cell with no
/// authority residue beyond its carried (balance/nonce/fields/cap_root) limbs
/// uses for the EffectVM `CellState::record_digest`. Absorbed as the fourth
/// input of the state-commitment root hash, it is a uniform no-op for such cells
/// (structurally mirroring the Lean `emptySystemRootsDigest` / `legacyReferenceCommitS`
/// no-op fold). A real cell carries `dregg_cell::compute_authority_digest_felt(&cell)`.
///
/// It is `ZERO` so that the new full-state commitment is byte-identical to the
/// OLD lossy `hash_4_to_1(inter1, inter2, inter3, ZERO)` for a residue-free cell —
/// the flag-day-free no-op cutover. Cells carrying real authority residue get a
/// different (binding) fourth limb.
pub fn empty_record_digest() -> BabyBear {
    BabyBear::ZERO
}

/// A **cap-membership opening witness** for the IN-CIRCUIT authority leg: the
/// genuine 7-field [`CapLeaf`] plus the depth-16 `(sibling, direction)` path that
/// recomposes the committed `cap_root` from the leaf digest. This is the witness
/// the `CapMembership` AIR consumes (and the value `full_turn_proof.rs` must pass
/// in place of the `&[]` placeholder for a cap turn).
///
/// It is the Rust twin of the Lean `DeployedCapOpen.CapOpenCols` witness
/// (`metatheory/Dregg2/Circuit/DeployedCapOpen.lean`): the AIR absorbs the 7 leaf
/// fields into `leaf_digest` (= [`CapLeaf::digest`] = Lean `capLeafDigest`), folds
/// up the path via [`recompose_membership`] (= Lean `recomposeUp`, `hash_fact`
/// nodes mixed by the direction bit), and constrains the top `== cap_root`.
#[derive(Clone, Debug)]
pub struct CapMembershipWitness {
    /// The opened (genuine, held) leaf — its 7 fields ride the chip absorb.
    pub leaf: CapLeaf,
    /// Sibling digests along the path from the leaf to the root (bottom-up).
    pub siblings: Vec<[BabyBear; CAP_DIGEST_W]>,
    /// Direction bits (0 = current is LEFT child at this level, 1 = right).
    pub directions: Vec<u8>,
    /// The committed cap-tree root the path recomposes to.
    pub root: [BabyBear; CAP_DIGEST_W],
}

/// **`recompose_membership`** — fold the held leaf's digest up the `(sibling,
/// direction)` path to the root. The Rust twin of the Lean
/// `DeployedCapTree.recomposeUp` / `DeployedCapOpen` per-level fold: at each level,
/// `dir == 0` ⇒ the current node is the LEFT child (`hash_fact(cur, sib)`), else
/// the RIGHT child (`hash_fact(sib, cur)`). This is EXACTLY the per-level `mix`
/// the `descriptor_ir2.rs` Merkle-chain AIR computes (lines ~2109-2135), applied to
/// the 7-field cap leaf rather than the 2-field heap leaf.
pub fn recompose_membership(
    leaf_digest: [BabyBear; CAP_DIGEST_W],
    siblings: &[[BabyBear; CAP_DIGEST_W]],
    directions: &[u8],
) -> [BabyBear; CAP_DIGEST_W] {
    assert_eq!(
        siblings.len(),
        directions.len(),
        "membership path: siblings and directions must have equal length"
    );
    let mut cur = leaf_digest;
    for level in 0..siblings.len() {
        let sib = siblings[level];
        cur = if directions[level] == 0 {
            cap_node8(cur, sib)
        } else {
            cap_node8(sib, cur)
        };
    }
    cur
}

impl CanonicalCapTree {
    /// Build a [`CapMembershipWitness`] that opens the leaf at `slot_hash` (its
    /// sort key) in this tree. Returns `None` if no leaf with that slot is present
    /// (a fabricated leaf has no authenticated position — the in-circuit forgery
    /// guard). The returned witness's path recomposes THIS tree's root from the
    /// genuine held leaf's digest.
    pub fn membership_witness(&self, slot_hash: BabyBear) -> Option<CapMembershipWitness> {
        let pos = self.position_of(slot_hash)?;
        let leaf = self.sorted_leaves[pos];
        let (siblings, directions) = self.prove_membership(pos)?;
        Some(CapMembershipWitness {
            leaf,
            siblings,
            directions,
            root: self.root(),
        })
    }
}

impl CapMembershipWitness {
    /// Check the witness recomposes its committed `root` from the genuine leaf
    /// digest — the soundness contract the AIR's root-pin constraint enforces
    /// (Lean `capOpen_membership`). A fabricated leaf or tampered path fails here.
    pub fn recomposes(&self) -> bool {
        recompose_membership(self.leaf.digest(), &self.siblings, &self.directions) == self.root
    }

    /// The **leaf↔effect binding**: the opened leaf's `target` equals the turn's
    /// `src` cell (folded to a felt). The Rust twin of the Lean `targetBindGate`
    /// (`leaf.target == src`) — authenticate the ACTOR's cap over `src`, not an
    /// arbitrary leaf.
    pub fn target_is(&self, src: BabyBear) -> bool {
        self.leaf.target == src
    }

    /// The write-rights binding: the opened leaf's `mask_lo` admits the write bit
    /// `write_bit` (a submask check `write_bit & mask_lo == write_bit`). The Rust
    /// twin of the Lean `writeMaskGate` (`write ∈ leaf.mask`).
    ///
    /// NB (the deliberate mask-convention reconciliation): the Lean
    /// `DeployedCapTree.confersWriteLeaf` pins `mask_lo == rightsMaskOf(endpoint
    /// [read,write])` over the abstract `Auth`-rights mask, whereas the deployed
    /// `CapLeaf.mask_lo` is the low-16 of an `EffectMask` (cell/facet.rs effect
    /// bitmap). Aligning the two mask conventions (so the in-circuit write bit IS
    /// the deployed `mask_lo`'s write-conferring bit) is the documented flag-day
    /// reconciliation; this checks the submask shape either convention shares.
    pub fn confers_write(&self, write_bit: u32) -> bool {
        (write_bit & self.leaf.mask_lo.as_u32()) == write_bit
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(slot: u32, target_byte: u8, tier: u32, mask: u32) -> CapLeaf {
        let mut tgt = [0u8; 32];
        tgt[0] = target_byte;
        let (mask_lo, mask_hi) = split_effect_mask(mask);
        CapLeaf {
            slot_hash: slot_hash(slot),
            target: fold_bytes32(&tgt),
            auth_tag: BabyBear::new(tier),
            mask_lo,
            mask_hi,
            expiry: encode_expiry(None),
            breadstuff: encode_breadstuff(None),
        }
    }

    /// **INSERT witness (the keystone deploy):** the spliced leaf's AFTER path recomposes the
    /// rebuilt root (byte-identical to the cell-side post-grant root), the non-membership bracket
    /// genuinely brackets the fresh key, and a present / sentinel-colliding key is REFUSED.
    #[test]
    fn insert_witness_recomposes_rebuilt_root_and_brackets() {
        let a = leaf(10, 1, 1, 0x0F);
        let b = leaf(30, 2, 1, 0x0F);
        let tree = CanonicalCapTree::new(vec![a, b], CAP_TREE_DEPTH);
        let fresh = leaf(20, 3, 1, 0x03);
        let w = tree.insert_witness(fresh).expect("fresh key splices");
        // The AFTER path recomposes the FULL sorted rebuild (cell-side byte-identity).
        assert_eq!(
            recompose_membership(fresh.digest(), &w.siblings, &w.directions),
            w.new_root,
            "the spliced leaf's AFTER path recomposes the rebuilt root"
        );
        assert_eq!(
            w.new_root,
            compute_capability_root(vec![a, b, fresh]),
            "the AFTER root IS the cell-side post-grant root"
        );
        assert_eq!(w.old_root, tree.root());
        assert_ne!(
            w.old_root, w.new_root,
            "the insert genuinely moves the root"
        );
        // The non-membership bracket: pred < key < succ, both committed BEFORE members.
        assert!(w.pred.slot_hash.as_u32() < fresh.slot_hash.as_u32());
        assert!(fresh.slot_hash.as_u32() < w.succ.slot_hash.as_u32());
        assert!(tree.position_of(w.pred.slot_hash).is_some());
        assert!(tree.position_of(w.succ.slot_hash).is_some());
        // FAIL CLOSED: a present key / a sentinel key refuses (no fabricated after-root).
        assert!(tree.insert_witness(a).is_none(), "present key refused");
        assert!(
            tree.insert_witness(sentinel_leaf(SENTINEL_MIN)).is_none(),
            "sentinel refused"
        );
    }

    /// **REMOVE witness (the keystone deploy):** the tombstone zero-fold's AFTER root is
    /// byte-identical to the cell-side post-revoke root (`new_with_tombstones`), and an
    /// absent key is REFUSED.
    #[test]
    fn remove_witness_matches_tombstone_root() {
        let a = leaf(10, 1, 1, 0x0F);
        let b = leaf(30, 2, 1, 0x0F);
        let tree = CanonicalCapTree::new(vec![a, b], CAP_TREE_DEPTH);
        let w = tree
            .remove_witness(a.slot_hash)
            .expect("present key removes");
        assert_eq!(w.removed, a);
        assert_eq!(w.old_root, tree.root());
        assert_eq!(
            w.new_root,
            compute_capability_root_with_tombstones(vec![b], &[a.slot_hash]),
            "the tombstone zero-fold root IS the cell-side post-revoke root"
        );
        assert_ne!(
            w.old_root, w.new_root,
            "the remove genuinely moves the root"
        );
        // FAIL CLOSED: an absent key refuses.
        assert!(
            tree.remove_witness(slot_hash(99)).is_none(),
            "absent key refused"
        );
        // A second remove of the SAME (now tombstoned) key refuses too.
        let after = CanonicalCapTree::new_with_tombstones(vec![b], &[a.slot_hash], CAP_TREE_DEPTH);
        assert!(
            after.remove_witness(a.slot_hash).is_none(),
            "a ghost (already-tombstoned) key refused"
        );
    }

    /// The empty root is deterministic and non-zero (the sentinels hash into a
    /// real value, not the all-zero default).
    #[test]
    fn empty_root_deterministic_and_nonzero() {
        let a = empty_capability_root();
        let b = empty_capability_root();
        assert_eq!(a, b, "empty root is deterministic");
        assert_ne!(
            a, CAP_ZERO8,
            "empty root is NOT the ZERO default (the disjoint-seed bug)"
        );
    }

    /// Adding a capability moves the root (the commitment is load-bearing).
    #[test]
    fn grant_moves_root() {
        let empty = empty_capability_root();
        let with_one = compute_capability_root(vec![leaf(0, 1, 1, 0xFFFF_FFFF)]);
        assert_ne!(empty, with_one, "a granted capability must move the root");
    }

    /// The root is order-independent in the INPUT (the tree sorts by key), so
    /// the same c-list presented in any order yields the same root.
    #[test]
    fn root_is_input_order_independent() {
        let a = compute_capability_root(vec![
            leaf(0, 1, 1, 0x1),
            leaf(1, 2, 2, 0x2),
            leaf(2, 3, 3, 0x3),
        ]);
        let b = compute_capability_root(vec![
            leaf(2, 3, 3, 0x3),
            leaf(0, 1, 1, 0x1),
            leaf(1, 2, 2, 0x2),
        ]);
        assert_eq!(a, b, "sorted tree: input order must not change the root");
    }

    /// EFFECT_ALL (0xFFFF_FFFF) needs the full 32 bits: a cap with mask
    /// 0xFFFF_FFFF must differ from one with mask 0x0000_FFFF (high limb
    /// distinguishes them). A single 30-bit limb would COLLIDE these.
    #[test]
    fn full_32bit_mask_does_not_collide() {
        let all = compute_capability_root(vec![leaf(0, 1, 1, 0xFFFF_FFFF)]);
        let lo_only = compute_capability_root(vec![leaf(0, 1, 1, 0x0000_FFFF)]);
        assert_ne!(
            all, lo_only,
            "high 16 bits of the mask must bind (no 30-bit truncation)"
        );
        let (lo, hi) = split_effect_mask(0xFFFF_FFFF);
        assert_eq!(lo.as_u32(), 0xFFFF);
        assert_eq!(hi.as_u32(), 0xFFFF);
    }

    /// Two caps differing ONLY in breadstuff must produce different leaves
    /// (breadstuff is included in the leaf).
    #[test]
    fn breadstuff_binds() {
        let mut base = leaf(0, 1, 1, 0x1);
        let mut other = base;
        base.breadstuff = encode_breadstuff(Some(&[7u8; 32]));
        other.breadstuff = encode_breadstuff(Some(&[9u8; 32]));
        assert_ne!(
            base.digest(),
            other.digest(),
            "breadstuff must bind the leaf"
        );
        // And None vs Some differs.
        let none = leaf(0, 1, 1, 0x1);
        assert_ne!(
            none.digest(),
            base.digest(),
            "None vs Some breadstuff must differ"
        );
    }

    /// Distinct auth tiers bind (tier byte participates).
    #[test]
    fn auth_tier_binds() {
        let sig = compute_capability_root(vec![leaf(0, 1, 1, 0x1)]);
        let proof = compute_capability_root(vec![leaf(0, 1, 2, 0x1)]);
        assert_ne!(sig, proof, "auth tier must bind the root");
    }

    /// The revocation witness opens the genuine held leaf and recomputes the new
    /// root as the IN-PLACE zero-fold: the revoked position collapses to the
    /// `BabyBear::ZERO` padding leaf, folded up the SAME sibling path. This is the
    /// TOMBSTONE deletion semantics — it leaves a zero leaf at the position rather
    /// than reindexing the sorted array.
    ///
    /// NB (the cap-crown reconciliation gap, deliberate): this is NOT the same as
    /// `CanonicalCapTree::new(remaining)` (the COMPACTED rebuild the cell currently
    /// does via `CapabilitySet::revoke`'s `retain`), because a sorted,
    /// sentinel-bracketed Merkle tree RE-INDEXES on deletion: removing a key shifts
    /// every key (and the MAX sentinel) that sorts after it, so the compacted root
    /// differs from the in-place tombstone. The in-circuit revoke gate (Rust AIR +
    /// Lean v2 descriptor) enforces the TOMBSTONE semantics; the cell→circuit
    /// reconciliation (cell tombstones-not-compacts, OR the circuit computes the
    /// reindexing deletion) is the documented flag-day step. This test PINS the
    /// tombstone semantics the witness/gate actually realize.
    #[test]
    fn revocation_witness_zero_folds_the_slot_in_place() {
        let revoked = leaf(7, 0x11, 1, 0xFF);
        let other_a = leaf(3, 0x22, 1, 0xFFFF_FFFF);
        let other_b = leaf(42, 0x33, 2, 0x1);
        let tree = CanonicalCapTree::new(vec![revoked, other_a, other_b], CAP_TREE_DEPTH);

        let w = tree
            .revocation_witness(revoked.slot_hash)
            .expect("revoked slot present");
        assert_eq!(w.held, revoked, "membership opens the genuine held leaf");
        assert_eq!(w.old_root, tree.root(), "old_root is the seeded tree root");
        assert_ne!(
            w.new_root, w.old_root,
            "revoking a held slot moves the root"
        );

        // Recompute the in-place tombstone root by hand: fold BabyBear::ZERO up the
        // witnessed path. This is EXACTLY what the witness returns (and what the
        // in-circuit zero-fold gate enforces).
        let mut cur = CAP_ZERO8;
        for level in 0..CAP_TREE_DEPTH {
            cur = if w.directions[level] == 0 {
                cap_node8(cur, w.siblings[level])
            } else {
                cap_node8(w.siblings[level], cur)
            };
        }
        assert_eq!(
            w.new_root, cur,
            "new_root IS the ZERO/padding leaf folded up the held leaf's sibling path"
        );

        // And the witness's siblings genuinely authenticate the held leaf: folding
        // the held leaf digest up the SAME path reproduces old_root.
        let mut hcur = revoked.digest();
        for level in 0..CAP_TREE_DEPTH {
            hcur = if w.directions[level] == 0 {
                cap_node8(hcur, w.siblings[level])
            } else {
                cap_node8(w.siblings[level], hcur)
            };
        }
        assert_eq!(
            hcur, w.old_root,
            "the held leaf folds up the path to old_root"
        );
    }

    /// THE TOMBSTONE EQUIVALENCE (the cell↔circuit revoke reconciliation
    /// keystone): building a fresh tree from the REMAINING live leaves plus the
    /// revoked slot as a TOMBSTONE key yields the byte-identical root to the
    /// `revocation_witness` zero-fold (membership-open the held leaf, fold ZERO
    /// up its sibling path). This is the equivalence the cell-side tombstone
    /// rebuild relies on: the cell drops the revoked leaf from its live c-list
    /// and records the slot key as a tombstone; `compute_capability_root_with_
    /// tombstones` then reproduces the circuit's post-revoke `cap_root` exactly.
    #[test]
    fn tombstone_rebuild_equals_revocation_witness_zero_fold() {
        let revoked = leaf(7, 0x11, 1, 0xFF);
        let other_a = leaf(3, 0x22, 1, 0xFFFF_FFFF);
        let other_b = leaf(42, 0x33, 2, 0x1);
        let live_tree = CanonicalCapTree::new(vec![revoked, other_a, other_b], CAP_TREE_DEPTH);

        // The circuit-truth post-revoke root: the zero-fold deletion witness.
        let w = live_tree
            .revocation_witness(revoked.slot_hash)
            .expect("revoked slot present");
        let witness_root = w.new_root;

        // The cell-side tombstone rebuild: drop the revoked leaf from the live
        // set, record its slot_hash as a tombstone key.
        let tombstone_root =
            compute_capability_root_with_tombstones(vec![other_a, other_b], &[revoked.slot_hash]);

        assert_eq!(
            tombstone_root, witness_root,
            "the tombstone rebuild MUST equal the revocation-witness zero-fold (the cell↔circuit revoke binding)"
        );

        // And it must DIFFER from the compacted rebuild (the pre-cap-crown cell
        // behavior), proving the reconciliation is non-vacuous.
        let compacted_root = CanonicalCapTree::new(vec![other_a, other_b], CAP_TREE_DEPTH).root();
        assert_ne!(
            tombstone_root, compacted_root,
            "tombstone (zero-fold) must DIFFER from the compacted rebuild — the seam the reconciliation closes"
        );
    }

    /// Two tombstones fold two positions to ZERO, still position-stable: revoking
    /// slot 7 then slot 3 from {3,7,42} equals the live set {42} plus tombstones
    /// {3,7}, and equals chaining two `revocation_witness` zero-folds.
    #[test]
    fn two_tombstones_equal_chained_zero_folds() {
        let a = leaf(3, 0x22, 1, 0xFFFF_FFFF);
        let b = leaf(7, 0x11, 1, 0xFF);
        let c = leaf(42, 0x33, 2, 0x1);
        let t0 = CanonicalCapTree::new(vec![a, b, c], CAP_TREE_DEPTH);

        // Chain: revoke 7 (zero-fold), then revoke 3 against the resulting tree.
        // The resulting tree after the first revoke is the live {3,42} + tomb{7}.
        let after_7 =
            CanonicalCapTree::new_with_tombstones(vec![a, c], &[b.slot_hash], CAP_TREE_DEPTH);
        let w3 = after_7
            .revocation_witness(a.slot_hash)
            .expect("slot 3 still present after revoking 7");
        let chained_root = w3.new_root;

        // One-shot: live {42} + tombstones {3,7}.
        let one_shot =
            compute_capability_root_with_tombstones(vec![c], &[a.slot_hash, b.slot_hash]);

        assert_eq!(
            one_shot, chained_root,
            "two tombstones at once == chaining two zero-fold revokes (position stability)"
        );
        // Sanity: t0 root differs (caps were actually present).
        assert_ne!(one_shot, t0.root());
    }

    /// A stale tombstone whose slot is RE-GRANTED is shadowed by the live leaf:
    /// {3,42} live + tombstone{7}, then re-grant 7 ⇒ {3,7,42} live + tomb{7} must
    /// equal the plain live {3,7,42} root (the live leaf resurrects the position).
    #[test]
    fn re_granted_slot_shadows_its_tombstone() {
        let a = leaf(3, 0x22, 1, 0xFFFF_FFFF);
        let b = leaf(7, 0x11, 1, 0xFF);
        let c = leaf(42, 0x33, 2, 0x1);
        let plain = CanonicalCapTree::new(vec![a, b, c], CAP_TREE_DEPTH).root();
        // b's slot is BOTH live and tombstoned: live must shadow the tombstone.
        let shadowed = compute_capability_root_with_tombstones(vec![a, b, c], &[b.slot_hash]);
        assert_eq!(
            shadowed, plain,
            "a live leaf must shadow a stale tombstone for the same slot key"
        );
    }

    /// A fabricated held slot (not in the tree) has no authenticated position:
    /// the revocation witness is `None` (Forgery 3 for revoke).
    #[test]
    fn revocation_witness_rejects_fabricated_slot() {
        let tree = CanonicalCapTree::new(vec![leaf(7, 0x11, 1, 0xFF)], CAP_TREE_DEPTH);
        assert!(
            tree.revocation_witness(slot_hash(99)).is_none(),
            "a slot not in the tree has no revocation witness"
        );
    }

    /// **THE IN-CIRCUIT MEMBERSHIP OPEN (the authority leg's witness).** A
    /// `membership_witness` opens the genuine held leaf and its depth-16
    /// `(sibling, direction)` path recomposes the committed root from the leaf
    /// digest — the EXACT contract the `CapMembership` AIR's root-pin enforces
    /// and the Lean `capOpen_membership` proves. This is the value
    /// `full_turn_proof.rs` must pass for a cap turn (killing the `&[]` placeholder).
    #[test]
    fn membership_witness_recomposes_to_root() {
        let held = leaf(7, 0x55, 1, 0xFFFF_FFFF);
        let other_a = leaf(3, 0x22, 1, 0xFF);
        let other_b = leaf(42, 0x33, 2, 0x1);
        let tree = CanonicalCapTree::new(vec![held, other_a, other_b], CAP_TREE_DEPTH);

        let w = tree
            .membership_witness(held.slot_hash)
            .expect("held slot present");
        assert_eq!(w.leaf, held, "the witness opens the genuine held leaf");
        assert_eq!(
            w.root,
            tree.root(),
            "the witness root is the committed tree root"
        );
        assert_eq!(w.siblings.len(), CAP_TREE_DEPTH);
        assert_eq!(w.directions.len(), CAP_TREE_DEPTH);
        assert!(
            w.recomposes(),
            "the depth-16 fold of the held leaf digest MUST reach the committed root (the AIR's root-pin)"
        );
    }

    /// The leaf↔effect binding: a witness's opened leaf authenticates its
    /// `target` against the turn's `src`, and the write submask against `mask_lo`.
    /// The Rust twin of the Lean `targetBindGate` / `writeMaskGate`.
    #[test]
    fn membership_witness_binds_target_and_write() {
        // A read+write cap (low-16 mask = 0xFFFF) over target byte 0x55.
        let held = leaf(7, 0x55, 1, 0xFFFF);
        let tree = CanonicalCapTree::new(vec![held], CAP_TREE_DEPTH);
        let w = tree.membership_witness(held.slot_hash).unwrap();

        // target binding: the opened leaf's target IS held.target …
        assert!(
            w.target_is(held.target),
            "target binds to the committed leaf"
        );
        // … and REJECTS an arbitrary other src.
        let mut other = [0u8; 32];
        other[0] = 0x99;
        assert!(
            !w.target_is(fold_bytes32(&other)),
            "target binding rejects a non-matching src (not an arbitrary leaf)"
        );

        // write submask: bit 1 (0x1) is set in mask_lo = 0xFFFF.
        assert!(
            w.confers_write(0x1),
            "a present mask bit passes the write submask"
        );
        // a bit NOT in the mask is rejected.
        let narrow = leaf(8, 0x55, 1, 0x1); // mask_lo = 0x1
        let tree2 = CanonicalCapTree::new(vec![narrow], CAP_TREE_DEPTH);
        let w2 = tree2.membership_witness(narrow.slot_hash).unwrap();
        assert!(
            !w2.confers_write(0x2),
            "a bit absent from mask_lo fails the write submask (the anti-amplify tooth)"
        );
    }

    /// A fabricated leaf or tampered path does NOT recompose to the committed
    /// root — the in-circuit forgery guard (Lean: a forged leaf makes
    /// `capOpen_membership` unsatisfiable). We swap the opened leaf's digest by
    /// mutating a field and check the recompose now misses the root.
    #[test]
    fn membership_witness_rejects_forged_leaf() {
        let held = leaf(7, 0x55, 1, 0xFFFF);
        let tree = CanonicalCapTree::new(vec![held], CAP_TREE_DEPTH);
        let mut w = tree.membership_witness(held.slot_hash).unwrap();
        assert!(w.recomposes(), "genuine witness recomposes");

        // Forge: replace the leaf with a rights-inflated one (different digest)
        // while keeping the authenticated path. The fold now misses the root.
        let mut forged = held;
        forged.mask_lo = BabyBear::new(0xFFFF_u32); // already; bump high instead
        forged.mask_hi = BabyBear::new(0x1);
        w.leaf = forged;
        assert!(
            !w.recomposes(),
            "a forged (digest-changed) leaf MUST fail to recompose to the committed root"
        );
    }

    // ---- SPARSE-FOLD BYTE-IDENTITY DIFFERENTIAL (temp; pins step 1 of INCREMENTAL-COMMITMENT.md) ----

    /// A tiny deterministic xorshift RNG — no external dep, reproducible corpus.
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
    /// sorted/deduped/tombstoned leaf+digest list EXACTLY as
    /// `new_with_tombstones`, then `resize` to the full `2^depth` with ZERO
    /// padding and fold ALL levels. Returns `(root, levels)` so membership can
    /// be cross-checked against the dense level arrays.
    fn dense_build(
        leaves: Vec<CapLeaf>,
        tombstone_keys: &[BabyBear],
        depth: usize,
    ) -> (Vec<CapLeaf>, Vec<Vec<[BabyBear; CAP_DIGEST_W]>>) {
        let mut leaves = leaves;
        leaves.push(sentinel_leaf(SENTINEL_MIN));
        leaves.push(sentinel_leaf(SENTINEL_MAX));
        leaves.sort_by_key(|l| l.slot_hash.as_u32());
        leaves.dedup_by_key(|l| l.slot_hash.as_u32());
        let live_keys: std::collections::HashSet<u32> =
            leaves.iter().map(|l| l.slot_hash.as_u32()).collect();
        let mut keyed: Vec<(CapLeaf, [BabyBear; CAP_DIGEST_W])> =
            leaves.into_iter().map(|l| (l, l.digest())).collect();
        let mut seen_tomb: std::collections::HashSet<u32> = std::collections::HashSet::new();
        for &k in tombstone_keys {
            let ku = k.as_u32();
            if live_keys.contains(&ku) || !seen_tomb.insert(ku) {
                continue;
            }
            keyed.push((sentinel_leaf(k), CAP_ZERO8));
        }
        keyed.sort_by_key(|(l, _)| l.slot_hash.as_u32());
        let capacity = 1usize << depth;
        assert!(keyed.len() <= capacity);
        let sorted_leaves: Vec<CapLeaf> = keyed.iter().map(|(l, _)| *l).collect();
        let mut leaf_digests: Vec<[BabyBear; CAP_DIGEST_W]> =
            keyed.iter().map(|(_, d)| *d).collect();
        leaf_digests.resize(capacity, CAP_ZERO8);
        let mut levels = vec![leaf_digests];
        for _ in 0..depth {
            let prev = levels.last().unwrap();
            let mut next = Vec::with_capacity(prev.len() / 2);
            for chunk in prev.chunks(2) {
                next.push(cap_node8(chunk[0], chunk[1]));
            }
            levels.push(next);
        }
        (sorted_leaves, levels)
    }

    fn rand_leaf(rng: &mut Rng) -> CapLeaf {
        // Keep slots in a modest range so collisions (dedup) get exercised.
        leaf(
            rng.below(64),
            rng.below(255) as u8,
            rng.below(6),
            rng.next_u64() as u32,
        )
    }

    /// THE DIFFERENTIAL: for a 10k-case random corpus of {leaf sets of varying
    /// size incl. empty, + tombstone key sets}, the SPARSE `new_with_tombstones`
    /// must produce the byte-identical root AND byte-identical membership paths
    /// (siblings + directions) for every present leaf, vs the dense oracle.
    /// Use a SMALL depth so the dense oracle is affordable; the fold logic is
    /// depth-independent, so byte-identity here implies it at depth 16 (and the
    /// depth-16 empty/grant tests above pin the canonical depth).
    #[test]
    fn sparse_matches_dense_root_and_membership() {
        const CASES: usize = 10_000;
        const DEPTH: usize = 8; // capacity 256; oracle folds 255 nodes/case
        let mut rng = Rng(0x5107_CABD_BEEF_0001);
        let mut mismatches = 0usize;
        let mut total_leaves = 0usize;
        for _ in 0..CASES {
            let n = rng.below(60) as usize; // 0..=59 live leaves (incl. empty)
            let leaves: Vec<CapLeaf> = (0..n).map(|_| rand_leaf(&mut rng)).collect();
            let n_tomb = rng.below(8) as usize;
            let tombs: Vec<BabyBear> = (0..n_tomb).map(|_| slot_hash(rng.below(64))).collect();

            let sparse = CanonicalCapTree::new_with_tombstones(leaves.clone(), &tombs, DEPTH);
            let (oracle_leaves, oracle_levels) = dense_build(leaves, &tombs, DEPTH);

            if sparse.root() != oracle_levels[DEPTH][0] {
                mismatches += 1;
                continue;
            }
            // sorted_leaves must be index-aligned identical (membership relies on it).
            assert_eq!(sparse.sorted_leaves(), oracle_leaves.as_slice());
            for pos in 0..oracle_leaves.len() {
                total_leaves += 1;
                let (s_sib, s_dir) = sparse.prove_membership(pos).unwrap();
                // Dense membership over the oracle level arrays.
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
            "sparse cap-tree fold must be byte-identical to the dense build over {CASES} cases ({total_leaves} membership paths checked)"
        );
    }

    /// Byte-identity at the CANONICAL depth-16 too: root + every membership path
    /// for a handful of non-trivial c-lists (incl. tombstones) match the dense
    /// depth-16 oracle. (Fewer cases — the depth-16 oracle is the expensive
    /// 65535-node fold this whole change exists to avoid.)
    #[test]
    fn sparse_matches_dense_at_depth_16() {
        let cases: Vec<(Vec<CapLeaf>, Vec<BabyBear>)> = vec![
            (vec![], vec![]),
            (vec![leaf(0, 1, 1, 0xFFFF_FFFF)], vec![]),
            (
                vec![
                    leaf(7, 0x11, 1, 0xFF),
                    leaf(3, 0x22, 1, 0xFFFF),
                    leaf(42, 0x33, 2, 0x1),
                ],
                vec![],
            ),
            (
                vec![leaf(3, 0x22, 1, 0xFFFF), leaf(42, 0x33, 2, 0x1)],
                vec![slot_hash(7)],
            ),
            (
                (0..50)
                    .map(|i| leaf(i, (i % 255) as u8, i % 6, i.wrapping_mul(7)))
                    .collect(),
                vec![slot_hash(5), slot_hash(13)],
            ),
        ];
        for (leaves, tombs) in cases {
            let sparse =
                CanonicalCapTree::new_with_tombstones(leaves.clone(), &tombs, CAP_TREE_DEPTH);
            let (oracle_leaves, oracle_levels) = dense_build(leaves, &tombs, CAP_TREE_DEPTH);
            assert_eq!(
                sparse.root(),
                oracle_levels[CAP_TREE_DEPTH][0],
                "depth-16 root"
            );
            assert_eq!(sparse.sorted_leaves(), oracle_leaves.as_slice());
            for pos in 0..oracle_leaves.len() {
                let (s_sib, s_dir) = sparse.prove_membership(pos).unwrap();
                let mut idx = pos;
                for level in 0..CAP_TREE_DEPTH {
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
