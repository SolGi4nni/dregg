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

use crate::field::BabyBear;
use crate::poseidon2::{hash_fact, hash_many};

pub use crate::dsl::revocation::{SENTINEL_MAX, SENTINEL_MIN};

/// Tree depth for the canonical capability tree. A binary tree of depth 16
/// holds `2^16 - 2 = 65534` capabilities (two positions reserved for the
/// MIN/MAX sentinels). Chosen large enough that a c-list never re-rotates
/// the tree in practice.
pub const CAP_TREE_DEPTH: usize = 16;

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
    pub fn digest(&self) -> BabyBear {
        hash_many(&[
            self.slot_hash,
            self.target,
            self.auth_tag,
            self.mask_lo,
            self.mask_hi,
            self.expiry,
            self.breadstuff,
        ])
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
    /// All levels, bottom-up. `levels[0]` = leaf digests (padded);
    /// `levels[depth]` = `[root]`.
    levels: Vec<Vec<BabyBear>>,
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
        let mut keyed: Vec<(CapLeaf, BabyBear)> =
            leaves.into_iter().map(|l| (l, l.digest())).collect();
        let mut seen_tomb: std::collections::HashSet<u32> = std::collections::HashSet::new();
        for &k in tombstone_keys {
            let ku = k.as_u32();
            if live_keys.contains(&ku) || !seen_tomb.insert(ku) {
                continue;
            }
            // Ghost: keyed at `k`, all other fields zero, stored digest ZERO.
            keyed.push((sentinel_leaf(k), BabyBear::ZERO));
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
        let mut leaf_digests: Vec<BabyBear> = keyed.iter().map(|(_, d)| *d).collect();
        // Pad with the zero felt (the empty-position marker), exactly like the
        // revocation tree.
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
            sorted_leaves,
            depth,
        }
    }

    /// The Merkle root.
    pub fn root(&self) -> BabyBear {
        self.levels[self.depth][0]
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
                    && self.levels[0][*i] != BabyBear::ZERO
            })
            .count()
    }

    /// The tree depth.
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// All level vectors, bottom-up (`levels[0]` = padded leaf digests,
    /// `levels[depth] = [root]`). Exposed for Phase-B membership witnessing.
    pub fn levels(&self) -> &[Vec<BabyBear>] {
        &self.levels
    }

    /// The leaf-array position (0-based, in the padded bottom level) of the
    /// leaf whose `slot_hash == key`, or `None` if no such (non-padding) leaf
    /// exists. The sorted-tree placement is by `slot_hash` ordering, so this
    /// is the canonical position the membership path opens.
    pub fn position_of(&self, key: BabyBear) -> Option<usize> {
        self.sorted_leaves.iter().position(|l| l.slot_hash == key)
    }

    /// Generate a Merkle **membership** path for the leaf at the given padded
    /// position: `(siblings, directions)` where `directions[i] == 0` if the
    /// current node is the LEFT child at level `i` (sibling on the right), `1`
    /// otherwise. Mirrors [`crate::dsl::revocation::DslRevocationTree::prove_membership`].
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
    pub siblings: Vec<BabyBear>,
    /// Direction bits along the path (0 = current is left child, 1 = right).
    pub directions: Vec<u8>,
    /// The authenticated old root (= the held leaf's path top).
    pub old_root: BabyBear,
    /// The recomputed new root (= the granted leaf's path top, same siblings).
    pub new_root: BabyBear,
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
                hash_fact(cur, &[sib])
            } else {
                hash_fact(sib, &[cur])
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
        let mut cur = BabyBear::ZERO;
        for level in 0..self.depth {
            let sib = siblings[level];
            cur = if directions[level] == 0 {
                hash_fact(cur, &[sib])
            } else {
                hash_fact(sib, &[cur])
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

/// Compute the canonical capability root over a set of leaves at the canonical
/// depth ([`CAP_TREE_DEPTH`]). This is THE function `dregg-cell` calls; the
/// circuit seeds its `cap_root` column from this same value.
pub fn compute_capability_root(leaves: Vec<CapLeaf>) -> BabyBear {
    CanonicalCapTree::new(leaves, CAP_TREE_DEPTH).root()
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
) -> BabyBear {
    CanonicalCapTree::new_with_tombstones(leaves, tombstone_keys, CAP_TREE_DEPTH).root()
}

/// The canonical capability root of the EMPTY c-list (only the two sentinels).
/// This is the value `CellState::new` seeds `cap_root` with, and the value a
/// fresh cell's `compute_canonical_capability_root` returns. Deterministic and
/// cell-independent.
pub fn empty_capability_root() -> BabyBear {
    compute_capability_root(Vec::new())
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

    /// The empty root is deterministic and non-zero (the sentinels hash into a
    /// real value, not the all-zero default).
    #[test]
    fn empty_root_deterministic_and_nonzero() {
        let a = empty_capability_root();
        let b = empty_capability_root();
        assert_eq!(a, b, "empty root is deterministic");
        assert_ne!(
            a,
            BabyBear::ZERO,
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
        let mut cur = BabyBear::ZERO;
        for level in 0..CAP_TREE_DEPTH {
            cur = if w.directions[level] == 0 {
                hash_fact(cur, &[w.siblings[level]])
            } else {
                hash_fact(w.siblings[level], &[cur])
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
                hash_fact(hcur, &[w.siblings[level]])
            } else {
                hash_fact(w.siblings[level], &[hcur])
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
}
