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
        Some(h) => hash_many(&[
            BabyBear::new(h as u32),
            BabyBear::new((h >> 32) as u32),
        ]),
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
    pub fn new(mut leaves: Vec<CapLeaf>, depth: usize) -> Self {
        leaves.push(sentinel_leaf(SENTINEL_MIN));
        leaves.push(sentinel_leaf(SENTINEL_MAX));
        // Sort by the canonical sort key (slot_hash). Deterministic, total.
        leaves.sort_by_key(|l| l.slot_hash.as_u32());
        leaves.dedup_by_key(|l| l.slot_hash.as_u32());

        let capacity = 1usize << depth;
        // The c-list must fit (minus the two sentinels). A c-list this large
        // never occurs in practice; fail loudly rather than silently truncate.
        assert!(
            leaves.len() <= capacity,
            "capability c-list ({} entries incl. sentinels) exceeds tree capacity 2^{depth}",
            leaves.len()
        );

        let mut leaf_digests: Vec<BabyBear> = leaves.iter().map(CapLeaf::digest).collect();
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
            sorted_leaves: leaves,
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

    /// Number of real (non-sentinel) capabilities.
    pub fn num_caps(&self) -> usize {
        self.sorted_leaves
            .iter()
            .filter(|l| l.slot_hash != SENTINEL_MIN && l.slot_hash != SENTINEL_MAX)
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
        self.sorted_leaves
            .iter()
            .position(|l| l.slot_hash == key)
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
        assert_ne!(a, BabyBear::ZERO, "empty root is NOT the ZERO default (the disjoint-seed bug)");
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
        assert_ne!(all, lo_only, "high 16 bits of the mask must bind (no 30-bit truncation)");
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
        assert_ne!(base.digest(), other.digest(), "breadstuff must bind the leaf");
        // And None vs Some differs.
        let none = leaf(0, 1, 1, 0x1);
        assert_ne!(none.digest(), base.digest(), "None vs Some breadstuff must differ");
    }

    /// Distinct auth tiers bind (tier byte participates).
    #[test]
    fn auth_tier_binds() {
        let sig = compute_capability_root(vec![leaf(0, 1, 1, 0x1)]);
        let proof = compute_capability_root(vec![leaf(0, 1, 2, 0x1)]);
        assert_ne!(sig, proof, "auth tier must bind the root");
    }
}
