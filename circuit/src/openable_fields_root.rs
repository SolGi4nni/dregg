//! The canonical, **openable** `fields_root` commitment + an IN-CIRCUIT
//! INSERTION gate: a SORTED Poseidon2 binary Merkle map over a cell's
//! overflow user-field entries `key → value`, whose post-insertion root is
//! DERIVED in-circuit from the pre-root + the public `(key, value)`.
//!
//! ## Why this module exists (the REFUSAL ledgerless-authority close, #103)
//!
//! `refusal`'s authority change is the write of an audit record into the
//! protocol-reserved `fields_root` key (`REFUSAL_AUDIT_EXT_KEY`):
//!
//! ```text
//! post_fields_root = insert(pre_fields_root_map, REFUSAL_AUDIT_KEY → audit)
//! audit = blake3_keyed("dregg-refusal-audit-v1", offered_action_commitment
//!                       ++ reason_tag ++ reason_hash)
//! ```
//!
//! The deployed `fields_root` (`cell::state::compute_fields_root`) is a
//! length-seeded BLAKE3 sponge over the WHOLE `(key, value)` map, so the
//! post-root depends on every entry — a LEDGERLESS client (one holding only
//! the published commitment, not the trusted post-cell) cannot recompute it.
//! Today the verifier sidesteps this OFF-CIRCUIT: it anchors the post-root
//! from the trusted post-cell via `Anchor::RecordDigest`
//! (`turn/src/executor/proof_verify.rs`). That is the gap — refusal's
//! authority change is FORCED OFF-CIRCUIT.
//!
//! This module supplies the openable replacement: a sorted Poseidon2 Merkle
//! map (the SAME primitive [`crate::cap_root`] / [`crate::heap_root`] use)
//! that supports an **in-circuit insertion gate**. Given the in-circuit
//! pre-root, a key, and a value, the gate FORCES
//!
//! ```text
//! post_root = insert(pre_root, key → value)
//! ```
//!
//! by opening ONE Merkle path (the position the key sorts to) and recomputing
//! the root with the new leaf — the OLD leaf folds up the witnessed sibling
//! path to `pre_root`, the NEW leaf folds up the SAME path to `post_root`. The
//! sibling path is WITNESSED and CONSTRAINED (it appears inside the in-circuit
//! `cap_node` hashes that the two boundaries pin), NOT a free `post_root`
//! column — so a prover cannot publish a `post_root` that is not the genuine
//! insertion of the witnessed `(key, value)` into the witnessed `pre_root`.
//!
//! With an openable root the post-root is DERIVED in-circuit from
//! `(pre_root + public key + public value)` — no trusted post-cell is needed.
//! For refusal the `value` is the PUBLIC audit felt (folded from the public
//! offered-action-commitment + reason), so a ledgerless client recomputes the
//! audit, supplies it as the public insertion value, and the proof alone binds
//! the post-root.
//!
//! ## The scheme (mirrors the proven [`crate::cap_root::CanonicalCapTree`])
//!
//! A SORTED binary Merkle tree over the `fields_map` entries, keyed by `key`
//! (the overflow user-field key, `>= STATE_SLOTS`), sentinel-bracketed by
//! [`SENTINEL_MIN`] / [`SENTINEL_MAX`], padded to `2^DEPTH`. Internal nodes are
//! [`cap_node`] — the SAME single in-circuit cap hash the cap-membership DSL
//! commits to (`cap_chip_absorb([CAP_FACT_MARK, l, r])`), so the path folds are
//! chip-realizable via the `Hash3Cap` form on the audited `prove_dsl_p3` path.
//! Each leaf is the arity-2 image `hash[key, value]` (a sort-key + payload pair,
//! the same 2-field shape [`crate::heap_root::HeapLeaf`] uses).
//!
//! ## Position-stable (reserved-slot) discipline — the single-shared-path key
//!
//! A SORTED-compacting tree re-indexes on a fresh insert (every larger key and
//! the MAX sentinel shift), so a fresh insert and its pre-image would NOT share
//! one sibling path. To keep ONE shared path (the insertion gate's requirement)
//! this tree is POSITION-STABLE, exactly the TOMBSTONE discipline
//! [`crate::cap_root`] uses for revoke: a key occupies a FIXED sorted position,
//! and an insert/update is an in-place value move at that position (no
//! re-index). A cell that can refuse RESERVES the audit slot ([`with_reserved`]
//! / [`refusal_pre_tree`]): the audit key is present with value `ZERO` (a real
//! `hash[key, 0]` leaf at its sorted position). A refusal then OVERWRITES that
//! slot's value (ZERO → audit), so the OLD leaf (`hash[key, 0]`, witnessed) and
//! the NEW leaf (`hash[key, audit]`) fold up the SAME sibling path to `pre_root`
//! / `post_root`. A refusal that re-fires overwrites the real old audit the same
//! way. The post-root the verifier independently reconstructs is
//! [`OpenableFieldsTree::with_value_at`] (the SAME layout, one leaf moved) — no
//! trusted post-cell.

use crate::cap_root::{CAP_TREE_DEPTH, cap_node};
use crate::field::BabyBear;
use crate::poseidon2::hash_many;

pub use crate::dsl::revocation::{SENTINEL_MAX, SENTINEL_MIN};

/// Tree depth for the canonical openable fields tree. Matches
/// [`CAP_TREE_DEPTH`] (16): `2^16 - 2 = 65534` overflow entries (two positions
/// reserved for the MIN/MAX sentinels). A cell's overflow field map never
/// re-rotates the tree in practice.
pub const FIELDS_TREE_DEPTH: usize = CAP_TREE_DEPTH;

/// The canonical sort key for an overflow field key: a domain-separated
/// Poseidon2 image of the (unbounded) `u64` key, so the sorted-tree positions
/// are well-distributed and a `u64` key (`REFUSAL_AUDIT_EXT_KEY = 2^32` is far
/// above any app key) maps injectively into the BabyBear sort domain. Mirrors
/// [`crate::cap_root::slot_hash`] in spirit (a hashed sort key, not the raw
/// integer).
const FIELDS_KEY_TAG: u32 = 0x0F1E_1D50; // "fields"

/// The canonical sort key for an overflow field key `key: u64`. Folds both
/// 32-bit limbs through the domain-tagged Poseidon2 sponge so the full 64-bit
/// key binds (`REFUSAL_AUDIT_EXT_KEY` lives at `2^32`, so the high limb is
/// load-bearing).
pub fn field_key_hash(key: u64) -> BabyBear {
    hash_many(&[
        BabyBear::new(FIELDS_KEY_TAG),
        BabyBear::new(key as u32),
        BabyBear::new((key >> 32) as u32),
    ])
}

/// Fold a 32-byte field value into a single BabyBear felt: `hash_many` over the
/// 8 little-endian limbs (`BabyBear::encode_hash`). The deployed audit value
/// (and any overflow `FieldElement`) is 32 bytes; this is the canonical,
/// collision-resistant fold (the same shape [`crate::cap_root::fold_bytes32`]
/// uses for `target` / `breadstuff`).
pub fn fold_value32(bytes: &[u8; 32]) -> BabyBear {
    hash_many(&BabyBear::encode_hash(bytes))
}

/// One openable-fields entry: the sorted-tree leaf `(key_hash, value)`. The
/// leaf digest is the arity-2 image `hash[key_hash, value]` — the same 2-field
/// shape [`crate::heap_root::HeapLeaf`] uses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldsLeaf {
    /// The sort key: [`field_key_hash`] of the entry's overflow key.
    pub key_hash: BabyBear,
    /// The stored value felt (a folded 32-byte `FieldElement`).
    pub value: BabyBear,
}

impl FieldsLeaf {
    /// The arity-2 Poseidon2 leaf digest `hash[key_hash, value]`.
    pub fn digest(&self) -> BabyBear {
        hash_many(&[self.key_hash, self.value])
    }
}

/// The sentinel leaf for a given sort key (MIN or MAX). The value is zero; the
/// sentinel brackets the sorted key range so an absent key can sit between two
/// adjacent present keys.
fn sentinel_leaf(key: BabyBear) -> FieldsLeaf {
    FieldsLeaf {
        key_hash: key,
        value: BabyBear::ZERO,
    }
}

/// The canonical openable fields tree: a sorted binary Poseidon2 Merkle tree
/// over the overflow field entries, keyed by `key_hash`, sentinel-bracketed,
/// **`cap_node`-folded** (so the path is chip-realizable in-circuit). Mirrors
/// [`crate::cap_root::CanonicalCapTree`] with the generic 2-field leaf.
#[derive(Clone, Debug)]
pub struct OpenableFieldsTree {
    /// All levels, bottom-up. `levels[0]` = leaf digests (padded);
    /// `levels[depth]` = `[root]`.
    levels: Vec<Vec<BabyBear>>,
    /// The leaves in sorted-by-`key_hash` order, including sentinels (before
    /// padding). Retained for membership / insertion witnessing.
    sorted_leaves: Vec<FieldsLeaf>,
    /// Tree depth.
    depth: usize,
}

impl OpenableFieldsTree {
    /// Build the canonical openable fields tree from a cell's overflow entries.
    pub fn new(mut leaves: Vec<FieldsLeaf>, depth: usize) -> Self {
        leaves.push(sentinel_leaf(SENTINEL_MIN));
        leaves.push(sentinel_leaf(SENTINEL_MAX));
        leaves.sort_by_key(|l| l.key_hash.as_u32());
        leaves.dedup_by_key(|l| l.key_hash.as_u32());

        let capacity = 1usize << depth;
        assert!(
            leaves.len() <= capacity,
            "openable fields map ({} entries incl. sentinels) exceeds tree capacity 2^{depth}",
            leaves.len()
        );

        let mut leaf_digests: Vec<BabyBear> = leaves.iter().map(FieldsLeaf::digest).collect();
        leaf_digests.resize(capacity, BabyBear::ZERO);

        let mut levels = vec![leaf_digests];
        for _ in 0..depth {
            let prev = levels.last().unwrap();
            let mut next_level = Vec::with_capacity(prev.len() / 2);
            for chunk in prev.chunks(2) {
                next_level.push(cap_node(chunk[0], chunk[1]));
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

    /// The sorted leaves (including sentinels). For witnessing.
    pub fn sorted_leaves(&self) -> &[FieldsLeaf] {
        &self.sorted_leaves
    }

    /// Number of real (non-sentinel) entries.
    pub fn num_entries(&self) -> usize {
        self.sorted_leaves
            .iter()
            .filter(|l| l.key_hash != SENTINEL_MIN && l.key_hash != SENTINEL_MAX)
            .count()
    }

    /// The tree depth.
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// All level vectors, bottom-up. Exposed for witnessing.
    pub fn levels(&self) -> &[Vec<BabyBear>] {
        &self.levels
    }

    /// The leaf-array position (0-based, in the padded bottom level) of the
    /// leaf whose `key_hash == key`, or `None` if no such (non-padding) leaf
    /// exists.
    pub fn position_of(&self, key: BabyBear) -> Option<usize> {
        // `sorted_leaves` is sorted+deduped by `key_hash.as_u32()`, so an exact
        // match is a binary search — O(log n) vs the former O(n) scan.
        self.sorted_leaves
            .binary_search_by(|l| l.key_hash.cmp(&key))
            .ok()
    }

    /// Generate a Merkle membership path for the leaf at the given padded
    /// position: `(siblings, directions)` where `directions[i] == 0` if the
    /// current node is the LEFT child at level `i`. Mirrors
    /// [`crate::cap_root::CanonicalCapTree::prove_membership`].
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

/// An **in-circuit insertion witness**: opens the position the `key_hash` sorts
/// to and forces `post_root = insert(pre_root, key → value)` by recomputing the
/// root with the new leaf over the SAME witnessed sibling path. The OLD leaf
/// digest (ZERO for a fresh key; the genuine old digest for a present key)
/// folds up the path to `pre_root`; the NEW leaf digest `hash[key_hash, value]`
/// folds up the SAME path to `post_root`.
///
/// This is the Rust twin of the in-circuit gate [`crate::dsl::openable_fields_insertion`]:
/// the two boundaries pin the path tops to `pre_root` / `post_root`, the shared
/// `(sibling, direction)` columns force the two folds to ride ONE path, and the
/// row-0 boundaries pin `old_leaf_digest` / `new_leaf_digest`. So the post-root
/// is DERIVED, not a free column.
#[derive(Clone, Debug)]
pub struct FieldsInsertionWitness {
    /// The sort key the insertion lands at (`field_key_hash(key)`).
    pub key_hash: BabyBear,
    /// The OLD leaf digest at the position: `BabyBear::ZERO` if the key was
    /// absent (the padding leaf), else `hash[key_hash, old_value]`.
    pub old_leaf_digest: BabyBear,
    /// The NEW leaf: `(key_hash, value)`; its digest folds to `post_root`.
    pub new_leaf: FieldsLeaf,
    /// Sibling digests along the path from the leaf to the root (bottom-up).
    pub siblings: Vec<BabyBear>,
    /// Direction bits along the path (0 = current is left child, 1 = right).
    pub directions: Vec<u8>,
    /// The authenticated pre-root (= the old leaf digest's path top).
    pub pre_root: BabyBear,
    /// The recomputed post-root (= the new leaf digest's path top, same path).
    pub post_root: BabyBear,
}

impl OpenableFieldsTree {
    /// Build a [`FieldsInsertionWitness`] for `insert(self, key → value)`. If
    /// the key is already present its position is reused (an overwrite — the
    /// refusal-re-fires case); otherwise the key's sorted position is the
    /// ZERO/padding leaf it would occupy, and the witness opens that padding
    /// position (a fresh insert at a sorted-vacant slot).
    ///
    /// Returns `None` only when the key sorts beyond the bracketing sentinels
    /// (impossible for a well-formed `field_key_hash`, which lands strictly
    /// between MIN and MAX), or when the (rare) fresh-key slot has no padding
    /// witness because the tree is full.
    pub fn insertion_witness(&self, key: u64, value: BabyBear) -> Option<FieldsInsertionWitness> {
        let key_hash = field_key_hash(key);
        let new_leaf = FieldsLeaf { key_hash, value };

        // POSITION-STABLE (reserved-slot) semantics — mirrors the cap tree's
        // TOMBSTONE discipline (`cap_root::CanonicalCapTree::attenuation_witness`):
        // an insert/update does NOT re-index the sorted array. The key occupies a
        // FIXED sorted position whether its slot is currently RESERVED (a
        // ZERO/sentinel leaf at the key's sorted slot) or PRESENT (a real
        // `hash[key, old_value]` leaf). Because the position is stable, ONE shared
        // sibling path authenticates BOTH the pre-root (old leaf at that slot) and
        // the post-root (new leaf at that slot) — the single-shared-path the
        // in-circuit insertion gate folds.
        //
        // Self IS the pre-tree, which RESERVES the key's slot: either the key is
        // already a (real or reserved) leaf, or the canonical builder placed a
        // reserved ZERO leaf at the key's sorted position (see `with_reserved`).
        // A fresh insert is then an in-place value update of a reserved slot, NOT
        // a re-indexing insert. The post-root the verifier independently computes
        // is `self.with_value_at(key, value)` (the SAME layout, one leaf moved) —
        // pinned byte-identical by `is_genuine_insertion` + the differential.
        let pos = self.position_of(key_hash)?;
        let old_leaf = self.sorted_leaves[pos];
        let old_leaf_digest = self.levels[0][pos]; // the STORED digest (ZERO if reserved)

        let (siblings, directions) = self.prove_membership(pos)?;

        // pre_root: fold the OLD stored leaf digest up the witnessed path.
        let pre_root = recompose(old_leaf_digest, &siblings, &directions);
        // post_root: fold the NEW leaf digest up the SAME path.
        let post_root = recompose(new_leaf.digest(), &siblings, &directions);

        let _ = old_leaf;
        Some(FieldsInsertionWitness {
            key_hash,
            old_leaf_digest,
            new_leaf,
            siblings,
            directions,
            pre_root,
            post_root,
        })
    }

    /// The post-`fields_root` the verifier independently computes after an
    /// in-place value update at `key`: the SAME tree with the key's leaf set to
    /// `hash[key, value]` (position-stable; no re-index). The canonical post-cell
    /// root a ledgerless verifier reconstructs and pins against the proof's
    /// `post_root`. `key` MUST be a reserved/present slot (`with_reserved`).
    pub fn with_value_at(&self, key: u64, value: BabyBear) -> Option<BabyBear> {
        let key_hash = field_key_hash(key);
        let pos = self.position_of(key_hash)?;
        let (siblings, directions) = self.prove_membership(pos)?;
        let new_leaf = FieldsLeaf { key_hash, value };
        Some(recompose(new_leaf.digest(), &siblings, &directions))
    }
}

/// Build an openable fields tree from the cell's real entries PLUS a set of
/// RESERVED protocol keys (e.g. [`REFUSAL_AUDIT_EXT_KEY`]). A reserved key
/// occupies its sorted position with a ZERO-valued (sentinel-style) leaf, so a
/// later in-place insert of its value is a position-stable value update (NOT a
/// re-indexing insert) — the discipline the in-circuit insertion gate's
/// single-shared-path requires. This is the openable representation a cell with
/// the refusal-audit slot reserved carries.
pub fn with_reserved(
    mut entries: Vec<FieldsLeaf>,
    reserved_keys: &[u64],
    depth: usize,
) -> OpenableFieldsTree {
    use std::collections::HashSet;
    let present: HashSet<u32> = entries.iter().map(|l| l.key_hash.as_u32()).collect();
    let mut seen: HashSet<u32> = HashSet::new();
    for &k in reserved_keys {
        let kh = field_key_hash(k);
        if present.contains(&kh.as_u32()) || !seen.insert(kh.as_u32()) {
            continue;
        }
        // A reserved slot: keyed at the protocol key, value ZERO (so its stored
        // digest is `hash[key_hash, 0]`, a real non-padding leaf at a stable
        // sorted position — distinct from the ZERO padding of empty positions).
        entries.push(FieldsLeaf {
            key_hash: kh,
            value: BabyBear::ZERO,
        });
    }
    OpenableFieldsTree::new(entries, depth)
}

/// Fold a leaf digest up a `(sibling, direction)` path to the root, using the
/// chip-realizable [`cap_node`] at each level. The Rust twin of the in-circuit
/// per-level fold (`dir == 0` ⇒ current is LEFT child ⇒ `cap_node(cur, sib)`).
pub fn recompose(leaf_digest: BabyBear, siblings: &[BabyBear], directions: &[u8]) -> BabyBear {
    assert_eq!(
        siblings.len(),
        directions.len(),
        "insertion path: siblings and directions must have equal length"
    );
    let mut cur = leaf_digest;
    for level in 0..siblings.len() {
        let sib = siblings[level];
        cur = if directions[level] == 0 {
            cap_node(cur, sib)
        } else {
            cap_node(sib, cur)
        };
    }
    cur
}

impl FieldsInsertionWitness {
    /// Check the witness genuinely opens an INSERTION: the old leaf folds to
    /// `pre_root` and the new leaf folds to `post_root` over the SAME path —
    /// the soundness contract the AIR's two boundaries enforce. A tampered
    /// `post_root` (not the genuine insertion) fails here.
    pub fn is_genuine_insertion(&self) -> bool {
        recompose(self.old_leaf_digest, &self.siblings, &self.directions) == self.pre_root
            && recompose(self.new_leaf.digest(), &self.siblings, &self.directions) == self.post_root
    }

    /// The NEW leaf's digest (the value the AIR pins at the new-leaf row-0
    /// boundary). The composing verifier recomputes it from the PUBLIC
    /// `(key, value)` — for refusal, from the public audit felt — so the leaf
    /// FIELDS are bound, not just a digest.
    pub fn new_leaf_digest(&self) -> BabyBear {
        self.new_leaf.digest()
    }
}

// ============================================================================
// REFUSAL application: the public-audit fold + the insertion witness
// ============================================================================

/// The deployed refusal-audit ext key (`cell::state::REFUSAL_AUDIT_EXT_KEY`,
/// `2^32`). Re-declared here so the circuit crate need not depend on `cell` at
/// the library layer; the differential / refusal application pins the two equal.
pub const REFUSAL_AUDIT_EXT_KEY: u64 = 0x0000_0001_0000_0000;

/// Fold the PUBLIC 32-byte refusal audit value into the insertion VALUE felt.
/// The audit is `blake3_keyed("dregg-refusal-audit-v1", offered_action_commitment
/// ++ reason_tag ++ reason_hash)` — every input is light-client-knowable (the
/// offered-action commitment and the reason are public), so a ledgerless client
/// recomputes this felt and supplies it as the public insertion value. The
/// proof alone then binds the post-`fields_root`.
pub fn refusal_audit_value(audit: &[u8; 32]) -> BabyBear {
    fold_value32(audit)
}

/// Build a cell's PRE-refusal openable fields tree with the refusal-audit slot
/// RESERVED (a position-stable ZERO-valued leaf at the audit key). A cell that
/// can refuse carries this representation, so a refusal is an in-place value
/// update at the stable audit slot — the single-shared-path the insertion gate
/// folds. (A cell that has already refused carries the audit slot with its real
/// value; re-firing overwrites it, also position-stable.)
pub fn refusal_pre_tree(entries: Vec<FieldsLeaf>) -> OpenableFieldsTree {
    with_reserved(entries, &[REFUSAL_AUDIT_EXT_KEY], FIELDS_TREE_DEPTH)
}

/// Build the refusal insertion witness: write the PUBLIC audit felt at the
/// (reserved or present) refusal-audit slot of the pre-`fields_root` tree,
/// forcing the post-`fields_root` in-circuit. `pre_tree` is the cell's
/// PRE-refusal overflow fields tree (the openable representation of
/// `pre_fields_root`) — built via [`refusal_pre_tree`] so the audit slot is
/// position-stable. The post-`fields_root` the verifier independently
/// reconstructs is `pre_tree.with_value_at(REFUSAL_AUDIT_EXT_KEY, audit)`.
pub fn refusal_insertion_witness(
    pre_tree: &OpenableFieldsTree,
    audit: &[u8; 32],
) -> Option<FieldsInsertionWitness> {
    pre_tree.insertion_witness(REFUSAL_AUDIT_EXT_KEY, refusal_audit_value(audit))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(key: u64, val: u32) -> FieldsLeaf {
        FieldsLeaf {
            key_hash: field_key_hash(key),
            value: BabyBear::new(val),
        }
    }

    /// The empty root is deterministic and non-zero (the sentinels fold to a
    /// real value, not the all-zero default — the anti-vacuity floor).
    #[test]
    fn empty_root_deterministic_and_nonzero() {
        let a = OpenableFieldsTree::new(Vec::new(), FIELDS_TREE_DEPTH).root();
        let b = OpenableFieldsTree::new(Vec::new(), FIELDS_TREE_DEPTH).root();
        assert_eq!(a, b);
        assert_ne!(a, BabyBear::ZERO);
    }

    /// Writing into a RESERVED audit slot (the fresh-refusal case) derives
    /// post_root over the SAME witnessed path, POSITION-STABLE: the reserved
    /// (value-ZERO) leaf folds to pre_root and the audit leaf folds to post_root.
    /// The post_root equals the canonical position-stable rebuild
    /// (`with_value_at`) — the byte-identical root a ledgerless verifier
    /// reconstructs (NO re-index; the tombstone discipline `cap_root` uses).
    #[test]
    fn fresh_insert_derives_post_root_in_circuit() {
        // The pre-tree RESERVES the audit slot (position-stable): a cell that can
        // refuse carries this representation.
        let pre = refusal_pre_tree(vec![leaf(20, 7), leaf(99, 3)]);
        let w = pre
            .insertion_witness(REFUSAL_AUDIT_EXT_KEY, BabyBear::new(0xABCD))
            .expect("reserved-slot insert witness");
        // The reserved slot's old stored leaf is the value-ZERO leaf (a real
        // hash[key,0] leaf at a stable position), NOT the empty-padding ZERO.
        assert_eq!(
            w.old_leaf_digest,
            FieldsLeaf {
                key_hash: field_key_hash(REFUSAL_AUDIT_EXT_KEY),
                value: BabyBear::ZERO
            }
            .digest(),
            "reserved slot: old leaf is the value-ZERO leaf"
        );
        assert_eq!(
            w.pre_root,
            pre.root(),
            "old leaf folds to the genuine pre-root"
        );
        assert!(
            w.is_genuine_insertion(),
            "the two folds ride ONE shared path"
        );

        // The post_root is the canonical POSITION-STABLE rebuild (one leaf moved,
        // no re-index) — what the verifier independently reconstructs.
        let canonical_post = pre
            .with_value_at(REFUSAL_AUDIT_EXT_KEY, BabyBear::new(0xABCD))
            .expect("reserved slot present");
        assert_eq!(
            w.post_root, canonical_post,
            "the in-circuit-derived post_root IS the position-stable value update"
        );
        assert_ne!(
            w.post_root, w.pre_root,
            "writing the audit value moves the root"
        );
    }

    /// Overwriting a PRESENT key (refusal re-fires): the old leaf digest is the
    /// genuine old `hash[key, old_value]`, the new leaf folds to a moved root.
    #[test]
    fn present_overwrite_derives_post_root() {
        let pre = OpenableFieldsTree::new(
            vec![leaf(REFUSAL_AUDIT_EXT_KEY, 0x1111), leaf(20, 7)],
            FIELDS_TREE_DEPTH,
        );
        let w = pre
            .insertion_witness(REFUSAL_AUDIT_EXT_KEY, BabyBear::new(0x2222))
            .expect("overwrite witness");
        assert_eq!(
            w.old_leaf_digest,
            leaf(REFUSAL_AUDIT_EXT_KEY, 0x1111).digest(),
            "present key: old leaf is the genuine old digest"
        );
        assert_eq!(w.pre_root, pre.root());
        assert!(w.is_genuine_insertion());
        assert_ne!(
            w.post_root, w.pre_root,
            "overwriting the value moves the root"
        );
    }

    /// THE TOOTH (Rust witness layer): a forged post_root (not the genuine
    /// insertion) fails `is_genuine_insertion` — the path constrains it. The
    /// AIR test (`tests/openable_fields_insertion_air.rs`) is the real-Plonky3
    /// UNSAT proof; this pins the witness-level contract.
    #[test]
    fn forged_post_root_fails_witness() {
        let pre = refusal_pre_tree(vec![leaf(20, 7)]);
        let mut w = pre
            .insertion_witness(REFUSAL_AUDIT_EXT_KEY, BabyBear::new(0xBEEF))
            .unwrap();
        assert!(w.is_genuine_insertion());
        // Forge: bump the post_root off the genuine insertion.
        w.post_root = w.post_root + BabyBear::new(1);
        assert!(
            !w.is_genuine_insertion(),
            "a forged post_root MUST fail the insertion check (the path is constrained)"
        );
    }

    /// The refusal audit value is light-client-recomputable: folding the same
    /// 32-byte audit yields the same insertion value (no trusted post-cell).
    #[test]
    fn refusal_audit_value_is_public_recomputable() {
        let audit = [0x5Au8; 32];
        let a = refusal_audit_value(&audit);
        let b = refusal_audit_value(&audit);
        assert_eq!(
            a, b,
            "the audit fold is deterministic from the public bytes"
        );
        let other = refusal_audit_value(&[0x5Bu8; 32]);
        assert_ne!(a, other, "distinct audits fold to distinct values");
    }

    /// THE LEAN DIFFERENTIAL PIN: the refusal map-op's KEY constant
    /// (`EffectVmEmitRotationV3.refusalAuditKeyFelt`, emitted into the
    /// `refusalVmDescriptor2R24` JSON as `{"t":"const","v":529176517}`) IS the
    /// Rust `field_key_hash(REFUSAL_AUDIT_EXT_KEY)`. The in-circuit `.write`
    /// map-op opens the audit slot at THIS sort key; the cell-side openable
    /// `fields_root` (`cell::state::compute_fields_root`) reserves the slot at
    /// the SAME key. A drift here would float the gate (the map-op would look
    /// for an absent key and the honest refusal would fail to prove).
    #[test]
    fn fields_root_key_felt_matches_lean() {
        assert_eq!(
            field_key_hash(REFUSAL_AUDIT_EXT_KEY).as_u32(),
            529_176_517,
            "the refusal-audit sort key felt must equal the Lean `refusalAuditKeyFelt` constant \
             emitted into the descriptor JSON (529176517) — else the .write map-op opens an absent key"
        );
    }

    /// The refusal insertion witness forces the post-`fields_root` from the
    /// public audit at the refusal-audit key — no trusted post-cell.
    #[test]
    fn refusal_insertion_forces_post_root() {
        let pre = refusal_pre_tree(vec![leaf(20, 7)]);
        let audit = [0x33u8; 32];
        let w = refusal_insertion_witness(&pre, &audit).expect("refusal witness");
        assert_eq!(w.key_hash, field_key_hash(REFUSAL_AUDIT_EXT_KEY));
        assert_eq!(w.new_leaf.value, refusal_audit_value(&audit));
        assert!(w.is_genuine_insertion());
        assert_eq!(w.pre_root, pre.root());
        assert_ne!(w.post_root, w.pre_root);
        // The post_root is the position-stable canonical rebuild — no trusted
        // post-cell needed; the verifier reconstructs it from pre + public audit.
        assert_eq!(
            w.post_root,
            pre.with_value_at(REFUSAL_AUDIT_EXT_KEY, refusal_audit_value(&audit))
                .unwrap()
        );
    }
}
