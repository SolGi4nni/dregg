//! Nullifier accumulator: an append-only `(nullifier → value)` map of revealed
//! nullifiers.
//!
//! When a note is spent, its nullifier is revealed and recorded here TOGETHER with the spent
//! note's value. The accumulator is therefore an auditable `(nullifier, value)` record, NOT a
//! bare set. The value is already a circuit public input (`PI[38]`), so recording it leaks
//! nothing new; unlinkability rides the nullifier derivation, not the leaf value.
//!
//! ⚑ **THE COMMITTED LEAF, 2026-07-31.** [`NullifierSet::root8`] is the exact tagged
//! LINKED-LEAF root `FNI2 ‖ addr17 ‖ value4 ‖ next17` — sixteen `u16` address limbs, four `u16`
//! value limbs, a full-width successor pointer — at depth 16, arity 4, eight BabyBear lanes. It
//! replaced `HeapLeaf::entry(fold_bytes32_to_bb(nf), split_u64(value).0)`, whose address was a
//! 256→31-bit fold (A2) and whose value was the low 30 bits (A3). See that method's own comment
//! for why the "the deployed grow-gate opens against these leaves" blocker was not real, and
//! `turn/tests/note_value_alias_at_2_30_closed.rs` for the wound it closes at the signed anchor.
//!
//! ⚠ The committed root is APPEND-ORDER dependent (it is the AAFI fold). Reconstruction must go
//! through the persisted `seq` column — [`NullifierSet::from_records`] — never by re-inserting in
//! storage order.
//!
//! Double-spend detection is checking key membership. The map also supports non-membership
//! proofs (proving a note is NOT spent) via a byte-Merkle tree over the nullifier keys (the value
//! plays no role there — only in the felt-domain [`Self::root8`], which carries its own
//! `next_addr` absence bracket).
//!
//! # Performance
//!
//! Uses `BTreeMap<Nullifier, (value, append-seq)>` internally for O(log N)
//! insert and lookup, iterating keys in sorted order. The append-seq column
//! (gap-#5 AAFI) records the canonical tau spend order (INV-6) so an
//! order-dependent AAFI root is reconstructible; see `iter_in_append_order`
//! / `from_records`.

use std::collections::BTreeMap;

use dregg_circuit::Faithful8;
use dregg_circuit::exact_nullifier_aafi::{
    EXACT_NULLIFIER_AAFI_DOMAINS, ExactLinkedDomains, exact_linked_append_root8,
};
use dregg_circuit::field::BabyBear;
use serde::{Deserialize, Serialize};

use crate::note::{NoteError, Nullifier};

/// Depth of the exact spent-nullifier tree (`4^16 = 2^32` leaves).
///
/// Projected from the circuit crate rather than re-declared, so the store and the
/// Lean-authored exact-AAFI descriptor cannot drift apart on geometry.
pub const EXACT_NULLIFIER_TREE_DEPTH: usize = dregg_circuit::exact_nullifier_aafi::TREE_DEPTH;
/// Number of BabyBear lanes in every hashed node and root.
pub const EXACT_NULLIFIER_ROOT_LANES: usize = dregg_circuit::exact_nullifier_aafi::ROOT_LANES;

/// The spend-side exact tagged-linked-leaf domain triple: `FNI2`/`FNN2`/`FNE2` — the SAME triple
/// the Lean-authored exact-AAFI descriptor constrains
/// (`Dregg2/Circuit/Emit/ExactNullifierAafiDescriptorPlan.lean`), so [`NullifierSet::root8`] is
/// the object that descriptor proves the transition of rather than a parallel one.
pub const EXACT_NULLIFIER_LINKED_DOMAINS: ExactLinkedDomains = EXACT_NULLIFIER_AAFI_DOMAINS;

fn faithful8_from_exact_lanes(lanes: [BabyBear; EXACT_NULLIFIER_ROOT_LANES]) -> Faithful8 {
    let mut bytes = [0u8; 32];
    for (lane, felt) in lanes.iter().enumerate() {
        bytes[lane * 4..lane * 4 + 4].copy_from_slice(&felt.as_u32().to_le_bytes());
    }
    // These are already canonical permutation outputs, so from_bytes32
    // recovers the same eight lanes exactly.
    Faithful8::from_bytes32(&bytes)
}

/// A stored accumulator entry: the spent-note `value` PLUS the entry's
/// **append sequence** (`seq`) — the gap-#5 AAFI (append-at-free-index)
/// order column. AAFI roots are insertion-order-dependent (the append order
/// IS the canonical tau spend sequence, INV-6), so the store persists WHERE
/// in the append sequence each entry landed; a reconstruction replays the
/// records sorted by `seq` and recovers the identical AAFI layout every time.
/// ⚑ Since 2026-07-31 [`NullifierSet::root8`] IS the AAFI fold, so `seq` is no longer an
/// additive side column: it is the committed order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct AppendRecord {
    /// The spent note's value (the circuit's `NOTE_VALUE_LO` felt source).
    value: u64,
    /// 0-based append index: this entry was the `seq`-th nullifier appended.
    /// Mirrors [`dregg_circuit::heap_root::CanonicalHeapTree8::next_free_index`]
    /// semantics — the entry with append rank `seq` occupies physical AAFI
    /// slot `seq + 1` (slot 0 is the MIN sentinel).
    seq: u64,
}

/// A Merkle membership proof for a single nullifier in the set.
///
/// This proves that a specific nullifier exists at a given position in the
/// Merkle tree built over all nullifiers. Used as part of non-membership proofs
/// to demonstrate that neighbor elements are genuinely in the set.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MerkleMembershipProof {
    /// The nullifier whose membership is being proved.
    pub element: Nullifier,
    /// Index of the element in the sorted nullifier list.
    pub index: usize,
    /// Sibling hashes along the path from the leaf to the root (bottom-up).
    pub siblings: Vec<[u8; 32]>,
}

/// A non-membership proof: demonstrates that a nullifier is NOT in the set.
///
/// Uses adjacent-neighbor technique: shows two consecutive nullifiers in the
/// sorted set that bracket the absent value, plus Merkle membership proofs for
/// each neighbor (proving they ARE in the set).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonMembershipProof {
    /// The nullifier being proved absent.
    pub absent: Nullifier,
    /// The nullifier just before the absent one (if any).
    pub left_neighbor: Option<Nullifier>,
    /// The nullifier just after the absent one (if any).
    pub right_neighbor: Option<Nullifier>,
    /// Merkle membership proof for the left neighbor (if present).
    pub left_membership_proof: Option<MerkleMembershipProof>,
    /// Merkle membership proof for the right neighbor (if present).
    pub right_membership_proof: Option<MerkleMembershipProof>,
    /// Root of the nullifier tree at the time of proof generation.
    pub root: [u8; 32],
}

/// Append-only `(nullifier → value)` accumulator of revealed nullifiers.
/// Supports efficient membership checks and non-membership proofs.
///
/// Uses `BTreeMap<Nullifier, (value, seq)>` for O(log N) insert and contains operations.
/// For non-membership proofs, the keys are materialized into a sorted vec on
/// demand (the BTreeMap iterator yields keys in sorted order). The value is the
/// spent note value carried into the circuit-faithful [`Self::root8`] leaf.
#[derive(Clone, Debug)]
pub struct NullifierSet {
    /// Every revealed nullifier mapped to its spent-note value AND its append
    /// sequence, kept in a BTreeMap for O(log N) operations and sorted-key
    /// iteration. The value is the circuit's `NOTE_VALUE_LO` felt source for
    /// the accumulator leaf; the seq is the AAFI append-order column.
    nullifiers: BTreeMap<Nullifier, AppendRecord>,
    /// The next append sequence number (0-based). Every insert records the
    /// current `next_seq` and bumps it — the store-side mirror of the AAFI
    /// tree's `next_free_index` cursor (offset by 1 for the MIN sentinel).
    next_seq: u64,
}

impl NullifierSet {
    /// Create an empty nullifier set.
    pub fn new() -> Self {
        Self {
            nullifiers: BTreeMap::new(),
            next_seq: 0,
        }
    }

    /// Number of nullifiers in the set.
    pub fn len(&self) -> usize {
        self.nullifiers.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.nullifiers.is_empty()
    }

    /// Add a nullifier with its spent-note value (note is now spent). Returns
    /// error if the nullifier is already present (double-spend).
    ///
    /// The `value` is the spent note's value — the SAME `u64` the circuit
    /// noteSpend row publishes as `NOTE_VALUE_LO`/`NOTE_VALUE_HI` and folds into
    /// the grow-gate leaf (`split_u64(value).0`); carrying it here is what keeps
    /// [`Self::root8`] byte-identical to the in-circuit accumulator across turns.
    ///
    /// O(log N) via BTreeMap insertion (does not overwrite on collision, so a
    /// double-spend never mutates the recorded value).
    pub fn insert(&mut self, nullifier: Nullifier, value: u64) -> Result<(), NoteError> {
        if self.nullifiers.contains_key(&nullifier) {
            return Err(NoteError::DoubleSpend { nullifier });
        }
        self.nullifiers.insert(
            nullifier,
            AppendRecord {
                value,
                seq: self.next_seq,
            },
        );
        self.next_seq += 1;
        Ok(())
    }

    /// Check if a nullifier is in the set (note is spent).
    ///
    /// O(log N) via BTreeMap key lookup.
    pub fn contains(&self, nullifier: &Nullifier) -> bool {
        self.nullifiers.contains_key(nullifier)
    }

    /// The spent-note value recorded for a nullifier, if present.
    pub fn value_of(&self, nullifier: &Nullifier) -> Option<u64> {
        self.nullifiers.get(nullifier).map(|r| r.value)
    }

    /// The append sequence recorded for a nullifier, if present — the 0-based
    /// rank at which it was appended (the canonical tau spend order, INV-6).
    /// This is the column a persistence layer must carry per entry so an AAFI
    /// (order-dependent) root is reconstructible; see [`Self::from_records`].
    pub fn seq_of(&self, nullifier: &Nullifier) -> Option<u64> {
        self.nullifiers.get(nullifier).map(|r| r.seq)
    }

    /// Iterate the nullifiers in sorted key order (the universal-memory projection
    /// walks the set: every spent nullifier is a present `nullifiers`-domain cell).
    pub fn iter(&self) -> impl Iterator<Item = &Nullifier> {
        self.nullifiers.keys()
    }

    /// Iterate `(nullifier, value)` pairs in sorted key order — the full
    /// accumulator record (the projection/persistence path that must carry the
    /// value to reconstruct a matching [`Self::root8`]).
    pub fn iter_with_values(&self) -> impl Iterator<Item = (&Nullifier, u64)> {
        self.nullifiers.iter().map(|(n, r)| (n, r.value))
    }

    /// Iterate the full `(nullifier, value, seq)` records **in append order**
    /// (ascending `seq`) — the canonical tau spend sequence (INV-6). This is
    /// BOTH the persistence export (each record carries its seq column) and
    /// the AAFI replay order: a reconstruction that re-applies these records
    /// in this order rebuilds the order-dependent AAFI tree identically.
    ///
    /// Ties on `seq` (impossible for records minted by [`Self::insert`], which
    /// assigns unique seqs; possible only for hand-built record sets) are
    /// broken deterministically by the nullifier key, so the order is TOTAL.
    pub fn iter_in_append_order(&self) -> impl Iterator<Item = (Nullifier, u64, u64)> {
        let mut records: Vec<(Nullifier, u64, u64)> = self
            .nullifiers
            .iter()
            .map(|(n, r)| (*n, r.value, r.seq))
            .collect();
        records.sort_by_key(|(n, _, seq)| (*seq, *n));
        records.into_iter()
    }

    /// Reconstruct the set from durable `(nullifier, value, seq)` records,
    /// **fixing the append order** from the persisted seq column: records are
    /// replayed sorted by `(seq, key)` and keep their persisted seqs verbatim,
    /// so the reconstruction is deterministic in the canonical tau order no
    /// matter what order the storage layer yields the records in. This is the
    /// AAFI-order reconstruction path — under AAFI the accumulator root
    /// depends on the append order, so "reconstruct from the store" must
    /// recover the ORIGINAL order, not the store's key order.
    ///
    /// Returns the double-spend error on a duplicate nullifier key.
    pub fn from_records(
        records: impl IntoIterator<Item = (Nullifier, u64, u64)>,
    ) -> Result<Self, NoteError> {
        let mut sorted: Vec<(Nullifier, u64, u64)> = records.into_iter().collect();
        sorted.sort_by_key(|(n, _, seq)| (*seq, *n));
        let mut set = Self::new();
        for (nullifier, value, seq) in sorted {
            if set.nullifiers.contains_key(&nullifier) {
                return Err(NoteError::DoubleSpend { nullifier });
            }
            set.nullifiers
                .insert(nullifier, AppendRecord { value, seq });
            set.next_seq = set.next_seq.max(seq + 1);
        }
        Ok(set)
    }

    /// The committed accumulator's **dense physical leaf vector** — exactly what [`Self::root8`]
    /// hashes, indexed by physical slot. Slot 0 is the permanent `BOT` sentinel; the record at
    /// append rank `r` sits at slot `r + 1`.
    ///
    /// Exposed because it is the readable form of the two properties the root has and its
    /// predecessors did not: every leaf's `value()` is the FULL recorded `u64` and every leaf's
    /// `next_addr()` is the next larger present address (the absence bracket), so a test can
    /// assert the encoding ROUND-TRIPS rather than merely that two digests differ.
    pub fn exact_dense_leaves(&self) -> Vec<dregg_circuit::exact_nullifier_aafi::ExactLinkedLeaf> {
        dregg_circuit::exact_nullifier_aafi::exact_linked_dense_leaves(&self.exact_append_records())
            .expect("the nullifier map's keys are unique and within the 4^16 tree capacity")
    }

    /// The physical AAFI slot the NEXT append would occupy: `len() + 1`
    /// (slot 0 is the MIN sentinel) — the store-side mirror of
    /// [`dregg_circuit::heap_root::CanonicalHeapTree8::next_free_index`] for a
    /// tree replayed from [`Self::exact_dense_leaves`].
    pub fn aafi_next_free_index(&self) -> usize {
        self.nullifiers.len() + 1
    }

    /// Remove a nullifier from the set.
    ///
    /// Used ONLY by the turn-journal rollback path to undo a speculative insert
    /// when a turn fails after the nullifier was recorded. Outside of rollback
    /// the set is append-only.
    ///
    /// Returns `true` if the nullifier was present and removed, `false`
    /// otherwise. O(log N) via BTreeMap remove (plus an O(N) append-cursor
    /// recompute — rollback is rare and off the hot path).
    ///
    /// The append cursor rolls back with the entry: `next_seq` is recomputed
    /// to one past the highest surviving seq, so rolling back the LAST append
    /// frees its seq and the re-executed turn's insert lands at the SAME
    /// append rank — the deterministic tau order is preserved across a
    /// speculative-insert rollback.
    pub fn remove(&mut self, nullifier: &Nullifier) -> bool {
        let removed = self.nullifiers.remove(nullifier).is_some();
        if removed {
            self.next_seq = self
                .nullifiers
                .values()
                .map(|r| r.seq + 1)
                .max()
                .unwrap_or(0);
        }
        removed
    }

    /// Get the sorted list of nullifier keys (materializes from the BTreeMap key
    /// iterator). Used internally for Merkle tree construction and non-membership
    /// proofs — the byte-Merkle machinery keys on the nullifier only.
    fn sorted_vec(&self) -> Vec<Nullifier> {
        self.nullifiers.keys().copied().collect()
    }

    /// Prove non-membership (note is NOT spent).
    /// Returns None if the nullifier IS in the set.
    pub fn prove_non_membership(&self, nullifier: &Nullifier) -> Option<NonMembershipProof> {
        if self.nullifiers.contains_key(nullifier) {
            return None; // It IS in the set, can't prove non-membership.
        }

        let sorted = self.sorted_vec();
        // Binary search in the sorted vec to find the adjacent neighbors.
        let idx = sorted.binary_search(nullifier).unwrap_err();

        let left_neighbor = if idx > 0 { Some(sorted[idx - 1]) } else { None };
        let right_neighbor = if idx < sorted.len() {
            Some(sorted[idx])
        } else {
            None
        };
        let left_membership_proof = if idx > 0 {
            Some(self.prove_membership_from_sorted(&sorted, idx - 1))
        } else {
            None
        };
        let right_membership_proof = if idx < sorted.len() {
            Some(self.prove_membership_from_sorted(&sorted, idx))
        } else {
            None
        };
        Some(NonMembershipProof {
            absent: *nullifier,
            left_neighbor,
            right_neighbor,
            left_membership_proof,
            right_membership_proof,
            root: self.root(),
        })
    }

    /// Generate a Merkle membership proof for the element at the given index
    /// in the sorted nullifier list.
    ///
    /// The Merkle tree is built over the sorted list of nullifier hashes as leaves.
    /// Each leaf is: BLAKE3("dregg-nullifier-leaf v1", nullifier).
    /// Internal nodes are: BLAKE3("dregg-nullifier-node v1", left || right).
    fn prove_membership_from_sorted(
        &self,
        sorted: &[Nullifier],
        index: usize,
    ) -> MerkleMembershipProof {
        let leaves: Vec<[u8; 32]> = sorted.iter().map(|n| Self::leaf_hash(&n.0)).collect();
        let siblings = Self::merkle_path(&leaves, index);
        MerkleMembershipProof {
            element: sorted[index],
            index,
            siblings,
        }
    }

    /// Hash a leaf node.
    fn leaf_hash(data: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-nullifier-leaf v1");
        hasher.update(data);
        *hasher.finalize().as_bytes()
    }

    /// Hash two children into a parent node.
    fn node_hash(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-nullifier-node v1");
        hasher.update(left);
        hasher.update(right);
        *hasher.finalize().as_bytes()
    }

    /// Compute the Merkle path (sibling hashes from leaf to root) for a given index.
    fn merkle_path(leaves: &[[u8; 32]], index: usize) -> Vec<[u8; 32]> {
        if leaves.len() <= 1 {
            return vec![];
        }
        let mut siblings = Vec::new();
        let mut current_level = leaves.to_vec();
        let mut idx = index;

        while current_level.len() > 1 {
            // Pad to even length with a zero hash.
            if !current_level.len().is_multiple_of(2) {
                current_level.push([0u8; 32]);
            }
            let sibling_idx = if idx.is_multiple_of(2) {
                idx + 1
            } else {
                idx - 1
            };
            siblings.push(current_level[sibling_idx]);

            // Build next level.
            let mut next_level = Vec::with_capacity(current_level.len() / 2);
            for chunk in current_level.chunks(2) {
                next_level.push(Self::node_hash(&chunk[0], &chunk[1]));
            }
            current_level = next_level;
            idx /= 2;
        }
        siblings
    }

    /// Compute the Merkle root from leaves.
    fn merkle_root_from_leaves(leaves: &[[u8; 32]]) -> [u8; 32] {
        if leaves.is_empty() {
            return [0u8; 32];
        }
        let mut current_level = leaves.to_vec();
        while current_level.len() > 1 {
            if !current_level.len().is_multiple_of(2) {
                current_level.push([0u8; 32]);
            }
            let mut next_level = Vec::with_capacity(current_level.len() / 2);
            for chunk in current_level.chunks(2) {
                next_level.push(Self::node_hash(&chunk[0], &chunk[1]));
            }
            current_level = next_level;
        }
        current_level[0]
    }

    /// Verify a Merkle membership proof against a given root.
    fn verify_membership_proof(proof: &MerkleMembershipProof, root: &[u8; 32]) -> bool {
        let mut current = Self::leaf_hash(&proof.element.0);
        let mut idx = proof.index;
        for sibling in &proof.siblings {
            if idx.is_multiple_of(2) {
                current = Self::node_hash(&current, sibling);
            } else {
                current = Self::node_hash(sibling, &current);
            }
            idx /= 2;
        }
        current == *root
    }

    /// Current root of the nullifier set (Merkle tree root over all nullifier hashes).
    ///
    /// Leaves are domain-separated hashes of each nullifier (in sorted order).
    /// Internal nodes hash their two children. This produces a proper Merkle tree
    /// that supports membership proofs for non-membership verification.
    pub fn root(&self) -> [u8; 32] {
        if self.nullifiers.is_empty() {
            return [0u8; 32];
        }
        // BTreeMap keys iterate in sorted order, matching the old Vec behavior.
        let leaves: Vec<[u8; 32]> = self
            .nullifiers
            .keys()
            .map(|n| Self::leaf_hash(&n.0))
            .collect();
        Self::merkle_root_from_leaves(&leaves)
    }

    /// The canonical APPEND-ORDERED `(raw nullifier, value)` record list — the input the
    /// committed [`Self::root8`] folds. Physical slot 0 is the permanent `BOT` sentinel; the
    /// record at rank `r` occupies slot `r + 1`.
    fn exact_append_records(&self) -> Vec<([u8; 32], u64)> {
        self.iter_in_append_order()
            .map(|(nullifier, value, _)| (nullifier.0, value))
            .collect()
    }

    /// **THE committed accumulator root of the spent-nullifier set** — the exact tagged
    /// LINKED-LEAF (indexed-Merkle) append-at-free-index root, `FNI2 ‖ addr17 ‖ value4 ‖ next17`
    /// at depth 16, arity 4, eight BabyBear lanes.
    ///
    /// ⚑ **WHAT THIS REPLACED, AND WHY THE STATED BLOCKER WAS NOT REAL.** Until 2026-07-31 this
    /// folded `HeapLeaf::entry(fold_bytes32_to_bb(nf), split_u64(value).0)` through a
    /// `CanonicalHeapTree8` — a 256→31-bit address fold (A2) and a 64→30-bit value truncation
    /// (A3) — and its doc comment said byte-for-byte agreement with the deployed noteSpend
    /// grow-gate was load-bearing, so that changing it would make every spend turn UNSAT.
    /// **It was not.** The SDK builds the grow-gate's BEFORE leaf vector itself, and does it with
    /// a hard-coded existence bit: `HeapLeaf::entry(*nf, BabyBear::new(1))` at
    /// `sdk/src/full_turn_proof.rs:397`, `:1022` and `:1135`. So this root and the in-circuit
    /// tree already disagreed whenever a spent note's `split_u64(value).0 != 1`, and on the
    /// create side `before_commitments` is always `&[]` (`sdk/src/cipherclerk.rs:5812`,
    /// `full_turn_proof.rs:422`) so the commitments root never reached a circuit at all. Nothing
    /// threads this value into a map-op, so no VK rotates and no descriptor is re-emitted.
    ///
    /// The new leaf carries the address as a tag plus sixteen little-endian `u16` limbs (`2^256`
    /// on the nose, no reduction), the value as four (`2^64`, no truncation), AND a full-width
    /// `next_addr` pointer — so it is injective in every argument *and* keeps the IMT absence
    /// bracket a non-membership opening straddles. The dense `faithful_root8_exact` this also
    /// replaced had the injectivity but no pointer, so it could not express absence.
    ///
    /// It is the `EXACT_NULLIFIER_AAFI_DOMAINS` instance of
    /// [`dregg_circuit::exact_nullifier_aafi::exact_linked_append_root8`], i.e. definitionally
    /// the root [`dregg_circuit::exact_nullifier_aafi::ExactNullifierAafi`] maintains and the
    /// Lean-authored 1274-constraint exact-AAFI descriptor proves the transition of.
    ///
    /// UNLIKE the byte-Merkle [`Self::root`] (which serves the non-membership proof machinery),
    /// this is the FELT-domain accumulator root the consensus anchor commits to.
    pub fn root8(&self) -> Faithful8 {
        let records = self.exact_append_records();
        let lanes = exact_linked_append_root8(EXACT_NULLIFIER_LINKED_DOMAINS, &records).expect(
            "the nullifier map's keys are unique by construction (a BTreeMap over all 32 raw \
             bytes, and the tagged-key encoding is injective on them), and its length is bounded \
             by the 4^16 tree capacity",
        );
        faithful8_from_exact_lanes(lanes)
    }

    /// Verify a non-membership proof against the current root.
    ///
    /// This verifies:
    /// 1. The proof's root matches the given root.
    /// 2. The neighbors (if present) are properly ordered around the absent value.
    /// 3. The neighbors are actually IN the set (via Merkle membership proofs).
    /// 4. The neighbors are adjacent (no element between them).
    pub fn verify_non_membership(proof: &NonMembershipProof, root: &[u8; 32]) -> bool {
        if proof.root != *root {
            return false;
        }

        // Check ordering: left < absent < right.
        if let Some(left) = &proof.left_neighbor
            && left.0 >= proof.absent.0
        {
            return false;
        }
        if let Some(right) = &proof.right_neighbor
            && right.0 <= proof.absent.0
        {
            return false;
        }

        // Verify the left neighbor's Merkle membership proof.
        if let Some(left) = &proof.left_neighbor {
            match &proof.left_membership_proof {
                Some(membership_proof) => {
                    if membership_proof.element != *left {
                        return false;
                    }
                    if !Self::verify_membership_proof(membership_proof, root) {
                        return false;
                    }
                }
                None => return false, // Left neighbor claimed but no membership proof
            }
        }

        // Verify the right neighbor's Merkle membership proof.
        if let Some(right) = &proof.right_neighbor {
            match &proof.right_membership_proof {
                Some(membership_proof) => {
                    if membership_proof.element != *right {
                        return false;
                    }
                    if !Self::verify_membership_proof(membership_proof, root) {
                        return false;
                    }
                }
                None => return false, // Right neighbor claimed but no membership proof
            }
        }

        // Verify adjacency: left and right neighbors must be at consecutive indices.
        if let (Some(left_proof), Some(right_proof)) =
            (&proof.left_membership_proof, &proof.right_membership_proof)
            && right_proof.index != left_proof.index + 1
        {
            return false;
        }

        true
    }
}

impl Default for NullifierSet {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::note::Note;

    fn make_nullifier(seed: u8) -> Nullifier {
        let owner = {
            let mut k = [0u8; 32];
            k[0] = seed;
            k
        };
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let randomness = [seed; 32];
        let note = Note::with_randomness(owner, fields, randomness);
        let spending_key = [seed.wrapping_add(100); 32];
        note.nullifier(&spending_key)
    }

    /// A deterministic spent-note value for a seed — distinct per nullifier so
    /// the `(nf, value)` leaves are genuinely value-carrying in the teeth below.
    fn make_value(seed: u8) -> u64 {
        1_000 + (seed as u64) * 7
    }

    #[test]
    fn test_nullifier_set_insert_and_contains() {
        let mut set = NullifierSet::new();
        let n = make_nullifier(1);

        assert!(!set.contains(&n));
        set.insert(n, make_value(1)).unwrap();
        assert!(set.contains(&n));
        assert_eq!(set.value_of(&n), Some(make_value(1)));
    }

    #[test]
    fn test_nullifier_set_double_spend_rejected() {
        let mut set = NullifierSet::new();
        let n = make_nullifier(1);

        set.insert(n, make_value(1)).unwrap();
        // A double-spend is rejected AND must not overwrite the recorded value.
        let result = set.insert(n, 999_999);
        assert_eq!(result, Err(NoteError::DoubleSpend { nullifier: n }));
        assert_eq!(set.value_of(&n), Some(make_value(1)));
    }

    #[test]
    fn test_nullifier_set_multiple_inserts() {
        let mut set = NullifierSet::new();
        for i in 0..10 {
            let n = make_nullifier(i);
            set.insert(n, make_value(i)).unwrap();
        }
        assert_eq!(set.len(), 10);

        // All should be present.
        for i in 0..10 {
            assert!(set.contains(&make_nullifier(i)));
        }
    }

    #[test]
    fn test_nullifier_set_non_membership_proof() {
        let mut set = NullifierSet::new();
        let n1 = make_nullifier(1);
        let n2 = make_nullifier(2);
        let absent = make_nullifier(3);

        set.insert(n1, make_value(1)).unwrap();
        set.insert(n2, make_value(2)).unwrap();

        // absent is not in the set.
        assert!(!set.contains(&absent));

        let proof = set.prove_non_membership(&absent).unwrap();
        let root = set.root();
        assert!(NullifierSet::verify_non_membership(&proof, &root));
    }

    #[test]
    fn test_nullifier_set_non_membership_present_returns_none() {
        let mut set = NullifierSet::new();
        let n = make_nullifier(1);
        set.insert(n, make_value(1)).unwrap();

        // Can't prove non-membership for something that IS in the set.
        assert!(set.prove_non_membership(&n).is_none());
    }

    #[test]
    fn test_nullifier_set_root_changes_on_insert() {
        let mut set = NullifierSet::new();
        let root_empty = set.root();

        set.insert(make_nullifier(1), make_value(1)).unwrap();
        let root_one = set.root();
        assert_ne!(root_empty, root_one);

        set.insert(make_nullifier(2), make_value(2)).unwrap();
        let root_two = set.root();
        assert_ne!(root_one, root_two);
    }

    /// The empty set's faithful accumulator root is the NATIVE `CanonicalHeapTree8`
    /// empty root — the value a producer must fill for a no-spend accumulator, NOT
    /// the degenerate `hash_bytes([0u8; 32])` / `[0u8; 32]` the lossy producer path
    /// still uses. This is the "empty default the circuit expects" match.
    #[test]
    fn root8_empty_is_the_bot_sentinel_tree_and_is_domain_separated() {
        use dregg_circuit::exact_nullifier_aafi::{ExactNullifierAafi, ExactTaggedKey};

        let set = NullifierSet::new();
        assert_eq!(set.len(), 0);

        // The empty accumulator is NOT an empty tree: physical slot 0 permanently holds the
        // `BOT(value=0, next=TOP)` sentinel, which is the low endpoint every absence bracket
        // straddles. Cross-checked against the exact-AAFI runtime rather than re-derived.
        let runtime = ExactNullifierAafi::new();
        assert_eq!(
            set.root8()
                .limbs()
                .map(dregg_circuit::field::BabyBear::as_u32),
            runtime.root().map(dregg_circuit::field::BabyBear::as_u32),
            "the empty committed root must BE the exact-AAFI runtime's genesis root"
        );
        let leaves = set.exact_dense_leaves();
        assert_eq!(leaves.len(), 1, "slot 0 is the permanent BOT sentinel");
        assert_eq!(leaves[0].addr(), ExactTaggedKey::Bot);
        assert_eq!(leaves[0].next_addr(), ExactTaggedKey::Top);
        assert_eq!(leaves[0].value(), 0);

        // ⚠ It is NO LONGER the native `CanonicalHeapTree8` empty root: this accumulator left
        // that (lossy, arity-3, one-felt-address) tree on 2026-07-31. Asserted rather than
        // merely stated, so a silent revert to the old fold is a red.
        assert_ne!(
            set.root8(),
            dregg_circuit::heap_root::empty_heap_root_8(),
            "the committed root is the exact linked-leaf tree, not the legacy heap tree"
        );
        // And the create-side dual's empty root differs — the domain tags, not the contents,
        // are what keep the two accumulators from replaying each other.
        assert_ne!(
            set.root8(),
            crate::commitment_set::CommitmentSet::new().root8(),
            "even the EMPTY spend/create roots must be domain-separated"
        );
    }

    /// A non-empty accumulator fills ALL 8 lanes of the committed nullifier-root
    /// group: the completion lanes (rotated limbs 67..=73, i.e. `limbs()[1..8]`) are
    /// NON-ZERO — the vacuity the lossy 1-felt fill leaves open — and the root
    /// ADVANCES on every distinct insert (the cross-node anti-replay observable: a
    /// node that accepted a spend carries a different root).
    #[test]
    fn root8_grows_nonzero_completion_lanes_and_advances() {
        use dregg_circuit::field::BabyBear;

        let mut set = NullifierSet::new();
        let empty8 = set.root8();

        set.insert(make_nullifier(1), make_value(1)).unwrap();
        let one8 = set.root8();
        assert_ne!(
            empty8, one8,
            "inserting a nullifier must ADVANCE the committed accumulator root"
        );
        assert!(
            one8.limbs()[1..8].iter().any(|f| *f != BabyBear::ZERO),
            "a non-empty accumulator's completion lanes (rotated limbs 67..=73) must \
             be NON-ZERO — the whole point of the faithful 8-felt fill"
        );

        set.insert(make_nullifier(2), make_value(2)).unwrap();
        let two8 = set.root8();
        assert_ne!(
            one8, two8,
            "a second distinct spend must again advance the root (monotone accumulator)"
        );
    }

    /// ⚑ **THE UNIFICATION TOOTH.** `root8` IS the root the exact-AAFI runtime
    /// (`dregg_circuit::exact_nullifier_aafi::ExactNullifierAafi`) maintains incrementally — the
    /// object the Lean-authored 1274-constraint exact-AAFI descriptor proves the transition of,
    /// and the object `circuit-prove::faithful_note_spend_exact_v3` publishes as
    /// `successor_nullifier_root`.
    ///
    /// Before 2026-07-31 there were THREE trees here: this set's committed `root8` (a lossy
    /// arity-3 `CanonicalHeapTree8`), its `faithful_root8_exact` dual (injective but DENSE, with
    /// no `next` pointer, so it could not express absence at all), and the exact-AAFI runtime.
    /// The middle one was what `turn/src/executor/apply.rs`'s live spend admission compared a
    /// carrier's successor root against, while the prover minted the third — two "exact" roots
    /// that never agreed. There is now one.
    #[test]
    fn root8_is_the_exact_aafi_runtime_root() {
        use dregg_circuit::exact_nullifier_aafi::ExactNullifierAafi;

        let spends = [
            (make_nullifier(7), make_value(7)),
            (make_nullifier(42), 1u64 << 40),
            (make_nullifier(99), u64::MAX),
        ];
        let mut set = NullifierSet::new();
        let mut runtime = ExactNullifierAafi::new();
        for (n, v) in &spends {
            set.insert(*n, *v).unwrap();
            runtime.insert(n.0, *v).expect("fresh key");
            assert_eq!(
                set.root8()
                    .limbs()
                    .map(dregg_circuit::field::BabyBear::as_u32),
                runtime.root().map(dregg_circuit::field::BabyBear::as_u32),
                "the committed root must track the exact-AAFI runtime at EVERY step, not \
                 only at the end"
            );
        }
        assert_eq!(
            set.len() as u64 + 1,
            runtime.count(),
            "the runtime's count is the set size plus the BOT sentinel slot"
        );

        // Non-vacuity: it is emphatically NOT the retired grow-gate encoding.
        use dregg_circuit::effect_vm::{fold_bytes32_to_bb, split_u64};
        use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};
        let legacy = CanonicalHeapTree8::new(
            spends
                .iter()
                .map(|(n, v)| HeapLeaf::entry(fold_bytes32_to_bb(&n.0), split_u64(*v).0))
                .collect(),
            HEAP_TREE_DEPTH,
        )
        .root8();
        assert_ne!(set.root8(), legacy);
    }

    /// ⚑ **ANTI-VACUITY: THE ENCODING ROUND-TRIPS.** A scrambling "fix" passes any test that
    /// only asserts two digests differ. This one asserts the committed leaf vector DECODES:
    /// every recorded nullifier comes back byte-for-byte out of `addr()`, every recorded value
    /// comes back as the full `u64` out of `value()`, and the `next_addr()` chain is the sorted
    /// linked list `BOT < k₀ < … < kₙ < TOP` — the absence bracket, present and total.
    #[test]
    fn the_committed_leaf_encoding_round_trips_and_the_bracket_chain_is_total() {
        use dregg_circuit::exact_nullifier_aafi::ExactTaggedKey;

        let spends = [
            (Nullifier([0x71; 32]), 0xfedc_ba98_7654_3210u64),
            (Nullifier([0x03; 32]), 0),
            (Nullifier([0xa4; 32]), 1u64 << 62),
            (Nullifier([0x29; 32]), u64::MAX),
        ];
        let mut set = NullifierSet::new();
        for (nf, value) in spends {
            set.insert(nf, value).unwrap();
        }

        let leaves = set.exact_dense_leaves();
        assert_eq!(leaves.len(), spends.len() + 1);

        // (a) ADDRESS + VALUE round-trip, per record, at the physical slot the record occupies.
        for (rank, (nf, value)) in spends.iter().enumerate() {
            let leaf = leaves[rank + 1];
            assert_eq!(
                leaf.addr().real_raw_bytes(),
                Some(nf.0),
                "all 32 nullifier bytes must decode back out of the committed leaf"
            );
            assert_eq!(
                leaf.value(),
                *value,
                "all 64 value bits must decode back out of the committed leaf"
            );
        }

        // (b) The pointer chain, walked in KEY order, is strictly increasing and terminates at
        //     TOP — so every absent key has exactly one bracketing leaf.
        let mut by_key: Vec<_> = leaves.clone();
        by_key.sort_by_key(|leaf| leaf.addr());
        assert_eq!(by_key[0].addr(), ExactTaggedKey::Bot);
        for window in by_key.windows(2) {
            assert!(window[0].addr() < window[1].addr());
            assert_eq!(
                window[0].next_addr(),
                window[1].addr(),
                "each leaf must point at the NEXT LARGER present address"
            );
        }
        assert_eq!(
            by_key[by_key.len() - 1].next_addr(),
            ExactTaggedKey::Top,
            "the largest present address must point at TOP"
        );
    }

    /// **The `value` is load-bearing:** two accumulators over the SAME nullifiers but
    /// DIFFERENT values fold to DIFFERENT `root8`s. This is the regression guard for
    /// the exact bug being fixed — the old `value: 1` encoding threw the value away,
    /// so a spend of nf@value=5 and nf@value=500 committed the same root, breaking
    /// cross-turn continuity with the circuit (which always inserts `NOTE_VALUE_LO`).
    #[test]
    fn root8_depends_on_the_note_value() {
        let n = make_nullifier(3);

        let mut lo = NullifierSet::new();
        lo.insert(n, 5).unwrap();

        let mut hi = NullifierSet::new();
        hi.insert(n, 500).unwrap();

        assert_ne!(
            lo.root8(),
            hi.root8(),
            "the committed accumulator root MUST depend on the spent-note value — \
             the whole point of the (nf, value) leaf (the old value:1 bug erased it)"
        );
    }

    /// **CONTINUITY tooth (INV-2), RESTATED AT THE APPEND-ORDER ROOT.** Turn N's *after*-root
    /// equals turn N+1's *before*-root over the same history.
    ///
    /// ⚠ **WHAT CHANGED, SAID PLAINLY.** The committed root used to be insertion-order
    /// INDEPENDENT (a sorted-compacted tree), and this tooth asserted continuity by re-inserting
    /// the same records in a DIFFERENT order. It is now the append-at-free-index root — the
    /// order IS the canonical tau spend sequence (INV-6) — so continuity runs through the
    /// persisted `seq` column and [`NullifierSet::from_records`], which is the path every real
    /// reconstruction takes (`persist::Store::faithful_nullifier_root`,
    /// `plan_faithful_nullifier_successor`, `node::executor_side_state_persistence`). Both poles
    /// are pinned: the record-replay reconstruction AGREES, and a naive re-insertion in a
    /// different order does NOT — which is why the seq column is load-bearing rather than
    /// decorative.
    #[test]
    fn root8_is_cross_turn_continuous_through_the_append_order() {
        let base = [
            (make_nullifier(10), make_value(10)),
            (make_nullifier(20), make_value(20)),
        ];
        let new_spend = (make_nullifier(30), make_value(30));

        // Turn N: start from S (base), insert the new spend, publish the AFTER root.
        let mut turn_n = NullifierSet::new();
        for (nf, v) in &base {
            turn_n.insert(*nf, *v).unwrap();
        }
        turn_n.insert(new_spend.0, new_spend.1).unwrap();
        let after_root_n = turn_n.root8();

        // Turn N+1: a re-executor reconstructs the history from the durable
        // `(nf, value, seq)` records, handed back in a HOSTILE (key-sorted) storage order.
        let mut records: Vec<(Nullifier, u64, u64)> = turn_n.iter_in_append_order().collect();
        records.sort_by_key(|(nf, _, _)| *nf);
        let turn_n1 = NullifierSet::from_records(records).unwrap();

        assert_eq!(
            after_root_n,
            turn_n1.root8(),
            "turn N after-root must equal turn N+1 before-root over the same history, \
             reconstructed through the persisted seq column"
        );

        // NON-VACUITY, and the statement of the semantic change: the append ORDER is bound.
        let mut reordered = NullifierSet::new();
        reordered.insert(new_spend.0, new_spend.1).unwrap();
        for (nf, v) in base.iter().rev() {
            reordered.insert(*nf, *v).unwrap();
        }
        assert_ne!(
            after_root_n,
            reordered.root8(),
            "the committed root is append-order dependent — the same SET reached by a \
             different spend sequence is a different history and commits differently"
        );
    }

    /// **A8 tooth — the append order is RECORDED:** seqs are assigned in
    /// insertion order (0, 1, 2, …) regardless of key sort order, and the
    /// append-order iteration / AAFI leaf sequence follow the INSERTION order,
    /// not the BTreeMap's sorted-key order. Non-vacuous: the keys are inserted
    /// in reverse-sorted order so the two orders genuinely differ.
    #[test]
    fn append_seq_records_insertion_order_not_key_order() {
        // Reverse-sorted insertion: sorted-key order ≠ append order.
        let mut nfs: Vec<Nullifier> = (1u8..=4).map(make_nullifier).collect();
        nfs.sort();
        nfs.reverse();

        let mut set = NullifierSet::new();
        for (i, nf) in nfs.iter().enumerate() {
            set.insert(*nf, 100 + i as u64).unwrap();
            assert_eq!(
                set.seq_of(nf),
                Some(i as u64),
                "the i-th insert must record append seq i"
            );
        }
        assert_eq!(set.aafi_next_free_index(), nfs.len() + 1);

        let append_order: Vec<Nullifier> = set.iter_in_append_order().map(|(n, _, _)| n).collect();
        assert_eq!(
            append_order, nfs,
            "append-order iteration must follow INSERTION order"
        );
        let key_order: Vec<Nullifier> = set.iter().copied().collect();
        assert_ne!(
            append_order, key_order,
            "vacuity guard: this test's insertion order must differ from \
             sorted-key order or it proves nothing"
        );

        // The committed leaf sequence follows tau order: the i-th inserted nullifier and its
        // value are at physical slot i + 1, decoded back out of the leaf.
        let leaves = set.exact_dense_leaves();
        for (i, nf) in nfs.iter().enumerate() {
            assert_eq!(leaves[i + 1].addr().real_raw_bytes(), Some(nf.0));
            assert_eq!(leaves[i + 1].value(), 100 + i as u64);
        }
    }

    /// **A8 tooth — reconstruction FIXES the append order:** records exported
    /// with their seq column and handed back in a scrambled (store/key) order
    /// reconstruct the IDENTICAL append order, AAFI leaf sequence, seqs, and
    /// (sorted-compacted) root8 — the determinism the order-dependent AAFI
    /// root needs. Also proves ADDITIVITY: root8 is unchanged by the round-trip.
    #[test]
    fn reconstruction_from_records_fixes_the_append_order() {
        let mut nfs: Vec<Nullifier> = (1u8..=5).map(make_nullifier).collect();
        nfs.sort();
        nfs.reverse();

        let mut original = NullifierSet::new();
        for (i, nf) in nfs.iter().enumerate() {
            original.insert(*nf, make_value(i as u8)).unwrap();
        }

        // Export, then scramble as a hostile storage layer would (sorted by
        // key — exactly the "DIFFERENT insertion order" reconstruction bug).
        let mut records: Vec<(Nullifier, u64, u64)> = original.iter_in_append_order().collect();
        records.sort_by_key(|(n, _, _)| *n);

        let rebuilt = NullifierSet::from_records(records).unwrap();
        assert_eq!(
            rebuilt.iter_in_append_order().collect::<Vec<_>>(),
            original.iter_in_append_order().collect::<Vec<_>>(),
            "reconstruction must recover the CANONICAL append order from the \
             persisted seq column, not the storage yield order"
        );
        assert_eq!(
            rebuilt.exact_dense_leaves(),
            original.exact_dense_leaves(),
            "the committed dense leaf vector (the order-dependent root's input) must be \
             identical after reconstruction"
        );
        for nf in &nfs {
            assert_eq!(rebuilt.seq_of(nf), original.seq_of(nf));
        }
        assert_eq!(
            rebuilt.aafi_next_free_index(),
            original.aafi_next_free_index()
        );
        assert_eq!(
            rebuilt.root8(),
            original.root8(),
            "and therefore so is the committed root — this is the reconstruction path \
             every durable replay takes"
        );
    }

    /// **A8 tooth — duplicate keys in a record set are refused** (the same
    /// double-spend gate as the live insert path).
    #[test]
    fn from_records_rejects_duplicate_keys() {
        let n = make_nullifier(1);
        match NullifierSet::from_records([(n, 5, 0), (n, 7, 1)]) {
            Err(NoteError::DoubleSpend { nullifier }) => assert_eq!(nullifier, n),
            other => panic!("duplicate key must be refused, got {other:?}"),
        }
    }

    /// **A8 tooth — rollback frees the LAST seq:** removing the most recent
    /// speculative insert rolls the append cursor back, so the re-executed
    /// turn's insert lands at the SAME append rank (deterministic tau order
    /// across rollback).
    #[test]
    fn rollback_frees_the_last_append_seq() {
        let mut set = NullifierSet::new();
        let a = make_nullifier(1);
        let b = make_nullifier(2);
        let c = make_nullifier(3);

        set.insert(a, 10).unwrap();
        set.insert(b, 20).unwrap();
        assert_eq!(set.seq_of(&b), Some(1));

        assert!(set.remove(&b)); // rollback the speculative insert
        set.insert(c, 30).unwrap();
        assert_eq!(
            set.seq_of(&c),
            Some(1),
            "the re-executed insert must reuse the rolled-back append rank"
        );
        assert_eq!(set.aafi_next_free_index(), 3);
    }

    /// The legacy committed encoding, computed here so the aliasing exhibits below name a REAL
    /// object rather than a remembered one: `HeapLeaf::entry(fold_bytes32_to_bb(nf),
    /// split_u64(value).0)` folded through a `CanonicalHeapTree8`. This is what
    /// `NullifierSet::root8` was until 2026-07-31.
    fn legacy_committed_root8(records: &[(Nullifier, u64)]) -> dregg_circuit::Faithful8 {
        use dregg_circuit::effect_vm::{fold_bytes32_to_bb, split_u64};
        use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};
        CanonicalHeapTree8::new(
            records
                .iter()
                .map(|(n, v)| HeapLeaf::entry(fold_bytes32_to_bb(&n.0), split_u64(*v).0))
                .collect(),
            HEAP_TREE_DEPTH,
        )
        .root8()
    }

    /// ⚑ **A2 CLOSED AT THE COMMITTED ROOT.** A raw high-chunk mutation by exactly the BabyBear
    /// modulus is a deterministic, zero-cost collision in the legacy `u32 mod p` address fold.
    /// The legacy committed root cannot see it; the committed root now does — and the nullifier
    /// bytes DECODE back out of the leaf, so this is a binding, not a scramble.
    ///
    /// ⚠ THE BASE MUST NOT FOLD TO ZERO. This fixture used the ALL-ZEROS nullifier until
    /// 2026-07-28, and `fold_bytes32_to_bb([0u8; 32])` is `0` — which is
    /// [`dregg_circuit::heap_root::SENTINEL_MIN`]. The aliasing property under test is unrelated
    /// to the base, so the base is simply moved off zero and pinned there.
    #[test]
    fn the_committed_root_binds_the_high_nullifier_bytes_the_legacy_fold_aliased() {
        use dregg_circuit::field::BABYBEAR_P;

        // A nonzero base, so the legacy fold lands away from the sentinel address.
        let mut base_bytes = [0u8; 32];
        base_bytes[0] = 0xA7;
        let base = Nullifier(base_bytes);
        let mut aliased_bytes = base_bytes;
        aliased_bytes[28..32].copy_from_slice(&BABYBEAR_P.to_le_bytes());
        let high_chunk_alias = Nullifier(aliased_bytes);

        assert_ne!(base, high_chunk_alias);
        assert_ne!(base.0[31], high_chunk_alias.0[31]);
        assert_eq!(
            dregg_circuit::effect_vm::fold_bytes32_to_bb(&base.0),
            dregg_circuit::effect_vm::fold_bytes32_to_bb(&high_chunk_alias.0),
            "vacuity guard: the two hostile raw nullifiers must alias in the legacy fold"
        );
        assert_ne!(
            dregg_circuit::effect_vm::fold_bytes32_to_bb(&base.0),
            dregg_circuit::field::BabyBear::ZERO,
            "vacuity guard: the base must not fold onto SENTINEL_MIN, or this test \
             measures the sentinel collision instead of the aliasing it is about"
        );

        let mut base_set = NullifierSet::new();
        base_set.insert(base, 17).unwrap();
        let mut alias_set = NullifierSet::new();
        alias_set.insert(high_chunk_alias, 17).unwrap();

        // POLE 1 — the wound, at the object that carried it.
        assert_eq!(
            legacy_committed_root8(&[(base, 17)]),
            legacy_committed_root8(&[(high_chunk_alias, 17)]),
            "vacuity guard: the LEGACY committed root really did alias these two nullifiers"
        );
        // POLE 2 — the repair, at the object that carries the commitment today.
        assert_ne!(
            base_set.root8(),
            alias_set.root8(),
            "the committed root must bind the hostile high nullifier bytes"
        );
        // ANTI-VACUITY — not a scramble: both nullifiers decode back out of their leaves.
        assert_eq!(
            base_set.exact_dense_leaves()[1].addr().real_raw_bytes(),
            Some(base.0)
        );
        assert_eq!(
            alias_set.exact_dense_leaves()[1].addr().real_raw_bytes(),
            Some(high_chunk_alias.0)
        );
    }

    /// ⚑ **A3 CLOSED AT THE COMMITTED ROOT.** Values with equal low 30 bits were identical in
    /// the legacy grow-gate leaf (`split_u64(value).0`). The committed four-`u16` value carrier
    /// binds all 64 bits — and the value ROUND-TRIPS, so the binding is a real widening.
    #[test]
    fn the_committed_root_binds_all_64_value_bits_the_legacy_leaf_erased() {
        let nullifier = Nullifier([0x5a; 32]);
        let low_value = 17u64;
        let high_value = low_value | (1u64 << 50);
        assert_eq!(
            dregg_circuit::effect_vm::split_u64(low_value).0,
            dregg_circuit::effect_vm::split_u64(high_value).0,
            "vacuity guard: values must share the legacy low-30-bit leaf value"
        );

        let mut low_set = NullifierSet::new();
        low_set.insert(nullifier, low_value).unwrap();
        let mut high_set = NullifierSet::new();
        high_set.insert(nullifier, high_value).unwrap();

        assert_eq!(
            legacy_committed_root8(&[(nullifier, low_value)]),
            legacy_committed_root8(&[(nullifier, high_value)]),
            "vacuity guard: the LEGACY committed root really did erase these high value bits"
        );
        assert_ne!(
            low_set.root8(),
            high_set.root8(),
            "the committed root must bind all 64 spent-note value bits"
        );
        assert_eq!(low_set.exact_dense_leaves()[1].value(), low_value);
        assert_eq!(high_set.exact_dense_leaves()[1].value(), high_value);
    }

    /// ⚑ **THE NON-MEMBERSHIP FORGERY THE HALF-WIDE SCHEMA ADMITS IS UNSAT HERE.**
    ///
    /// `Dregg2/Circuit/MapOpWideKeyGate.lean::halfWideLeaf_forges_absence_of_present` proves —
    /// for EVERY hash, with NO collision-resistance hypothesis — that a leaf schema which widens
    /// the ADDRESS but projects the POINTER to one felt gives the honest low leaf
    /// `<keyLo, v, keyE>` and the fabricated `<keyLo, v, ptrHi>` the SAME digest whenever `keyE`
    /// and `ptrHi` agree on that projection. The honest bracket `(keyLo, keyE)` does not contain
    /// `keyE`; the fabricated bracket `(keyLo, ptrHi)` DOES — so a prover opening the committed
    /// digest proves `keyE` ABSENT while `keyE` is a PRESENT address of the very chain that
    /// digest commits to.
    ///
    /// This is that attack, instantiated at real 32-byte keys under the deployed
    /// `fold_bytes32_to_bb` projection, against BOTH schemas:
    ///
    /// * under the retired arity-3 leaf the two leaves are BIT-IDENTICAL — the forgery is
    ///   available, and the test says so rather than assuming it; and
    /// * under the committed `FNI2 ‖ addr17 ‖ value4 ‖ next17` leaf the pointer rides all
    ///   sixteen `u16` limbs plus a tag, so the two digests DIFFER and the fabricated bracket is
    ///   not representable at the committed root.
    #[test]
    fn the_half_wide_non_membership_forgery_is_unsat_at_the_committed_leaf() {
        use dregg_circuit::effect_vm::fold_bytes32_to_bb;
        use dregg_circuit::exact_nullifier_aafi::{
            EXACT_NULLIFIER_AAFI_DOMAINS, ExactLinkedLeaf, ExactTaggedKey, LinkedLeafWire,
            exact_leaf_digest_in, u64_to_u16_le,
        };
        use dregg_circuit::field::BABYBEAR_P;

        // `key_e` and `ptr_hi` are DISTINCT 32-byte keys that collide under the one-felt
        // projection — the same `+p` high-chunk construction the A2 exhibit uses.
        let mut key_lo_bytes = [0u8; 32];
        key_lo_bytes[0] = 0x01;
        let mut key_e_bytes = [0u8; 32];
        key_e_bytes[0] = 0xA7;
        let mut ptr_hi_bytes = key_e_bytes;
        ptr_hi_bytes[28..32].copy_from_slice(&BABYBEAR_P.to_le_bytes());

        assert_ne!(
            key_e_bytes, ptr_hi_bytes,
            "the two pointers must be distinct"
        );
        assert_eq!(
            fold_bytes32_to_bb(&key_e_bytes),
            fold_bytes32_to_bb(&ptr_hi_bytes),
            "vacuity guard: the two pointers must COLLIDE under the one-felt projection, or \
             the forgery is not available under the narrow schema either"
        );
        // ⚠ At the TAGGED-KEY order the bracket actually uses (`u16`-limb lex), not byte lex —
        // the module's own KAT records that the two disagree, so testing the wrong one would
        // make this guard accidentally right.
        let (k_lo, k_e, p_hi) = (
            ExactTaggedKey::from_raw(key_lo_bytes),
            ExactTaggedKey::from_raw(key_e_bytes),
            ExactTaggedKey::from_raw(ptr_hi_bytes),
        );
        assert!(
            k_lo < k_e && k_e < p_hi,
            "vacuity guard: the fabricated bracket (keyLo, ptrHi) must be strictly WIDER than \
             the honest one (keyLo, keyE), so that it genuinely contains the present key"
        );

        // POLE 1 — THE FORGERY IS AVAILABLE UNDER THE RETIRED SCHEMA. `HeapLeaf`'s preimage is
        // `[addr, value, next_addr]`, all three projected to one felt; the honest and fabricated
        // leaves are literally equal, so no hash can tell them apart.
        {
            use dregg_circuit::heap_root::HeapLeaf;
            let honest = HeapLeaf {
                addr: fold_bytes32_to_bb(&key_lo_bytes),
                value: dregg_circuit::field::BabyBear::new(1),
                next_addr: fold_bytes32_to_bb(&key_e_bytes),
            };
            let forged = HeapLeaf {
                addr: fold_bytes32_to_bb(&key_lo_bytes),
                value: dregg_circuit::field::BabyBear::new(1),
                next_addr: fold_bytes32_to_bb(&ptr_hi_bytes),
            };
            assert_eq!(
                honest.preimage(),
                forged.preimage(),
                "the retired leaf admits the half-wide non-membership forgery: the honest and \
                 fabricated brackets share one preimage"
            );
            assert_eq!(honest.digest(), forged.digest());
        }

        // POLE 2 — THE FORGERY IS UNSAT AT THE COMMITTED LEAF.
        let decode = |addr: [u8; 32], next: [u8; 32]| {
            ExactLinkedLeaf::decode(LinkedLeafWire {
                addr: ExactTaggedKey::from_raw(addr).wire(),
                value_u16_le: u64_to_u16_le(1),
                next_addr: ExactTaggedKey::from_raw(next).wire(),
            })
            .expect("both endpoints are REAL keys")
        };
        let honest = decode(key_lo_bytes, key_e_bytes);
        let forged = decode(key_lo_bytes, ptr_hi_bytes);
        assert_ne!(
            exact_leaf_digest_in(EXACT_NULLIFIER_AAFI_DOMAINS, honest),
            exact_leaf_digest_in(EXACT_NULLIFIER_AAFI_DOMAINS, forged),
            "the committed leaf must distinguish the honest bracket from the fabricated one"
        );
        // …and the fabricated pointer is not merely a different digest, it is a different KEY:
        // the pointer decodes back to its own 32 bytes.
        assert_eq!(honest.next_addr().real_raw_bytes(), Some(key_e_bytes));
        assert_eq!(forged.next_addr().real_raw_bytes(), Some(ptr_hi_bytes));

        // POLE 3 — AND THE FORGERY DOES NOT REACH THE COMMITTED ROOT AT ALL. Building the real
        // accumulator over `{key_lo, key_e}` links `key_lo -> key_e`; there is no witness in
        // which `key_lo` points past a present key.
        let mut set = NullifierSet::new();
        set.insert(Nullifier(key_lo_bytes), 1).unwrap();
        set.insert(Nullifier(key_e_bytes), 1).unwrap();
        let leaves = set.exact_dense_leaves();
        let low = leaves
            .iter()
            .find(|leaf| leaf.addr().real_raw_bytes() == Some(key_lo_bytes))
            .expect("the low key is present");
        assert_eq!(
            low.next_addr().real_raw_bytes(),
            Some(key_e_bytes),
            "the committed low leaf brackets exactly to the next PRESENT key — the wider \
             fabricated bracket has no representative in the committed tree"
        );
    }

    /// The committed root is append-order DEPENDENT (it is the AAFI fold), and the record
    /// round-trip is what makes that deterministic. Both poles.
    #[test]
    fn the_committed_root_is_append_order_bound_and_replay_stable() {
        let records = [
            (Nullifier([0x71; 32]), 0xfedc_ba98_7654_3210u64),
            (Nullifier([0x03; 32]), 7),
            (Nullifier([0xa4; 32]), 1u64 << 63),
            (Nullifier([0x29; 32]), u64::MAX),
        ];

        let mut forward = NullifierSet::new();
        for (nullifier, value) in records {
            forward.insert(nullifier, value).unwrap();
        }
        let mut reverse = NullifierSet::new();
        for (nullifier, value) in records.into_iter().rev() {
            reverse.insert(nullifier, value).unwrap();
        }

        assert_ne!(
            forward.iter_in_append_order().collect::<Vec<_>>(),
            reverse.iter_in_append_order().collect::<Vec<_>>(),
            "vacuity guard: append histories must genuinely differ"
        );
        assert_ne!(
            forward.root8(),
            reverse.root8(),
            "two different spend SEQUENCES over the same set are two different histories"
        );

        let replayed =
            NullifierSet::from_records(forward.iter_in_append_order().collect::<Vec<_>>()).unwrap();
        assert_eq!(
            forward.root8(),
            replayed.root8(),
            "and the durable record replay reproduces the history exactly"
        );
    }

    /// The committed protocol root, pinned. Any change to the domain tags, the leaf schema, the
    /// pointer linkage, the arity or the depth moves these.
    #[test]
    fn committed_root8_protocol_kat() {
        let empty = NullifierSet::new().root8();

        let records = [
            (Nullifier([0x00; 32]), 0),
            (Nullifier([0x42; 32]), 0x0123_4567_89ab_cdef),
            (Nullifier([0xff; 32]), u64::MAX),
        ];
        let mut populated = NullifierSet::new();
        for (nullifier, value) in records {
            populated.insert(nullifier, value).unwrap();
        }
        let populated = populated.root8();

        assert_eq!(
            empty.limbs().map(BabyBear::as_u32),
            [
                1_063_616_748,
                556_571_557,
                1_365_559_798,
                676_329_831,
                237_569_590,
                816_709_115,
                331_999_350,
                706_381_556,
            ],
            "depth-16 committed empty-root KAT drift"
        );
        assert_eq!(
            populated.limbs().map(BabyBear::as_u32),
            [
                1_109_381_348,
                607_456_375,
                1_517_686_098,
                968_324_157,
                877_318_795,
                1_910_849_679,
                1_229_883_632,
                36_666_916,
            ],
            "three-record committed-root KAT drift"
        );
    }
}
