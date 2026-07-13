//! Nullifier accumulator: an append-only `(nullifier → value)` map of revealed
//! nullifiers.
//!
//! When a note is spent, its nullifier is revealed and recorded here TOGETHER
//! with the spent note's value — the SAME `(addr, value)` leaf the deployed
//! circuit noteSpend grow-gate inserts (`trace_rotated.rs`
//! `generate_rotated_note_spend_trace_with_nullifier_tree`: `HeapLeaf::entry(//! fold(nf), NOTE_VALUE_LO)`). The accumulator is therefore an auditable
//! `(nullifier, value)` record, NOT a bare set: keeping the value is what makes
//! the committed [`Self::root8`] cross-turn-continuous with the circuit (turn
//! N's after-root == turn N+1's before-root over the same leaves). The value is
//! already a circuit public input (`PI[38]`), so recording it leaks nothing new;
//! unlinkability rides the nullifier derivation, not the leaf value.
//!
//! Double-spend detection is checking key membership. The map also supports
//! non-membership proofs (proving a note is NOT spent) via a Merkle tree over
//! the nullifier keys (the value plays no role in the byte-Merkle
//! non-membership machinery — only in the felt-domain [`Self::root8`]).
//!
//! # Performance
//!
//! Uses `BTreeMap<Nullifier, (value, append-seq)>` internally for O(log N)
//! insert and lookup, iterating keys in sorted order. The append-seq column
//! (gap-#5 AAFI) records the canonical tau spend order (INV-6) so an
//! order-dependent AAFI root is reconstructible; see `iter_in_append_order`
//! / `from_records`.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::note::{NoteError, Nullifier};

/// A stored accumulator entry: the spent-note `value` PLUS the entry's
/// **append sequence** (`seq`) — the gap-#5 AAFI (append-at-free-index)
/// order column. AAFI roots are insertion-order-dependent (the append order
/// IS the canonical tau spend sequence, INV-6), so the store persists WHERE
/// in the append sequence each entry landed; a reconstruction replays the
/// records sorted by `seq` and recovers the identical AAFI layout every time.
/// The sorted-compacted [`NullifierSet::root8`] layer ignores `seq` entirely
/// (order-independent), so this is purely ADDITIVE.
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

    /// The circuit-faithful accumulator leaves **in append order** — the
    /// canonical tau sequence of [`Self::accumulator_leaf`]s an AAFI
    /// (append-at-free-index) fold consumes. Each leaf at rank `r` here is the
    /// one an AAFI replay appends at physical slot `r + 1` (slot 0 is the MIN
    /// sentinel), mirroring `CanonicalHeapTree8::insert_witness_aafi`'s
    /// `next_free_index` semantics. The sorted-compacted [`Self::root8`] is
    /// untouched by this — same leaf SET, append positions instead of sorted.
    pub fn aafi_leaves(&self) -> Vec<dregg_circuit::heap_root::HeapLeaf> {
        self.iter_in_append_order()
            .map(|(n, v, _)| Self::accumulator_leaf(&n.0, v))
            .collect()
    }

    /// The physical AAFI slot the NEXT append would occupy: `len() + 1`
    /// (slot 0 is the MIN sentinel) — the store-side mirror of
    /// [`dregg_circuit::heap_root::CanonicalHeapTree8::next_free_index`] for a
    /// tree replayed from [`Self::aafi_leaves`].
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

    /// The circuit-faithful node8 leaf for a single `(nullifier, value)` — the
    /// EXACT [`dregg_circuit::heap_root::HeapLeaf`] the deployed rotated noteSpend
    /// grow-gate keys the nullifier accumulator on
    /// (`trace_rotated.rs::generate_rotated_note_spend_trace_with_nullifier_tree`,
    /// lines ~1204/1225): `addr` is the folded nullifier felt
    /// (`dregg_circuit::effect_vm::fold_bytes32_to_bb`, the SAME `nullifier_to_field`
    /// fold the freshness path / `DslRevocationTree` use — matching the spend row's
    /// `PARAM_BASE + param::NULLIFIER` column), and `value` is the spent note value
    /// folded through the circuit's `split_u64(value).0` — the identical
    /// `PARAM_BASE + param::NOTE_VALUE_LO` felt (the low 30 bits) the grow-gate reads
    /// from row 0.
    ///
    /// Byte-for-byte agreement with the grow-gate is load-bearing: the committed
    /// `nullifier_root` group (rotated limb 26 lane-0 ‖ completion limbs 67..=73)
    /// is opened in-circuit against a `CanonicalHeapTree8` built from these leaves,
    /// so the executor-derived accumulator root must fold through the identical
    /// leaf encoding or the published commitment would not match the proof. The
    /// prior `value: 1` existence-bit encoding was the Rust-side incoherence this
    /// fixes: the circuit always inserted `value = NOTE_VALUE_LO`, so `value: 1`
    /// made turn N's after-root ≠ turn N+1's before-root.
    pub fn accumulator_leaf(
        nullifier: &[u8; 32],
        value: u64,
    ) -> dregg_circuit::heap_root::HeapLeaf {
        // The circuit's leaf value is `split_u64(value).0` — the low 30 bits of the note value as a
        // BabyBear (`NOTE_VALUE_LO`). Fold through the circuit's OWN helper so the encoding cannot
        // drift. The IMT `next_addr` pointer is relinked by the tree builder.
        dregg_circuit::heap_root::HeapLeaf::entry(
            dregg_circuit::effect_vm::fold_bytes32_to_bb(nullifier),
            dregg_circuit::effect_vm::split_u64(value).0,
        )
    }

    /// **The faithful 8-felt (~124-bit) accumulator root of the spent-nullifier
    /// set** — the value that BELONGS in the committed rotated state's
    /// `nullifier_root` group (limb 26 lane-0 ‖ completion limbs 67..=73), so a
    /// cross-node anti-replay commitment is genuine: a node that has accepted a
    /// spend carries a DIFFERENT `root8` than one that has not.
    ///
    /// This is the native `CanonicalHeapTree8` (arity-16 sorted-Poseidon2, depth
    /// [`dregg_circuit::heap_root::HEAP_TREE_DEPTH`]) root the deployed noteSpend
    /// grow-gate opens against — built from [`Self::accumulator_leaf`] over every
    /// `(nullifier, value)` in the map, so it equals the BEFORE-tree root the SDK
    /// derives from `previously_spent` (`full_turn_proof::wide_commit_anchors`)
    /// lane-for-lane. The empty set folds to the native empty root
    /// (`dregg_circuit::heap_root::empty_heap_root_8`), NOT the degenerate
    /// `hash_bytes([0u8; 32])` / `[0u8; 32]` the producer path still fills.
    ///
    /// UNLIKE the byte-Merkle [`Self::root`] (which serves the non-membership
    /// proof machinery), this is the FELT-domain accumulator root the rotated
    /// circuit commits to.
    pub fn root8(&self) -> dregg_circuit::Faithful8 {
        let leaves: Vec<dregg_circuit::heap_root::HeapLeaf> = self
            .nullifiers
            .iter()
            .map(|(n, r)| Self::accumulator_leaf(&n.0, r.value))
            .collect();
        dregg_circuit::heap_root::CanonicalHeapTree8::new(
            leaves,
            dregg_circuit::heap_root::HEAP_TREE_DEPTH,
        )
        .root8()
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
    fn root8_empty_matches_native_empty_heap_root_8() {
        let set = NullifierSet::new();
        assert_eq!(
            set.root8(),
            dregg_circuit::heap_root::empty_heap_root_8(),
            "an empty nullifier set must fold to the native empty node8 root the \
             circuit's nullifier grow-gate defaults to"
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

    /// **Encoding-match tooth (the load-bearing differential):** `root8` over the
    /// set equals a `CanonicalHeapTree8` built by REPRODUCING the deployed grow-gate's
    /// exact after-tree construction from `trace_rotated.rs`
    /// (`generate_rotated_note_spend_trace_with_nullifier_tree`, lines ~1204/1225):
    /// each inserted leaf is `HeapLeaf::entry(<spend row NULLIFIER col>, /// <spend row NOTE_VALUE_LO col>)`, where the NULLIFIER column is
    /// `fold_bytes32_to_bb(nf)` (what the executor threads as `Effect::NoteSpend.nullifier`)
    /// and NOTE_VALUE_LO is `split_u64(value).0`. Both are folded through the
    /// circuit's OWN `fold_bytes32_to_bb`/`split_u64` helpers, so this is genuine
    /// byte-identity with the grow-gate, not a re-assertion of a private formula.
    /// A drift in this encoding would publish a root the in-circuit open cannot match.
    #[test]
    fn root8_matches_growgate_after_tree_encoding() {
        use dregg_circuit::effect_vm::{fold_bytes32_to_bb, split_u64};
        use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};

        let spends = [
            (make_nullifier(7), make_value(7)),
            (make_nullifier(42), make_value(42)),
            (make_nullifier(99), make_value(99)),
        ];
        let mut set = NullifierSet::new();
        for (n, v) in &spends {
            set.insert(*n, *v).unwrap();
        }

        // The grow-gate's after-tree encoding, reconstructed EXACTLY as
        // `generate_rotated_note_spend_trace_with_nullifier_tree` builds it: the
        // spend row's `nf_key = trace[0][PARAM_BASE + NULLIFIER]` (= fold(nf)) and
        // `nf_value = trace[0][PARAM_BASE + NOTE_VALUE_LO]` (= split_u64(value).0).
        let growgate_leaves: Vec<HeapLeaf> = spends
            .iter()
            .map(|(n, v)| HeapLeaf::entry(fold_bytes32_to_bb(&n.0), split_u64(*v).0))
            .collect();
        let expected = CanonicalHeapTree8::new(growgate_leaves, HEAP_TREE_DEPTH).root8();

        assert_eq!(
            set.root8(),
            expected,
            "root8 must fold through the EXACT (addr, value) node8 leaf encoding the \
             deployed noteSpend grow-gate inserts"
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

    /// **CONTINUITY tooth (INV-2):** turn N's *after*-root over `S ∪ {nf, value}`
    /// equals turn N+1's *before*-root over the same set — the property the old
    /// `value: 1` encoding broke. We model it exactly: the set AFTER inserting a new
    /// spend on turn N is byte-identical to the set a turn N+1 re-executor rebuilds
    /// from the same `(nf, value)` records (order-independent — a BTreeMap sorts).
    #[test]
    fn root8_is_cross_turn_continuous() {
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

        // Turn N+1: a re-executor reconstructs S ∪ {new_spend} from the durable
        // (nf, value) records — here in a DIFFERENT insertion order — and reads its
        // BEFORE root. It must equal turn N's after-root.
        let mut turn_n1 = NullifierSet::new();
        turn_n1.insert(new_spend.0, new_spend.1).unwrap();
        for (nf, v) in base.iter().rev() {
            turn_n1.insert(*nf, *v).unwrap();
        }
        let before_root_n1 = turn_n1.root8();

        assert_eq!(
            after_root_n, before_root_n1,
            "turn N after-root must equal turn N+1 before-root over the same \
             (nf, value) set (INV-2 continuity, insertion-order-independent)"
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

        // The AAFI leaf sequence is the accumulator leaves in tau order.
        let expected_leaves: Vec<dregg_circuit::heap_root::HeapLeaf> = nfs
            .iter()
            .enumerate()
            .map(|(i, nf)| NullifierSet::accumulator_leaf(&nf.0, 100 + i as u64))
            .collect();
        assert_eq!(set.aafi_leaves(), expected_leaves);
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
            rebuilt.aafi_leaves(),
            original.aafi_leaves(),
            "the AAFI leaf sequence (the order-dependent root's input) must be \
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
            "ADDITIVE: the sorted-compacted root8 lineage is untouched"
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
}
