//! Commitment accumulator: an append-only `(note-commitment → value)` map of
//! created note commitments — the CREATE dual of [`crate::nullifier_set::NullifierSet`].
//!
//! When a note is created, its commitment is published and recorded here TOGETHER
//! with the created note's value — the SAME `(addr, value)` leaf the deployed
//! circuit noteCreate grow-gate inserts (`trace_rotated.rs`
//! `generate_rotated_note_create_trace_with_commitments_tree`: `HeapLeaf::entry(//! fold(commitment), split_u64(value).0)`). The accumulator is therefore an
//! auditable `(commitment, value)` record: keeping the value is what makes the
//! committed [`Self::root8`] cross-turn-continuous with the circuit (turn N's
//! after-root == turn N+1's before-root over the same leaves).
//!
//! GROW-ONLY: NoteCreate is append-only — there is NO freshness/absent precondition
//! (`trace_rotated.rs` line ~1397). A duplicate commitment is rejected (a note
//! commitment cannot be created twice), the create-side analog of the nullifier
//! double-spend gate. Unlike the nullifier set there is no non-membership-proof
//! machinery: the commitments accumulator is a pure grow-only set whose ONLY
//! committed observable is the felt-domain [`Self::root8`].
//!
//! # Performance
//!
//! Uses `BTreeMap<[u8; 32], (value, append-seq)>` internally for O(log N)
//! insert and lookup, iterating keys in sorted order. The append-seq column
//! (gap-#5 AAFI) records the canonical tau append order so an
//! order-dependent AAFI root is reconstructible; see `iter_in_append_order`
//! / `from_records`.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::note::{NoteCommitment, NoteError};

/// A stored accumulator entry: the created-note `value` PLUS the entry's
/// **append sequence** (`seq`) — the gap-#5 AAFI (append-at-free-index) order
/// column. AAFI roots are insertion-order-dependent (the append order IS the
/// canonical tau create sequence, INV-6), so the store persists WHERE in the
/// append sequence each entry landed; a reconstruction replays the records
/// sorted by `seq` and recovers the identical AAFI layout every time. The
/// sorted-compacted [`CommitmentSet::root8`] layer ignores `seq` (order-
/// independent), so this is purely ADDITIVE.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct AppendRecord {
    /// The created note's value (the circuit's `NOTE_VALUE_LO` felt source).
    value: u64,
    /// 0-based append index: this entry was the `seq`-th commitment appended.
    /// Mirrors [`dregg_circuit::heap_root::CanonicalHeapTree8::next_free_index`]
    /// semantics — the entry with append rank `seq` occupies physical AAFI
    /// slot `seq + 1` (slot 0 is the MIN sentinel).
    seq: u64,
}

/// Append-only `(note-commitment → value)` accumulator of created note commitments.
/// The CREATE dual of [`crate::nullifier_set::NullifierSet`]. GROW-ONLY: a duplicate
/// commitment is rejected.
///
/// Uses `BTreeMap<[u8; 32], (value, seq)>` for O(log N) insert and contains operations and
/// sorted-key iteration. The value is the created note value carried into the
/// circuit-faithful [`Self::root8`] leaf.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CommitmentSet {
    /// Every created note commitment mapped to its note value AND its append
    /// sequence, kept in a BTreeMap for O(log N) operations and sorted-key
    /// iteration. The value is the circuit's `NOTE_VALUE_LO` felt source for
    /// the accumulator leaf; the seq is the AAFI append-order column.
    commitments: BTreeMap<[u8; 32], AppendRecord>,
    /// The next append sequence number (0-based). Every insert records the
    /// current `next_seq` and bumps it — the store-side mirror of the AAFI
    /// tree's `next_free_index` cursor (offset by 1 for the MIN sentinel).
    next_seq: u64,
}

impl CommitmentSet {
    /// Create an empty commitment set.
    pub fn new() -> Self {
        Self {
            commitments: BTreeMap::new(),
            next_seq: 0,
        }
    }

    /// Number of commitments in the set.
    pub fn len(&self) -> usize {
        self.commitments.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.commitments.is_empty()
    }

    /// Add a note commitment with its note value (note is now created). Returns
    /// error if the commitment is already present (duplicate create).
    ///
    /// The `value` is the created note's value — the SAME `u64` the circuit
    /// noteCreate row publishes as `NOTE_VALUE_LO`/`NOTE_VALUE_HI` and folds into
    /// the grow-gate leaf (`split_u64(value).0`); carrying it here is what keeps
    /// [`Self::root8`] byte-identical to the in-circuit accumulator across turns.
    ///
    /// O(log N) via BTreeMap insertion (does not overwrite on collision).
    pub fn insert(&mut self, commitment: NoteCommitment, value: u64) -> Result<(), NoteError> {
        if self.commitments.contains_key(&commitment.0) {
            return Err(NoteError::DuplicateCommitment { commitment });
        }
        self.commitments.insert(
            commitment.0,
            AppendRecord {
                value,
                seq: self.next_seq,
            },
        );
        self.next_seq += 1;
        Ok(())
    }

    /// Check if a commitment is in the set (note is created).
    ///
    /// O(log N) via BTreeMap key lookup.
    pub fn contains(&self, commitment: &NoteCommitment) -> bool {
        self.commitments.contains_key(&commitment.0)
    }

    /// The note value recorded for a commitment, if present.
    pub fn value_of(&self, commitment: &NoteCommitment) -> Option<u64> {
        self.commitments.get(&commitment.0).map(|r| r.value)
    }

    /// The append sequence recorded for a commitment, if present — the 0-based
    /// rank at which it was appended (the canonical tau create order, INV-6).
    /// This is the column a persistence layer must carry per entry so an AAFI
    /// (order-dependent) root is reconstructible; see [`Self::from_records`].
    pub fn seq_of(&self, commitment: &NoteCommitment) -> Option<u64> {
        self.commitments.get(&commitment.0).map(|r| r.seq)
    }

    /// Iterate the commitments in sorted key order (the universal-memory projection
    /// walks the set: every created commitment is a present `commitments`-domain cell).
    pub fn iter(&self) -> impl Iterator<Item = &[u8; 32]> {
        self.commitments.keys()
    }

    /// Iterate `(commitment, value)` pairs in sorted key order — the full
    /// accumulator record (the projection/persistence path that must carry the
    /// value to reconstruct a matching [`Self::root8`]).
    pub fn iter_with_values(&self) -> impl Iterator<Item = (&[u8; 32], u64)> {
        self.commitments.iter().map(|(c, r)| (c, r.value))
    }

    /// Iterate the full `(commitment, value, seq)` records **in append order**
    /// (ascending `seq`) — the canonical tau create sequence (INV-6). This is
    /// BOTH the persistence export (each record carries its seq column) and
    /// the AAFI replay order: a reconstruction that re-applies these records
    /// in this order rebuilds the order-dependent AAFI tree identically.
    ///
    /// Ties on `seq` (impossible for records minted by [`Self::insert`], which
    /// assigns unique seqs; possible only for hand-built record sets) are
    /// broken deterministically by the commitment key, so the order is TOTAL.
    pub fn iter_in_append_order(&self) -> impl Iterator<Item = ([u8; 32], u64, u64)> {
        let mut records: Vec<([u8; 32], u64, u64)> = self
            .commitments
            .iter()
            .map(|(c, r)| (*c, r.value, r.seq))
            .collect();
        records.sort_by_key(|(c, _, seq)| (*seq, *c));
        records.into_iter()
    }

    /// Reconstruct the set from durable `(commitment, value, seq)` records,
    /// **fixing the append order** from the persisted seq column: records are
    /// replayed sorted by `(seq, key)` and keep their persisted seqs verbatim,
    /// so the reconstruction is deterministic in the canonical tau order no
    /// matter what order the storage layer yields the records in. This is the
    /// AAFI-order reconstruction path — under AAFI the accumulator root
    /// depends on the append order, so "reconstruct from the store" must
    /// recover the ORIGINAL order, not the store's key order.
    ///
    /// Returns the duplicate-commitment error on a duplicate key.
    pub fn from_records(
        records: impl IntoIterator<Item = ([u8; 32], u64, u64)>,
    ) -> Result<Self, NoteError> {
        let mut sorted: Vec<([u8; 32], u64, u64)> = records.into_iter().collect();
        sorted.sort_by_key(|(c, _, seq)| (*seq, *c));
        let mut set = Self::new();
        for (commitment, value, seq) in sorted {
            if set.commitments.contains_key(&commitment) {
                return Err(NoteError::DuplicateCommitment {
                    commitment: NoteCommitment(commitment),
                });
            }
            set.commitments
                .insert(commitment, AppendRecord { value, seq });
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
            .map(|(c, v, _)| Self::accumulator_leaf(&c, v))
            .collect()
    }

    /// The physical AAFI slot the NEXT append would occupy: `len() + 1`
    /// (slot 0 is the MIN sentinel) — the store-side mirror of
    /// [`dregg_circuit::heap_root::CanonicalHeapTree8::next_free_index`] for a
    /// tree replayed from [`Self::aafi_leaves`].
    pub fn aafi_next_free_index(&self) -> usize {
        self.commitments.len() + 1
    }

    /// Remove a commitment from the set.
    ///
    /// Used ONLY by the turn-journal rollback path to undo a speculative insert
    /// when a turn fails after the commitment was recorded. Outside of rollback
    /// the set is append-only.
    ///
    /// Returns `true` if the commitment was present and removed, `false`
    /// otherwise. O(log N) via BTreeMap remove (plus an O(N) append-cursor
    /// recompute — rollback is rare and off the hot path).
    ///
    /// The append cursor rolls back with the entry: `next_seq` is recomputed
    /// to one past the highest surviving seq, so rolling back the LAST append
    /// frees its seq and the re-executed turn's insert lands at the SAME
    /// append rank — the deterministic tau order is preserved across a
    /// speculative-insert rollback.
    pub fn remove(&mut self, commitment: &NoteCommitment) -> bool {
        let removed = self.commitments.remove(&commitment.0).is_some();
        if removed {
            self.next_seq = self
                .commitments
                .values()
                .map(|r| r.seq + 1)
                .max()
                .unwrap_or(0);
        }
        removed
    }

    /// The circuit-faithful node8 leaf for a single `(commitment, value)` — the
    /// EXACT [`dregg_circuit::heap_root::HeapLeaf`] the deployed rotated noteCreate
    /// grow-gate keys the commitments accumulator on
    /// (`trace_rotated.rs::generate_rotated_note_create_trace_with_commitments_tree`,
    /// lines ~1392/1402): `addr` is the folded commitment felt
    /// (`dregg_circuit::effect_vm::fold_bytes32_to_bb`, the SAME fold
    /// `effect_vm_bridge.rs`'s `hash_to_bb` applies to build the circuit's
    /// `Effect::NoteCreate { commitment }` param0 = `PARAM_BASE + param::NOTE_COMMITMENT`
    /// column), and `value` is the created note value folded through the circuit's
    /// `split_u64(value).0` — the identical `PARAM_BASE + param::NOTE_VALUE_LO` felt
    /// (the low 30 bits) the grow-gate reads from row 0.
    ///
    /// Byte-for-byte agreement with the grow-gate is load-bearing: the committed
    /// `commitments_root` group (rotated limb 27 lane-0 ‖ completion limbs 74..=80)
    /// is opened in-circuit against a `CanonicalHeapTree8` built from these leaves,
    /// so the executor-derived accumulator root must fold through the identical
    /// leaf encoding or the published commitment would not match the proof.
    pub fn accumulator_leaf(
        commitment: &[u8; 32],
        value: u64,
    ) -> dregg_circuit::heap_root::HeapLeaf {
        // The circuit's leaf value is `split_u64(value).0` — the low 30 bits of the note value as a
        // BabyBear (`NOTE_VALUE_LO`). Fold through the circuit's OWN helper so the encoding cannot
        // drift. The IMT `next_addr` pointer is relinked by the tree builder.
        dregg_circuit::heap_root::HeapLeaf::entry(
            dregg_circuit::effect_vm::fold_bytes32_to_bb(commitment),
            dregg_circuit::effect_vm::split_u64(value).0,
        )
    }

    /// **The faithful 8-felt (~124-bit) accumulator root of the created-commitment
    /// set** — the value that BELONGS in the committed rotated state's
    /// `commitments_root` group (limb 27 lane-0 ‖ completion limbs 74..=80), so a
    /// cross-node commitment is genuine: a node that has accepted a note-create
    /// carries a DIFFERENT `root8` than one that has not.
    ///
    /// This is the native `CanonicalHeapTree8` (arity-16 sorted-Poseidon2, depth
    /// [`dregg_circuit::heap_root::HEAP_TREE_DEPTH`]) root the deployed noteCreate
    /// grow-gate opens against — built from [`Self::accumulator_leaf`] over every
    /// `(commitment, value)` in the map, so it equals the BEFORE-tree root the
    /// grow-gate derives from `before_commitments` lane-for-lane. The empty set
    /// folds to the native empty root (`dregg_circuit::heap_root::empty_heap_root_8`).
    pub fn root8(&self) -> dregg_circuit::Faithful8 {
        let leaves: Vec<dregg_circuit::heap_root::HeapLeaf> = self
            .commitments
            .iter()
            .map(|(c, r)| Self::accumulator_leaf(c, r.value))
            .collect();
        dregg_circuit::heap_root::CanonicalHeapTree8::new(
            leaves,
            dregg_circuit::heap_root::HEAP_TREE_DEPTH,
        )
        .root8()
    }
}

impl Default for CommitmentSet {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_commitment(seed: u8) -> NoteCommitment {
        let mut c = [0u8; 32];
        c[0] = seed;
        c[1] = seed.wrapping_mul(3).wrapping_add(1);
        NoteCommitment(c)
    }

    /// A deterministic created-note value for a seed — distinct per commitment so
    /// the `(commitment, value)` leaves are genuinely value-carrying.
    fn make_value(seed: u8) -> u64 {
        2_000 + (seed as u64) * 11
    }

    #[test]
    fn test_commitment_set_insert_and_contains() {
        let mut set = CommitmentSet::new();
        let c = make_commitment(1);

        assert!(!set.contains(&c));
        set.insert(c, make_value(1)).unwrap();
        assert!(set.contains(&c));
        assert_eq!(set.value_of(&c), Some(make_value(1)));
    }

    #[test]
    fn test_commitment_set_duplicate_rejected() {
        let mut set = CommitmentSet::new();
        let c = make_commitment(1);

        set.insert(c, make_value(1)).unwrap();
        // A duplicate create is rejected AND must not overwrite the recorded value.
        let result = set.insert(c, 999_999);
        assert_eq!(
            result,
            Err(NoteError::DuplicateCommitment { commitment: c })
        );
        assert_eq!(set.value_of(&c), Some(make_value(1)));
    }

    #[test]
    fn test_commitment_set_multiple_inserts() {
        let mut set = CommitmentSet::new();
        for i in 0..10 {
            set.insert(make_commitment(i), make_value(i)).unwrap();
        }
        assert_eq!(set.len(), 10);
        for i in 0..10 {
            assert!(set.contains(&make_commitment(i)));
        }
    }

    #[test]
    fn test_commitment_set_remove_rollback() {
        let mut set = CommitmentSet::new();
        let c = make_commitment(1);
        set.insert(c, make_value(1)).unwrap();
        assert!(set.remove(&c));
        assert!(!set.contains(&c));
        // Re-insertable after rollback (the set is grow-only outside rollback).
        set.insert(c, make_value(1)).unwrap();
        assert!(set.contains(&c));
    }

    /// The empty set's faithful accumulator root is the NATIVE `CanonicalHeapTree8`
    /// empty root — the value a producer must fill for a no-create accumulator.
    #[test]
    fn root8_empty_matches_native_empty_heap_root_8() {
        let set = CommitmentSet::new();
        assert_eq!(
            set.root8(),
            dregg_circuit::heap_root::empty_heap_root_8(),
            "an empty commitment set must fold to the native empty node8 root the \
             circuit's noteCreate grow-gate defaults to"
        );
    }

    /// A non-empty accumulator fills ALL 8 lanes of the committed commitments-root
    /// group: the completion lanes (rotated limbs 74..=80) are NON-ZERO and the root
    /// ADVANCES on every distinct insert (the cross-node observable).
    #[test]
    fn root8_grows_nonzero_completion_lanes_and_advances() {
        use dregg_circuit::field::BabyBear;

        let mut set = CommitmentSet::new();
        let empty8 = set.root8();

        set.insert(make_commitment(1), make_value(1)).unwrap();
        let one8 = set.root8();
        assert_ne!(
            empty8, one8,
            "inserting a commitment must ADVANCE the committed accumulator root"
        );
        assert!(
            one8.limbs()[1..8].iter().any(|f| *f != BabyBear::ZERO),
            "a non-empty accumulator's completion lanes (rotated limbs 74..=80) must \
             be NON-ZERO — the whole point of the faithful 8-felt fill"
        );

        set.insert(make_commitment(2), make_value(2)).unwrap();
        let two8 = set.root8();
        assert_ne!(
            one8, two8,
            "a second distinct create must again advance the root (monotone accumulator)"
        );
    }

    /// **Encoding-match tooth:** `root8` over the set equals a `CanonicalHeapTree8`
    /// built by REPRODUCING the deployed grow-gate's exact after-tree construction
    /// from `trace_rotated.rs` (`generate_rotated_note_create_trace_with_commitments_tree`):
    /// each inserted leaf is `HeapLeaf::entry(fold_bytes32_to_bb(cm), /// split_u64(value).0)`. Both are folded through the circuit's OWN helpers, so
    /// this is genuine byte-identity with the grow-gate.
    #[test]
    fn root8_matches_growgate_after_tree_encoding() {
        use dregg_circuit::effect_vm::{fold_bytes32_to_bb, split_u64};
        use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};

        let creates = [
            (make_commitment(7), make_value(7)),
            (make_commitment(42), make_value(42)),
            (make_commitment(99), make_value(99)),
        ];
        let mut set = CommitmentSet::new();
        for (c, v) in &creates {
            set.insert(*c, *v).unwrap();
        }

        let growgate_leaves: Vec<HeapLeaf> = creates
            .iter()
            .map(|(c, v)| HeapLeaf::entry(fold_bytes32_to_bb(&c.0), split_u64(*v).0))
            .collect();
        let expected = CanonicalHeapTree8::new(growgate_leaves, HEAP_TREE_DEPTH).root8();

        assert_eq!(
            set.root8(),
            expected,
            "root8 must fold through the EXACT (addr, value) node8 leaf encoding the \
             deployed noteCreate grow-gate inserts"
        );
    }

    /// **The `value` is load-bearing:** two accumulators over the SAME commitment but
    /// DIFFERENT values fold to DIFFERENT `root8`s — the value column is genuinely
    /// bound into the committed root (the circuit always inserts `NOTE_VALUE_LO`).
    #[test]
    fn root8_depends_on_the_note_value() {
        let c = make_commitment(3);

        let mut lo = CommitmentSet::new();
        lo.insert(c, 5).unwrap();

        let mut hi = CommitmentSet::new();
        hi.insert(c, 500).unwrap();

        assert_ne!(
            lo.root8(),
            hi.root8(),
            "the committed accumulator root MUST depend on the created-note value"
        );
    }

    /// **CONTINUITY tooth:** turn N's *after*-root over `S ∪ {cm, value}` equals turn
    /// N+1's *before*-root over the same set (insertion-order-independent — a
    /// BTreeMap sorts).
    #[test]
    fn root8_is_cross_turn_continuous() {
        let base = [
            (make_commitment(10), make_value(10)),
            (make_commitment(20), make_value(20)),
        ];
        let new_create = (make_commitment(30), make_value(30));

        let mut turn_n = CommitmentSet::new();
        for (c, v) in &base {
            turn_n.insert(*c, *v).unwrap();
        }
        turn_n.insert(new_create.0, new_create.1).unwrap();
        let after_root_n = turn_n.root8();

        let mut turn_n1 = CommitmentSet::new();
        turn_n1.insert(new_create.0, new_create.1).unwrap();
        for (c, v) in base.iter().rev() {
            turn_n1.insert(*c, *v).unwrap();
        }
        let before_root_n1 = turn_n1.root8();

        assert_eq!(
            after_root_n, before_root_n1,
            "turn N after-root must equal turn N+1 before-root over the same \
             (commitment, value) set (INV-2 continuity, insertion-order-independent)"
        );
    }

    /// **A8 tooth — the append order is RECORDED:** seqs are assigned in
    /// insertion order regardless of key sort order, and the append-order
    /// iteration / AAFI leaf sequence follow the INSERTION order. Non-vacuous:
    /// the keys are inserted in reverse-sorted order so the orders differ.
    #[test]
    fn append_seq_records_insertion_order_not_key_order() {
        let mut cms: Vec<NoteCommitment> = (1u8..=4).map(make_commitment).collect();
        cms.sort_by_key(|c| c.0);
        cms.reverse();

        let mut set = CommitmentSet::new();
        for (i, cm) in cms.iter().enumerate() {
            set.insert(*cm, 100 + i as u64).unwrap();
            assert_eq!(
                set.seq_of(cm),
                Some(i as u64),
                "the i-th insert must record append seq i"
            );
        }
        assert_eq!(set.aafi_next_free_index(), cms.len() + 1);

        let append_order: Vec<[u8; 32]> = set.iter_in_append_order().map(|(c, _, _)| c).collect();
        let inserted_order: Vec<[u8; 32]> = cms.iter().map(|c| c.0).collect();
        assert_eq!(
            append_order, inserted_order,
            "append-order iteration must follow INSERTION order"
        );
        let key_order: Vec<[u8; 32]> = set.iter().copied().collect();
        assert_ne!(
            append_order, key_order,
            "vacuity guard: insertion order must differ from sorted-key order"
        );

        let expected_leaves: Vec<dregg_circuit::heap_root::HeapLeaf> = cms
            .iter()
            .enumerate()
            .map(|(i, cm)| CommitmentSet::accumulator_leaf(&cm.0, 100 + i as u64))
            .collect();
        assert_eq!(set.aafi_leaves(), expected_leaves);
    }

    /// **A8 tooth — reconstruction FIXES the append order:** records exported
    /// with their seq column and handed back sorted by KEY (the hostile
    /// storage order) reconstruct the IDENTICAL append order, AAFI leaf
    /// sequence, seqs, and (sorted-compacted) root8.
    #[test]
    fn reconstruction_from_records_fixes_the_append_order() {
        let mut cms: Vec<NoteCommitment> = (1u8..=5).map(make_commitment).collect();
        cms.sort_by_key(|c| c.0);
        cms.reverse();

        let mut original = CommitmentSet::new();
        for (i, cm) in cms.iter().enumerate() {
            original.insert(*cm, make_value(i as u8)).unwrap();
        }

        let mut records: Vec<([u8; 32], u64, u64)> = original.iter_in_append_order().collect();
        records.sort_by_key(|(c, _, _)| *c);

        let rebuilt = CommitmentSet::from_records(records).unwrap();
        assert_eq!(
            rebuilt.iter_in_append_order().collect::<Vec<_>>(),
            original.iter_in_append_order().collect::<Vec<_>>(),
            "reconstruction must recover the CANONICAL append order from the \
             persisted seq column, not the storage yield order"
        );
        assert_eq!(rebuilt.aafi_leaves(), original.aafi_leaves());
        for cm in &cms {
            assert_eq!(rebuilt.seq_of(cm), original.seq_of(cm));
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
    /// duplicate-create gate as the live insert path).
    #[test]
    fn from_records_rejects_duplicate_keys() {
        let c = make_commitment(1);
        match CommitmentSet::from_records([(c.0, 5, 0), (c.0, 7, 1)]) {
            Err(NoteError::DuplicateCommitment { commitment }) => assert_eq!(commitment, c),
            other => panic!("duplicate key must be refused, got {other:?}"),
        }
    }

    /// **A8 tooth — rollback frees the LAST seq:** removing the most recent
    /// speculative insert rolls the append cursor back, so the re-executed
    /// turn's insert lands at the SAME append rank.
    #[test]
    fn rollback_frees_the_last_append_seq() {
        let mut set = CommitmentSet::new();
        let a = make_commitment(1);
        let b = make_commitment(2);
        let c = make_commitment(3);

        set.insert(a, 10).unwrap();
        set.insert(b, 20).unwrap();
        assert_eq!(set.seq_of(&b), Some(1));

        assert!(set.remove(&b));
        set.insert(c, 30).unwrap();
        assert_eq!(
            set.seq_of(&c),
            Some(1),
            "the re-executed insert must reuse the rolled-back append rank"
        );
        assert_eq!(set.aafi_next_free_index(), 3);
    }
}
