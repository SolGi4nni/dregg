//! Commitment accumulator: an append-only `(note-commitment → value)` map of
//! created note commitments — the CREATE dual of [`crate::nullifier_set::NullifierSet`].
//!
//! When a note is created, its commitment is published and recorded here TOGETHER with the
//! created note's value. The accumulator is therefore an auditable `(commitment, value)` record.
//!
//! ⚑ **THE COMMITTED LEAF, 2026-07-31.** [`CommitmentSet::root8`] is the exact tagged
//! LINKED-LEAF root `FCI2 ‖ addr17 ‖ value4 ‖ next17` — sixteen `u16` address limbs, four `u16`
//! value limbs, a full-width successor pointer — at depth 16, arity 4, eight BabyBear lanes,
//! domain-separated from the spend-side dual. It replaced
//! `HeapLeaf::entry(fold_bytes32_to_bb(commitment), split_u64(value).0)` (A2 + A3).
//!
//! ⚠ The committed root is APPEND-ORDER dependent (it is the AAFI fold). Reconstruction must go
//! through the persisted `seq` column — [`CommitmentSet::from_records`].
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

use dregg_circuit::Faithful8;
use dregg_circuit::exact_nullifier_aafi::{ExactLinkedDomains, exact_linked_append_root8};
use dregg_circuit::field::BabyBear;
use serde::{Deserialize, Serialize};

use crate::note::{NoteCommitment, NoteError};

/// Depth of the exact created-commitment tree (`4^16 = 2^32` leaves) — the same
/// fixed geometry as the spent-nullifier dual
/// (`crate::nullifier_set::EXACT_NULLIFIER_TREE_DEPTH`), so the root shape is
/// protocol data rather than a function of the current set size.
pub const EXACT_COMMITMENT_TREE_DEPTH: usize = dregg_circuit::exact_nullifier_aafi::TREE_DEPTH;
/// Number of BabyBear lanes in every hashed node and root.
pub const EXACT_COMMITMENT_ROOT_LANES: usize = dregg_circuit::exact_nullifier_aafi::ROOT_LANES;

/// The create-side exact tagged-linked-leaf domain triple: `FCI2`/`FCN2`/`FCE2`.
///
/// Deliberately DISTINCT from the spend side's `FNI2`/`FNN2`/`FNE2`
/// ([`crate::nullifier_set::EXACT_NULLIFIER_LINKED_DOMAINS`]): a created commitment and a spent
/// nullifier are different statements about different sets, and a shared domain would let one
/// tree's leaf digest — or its EMPTY root — be replayed as the other's.
///
/// ⚠ These are NEW tags, not the retired `FCL8`/`FCN8`/`FCE8`. The leaf SCHEMA changed (an
/// arity-20 `(key16, value4)` preimage became the arity-39 `dom ‖ addr17 ‖ value4 ‖ next17`
/// linked leaf), and reusing a tag across a schema change is exactly how an old-schema digest
/// gets replayed as a new-schema one.
pub const EXACT_COMMITMENT_LINKED_DOMAINS: ExactLinkedDomains = ExactLinkedDomains {
    leaf: 0x4643_4932,  // `FCI2`
    node: 0x4643_4e32,  // `FCN2`
    empty: 0x4643_4532, // `FCE2`
};

fn faithful8_from_exact_lanes(lanes: [BabyBear; EXACT_COMMITMENT_ROOT_LANES]) -> Faithful8 {
    let mut bytes = [0u8; 32];
    for (lane, felt) in lanes.iter().enumerate() {
        bytes[lane * 4..lane * 4 + 4].copy_from_slice(&felt.as_u32().to_le_bytes());
    }
    // These are already canonical permutation outputs, so `from_bytes32`
    // recovers the same eight lanes exactly.
    Faithful8::from_bytes32(&bytes)
}

/// A stored accumulator entry: the created-note `value` PLUS the entry's
/// **append sequence** (`seq`) — the gap-#5 AAFI (append-at-free-index) order
/// column. AAFI roots are insertion-order-dependent (the append order IS the
/// canonical tau create sequence, INV-6), so the store persists WHERE in the
/// append sequence each entry landed; a reconstruction replays the records
/// sorted by `seq` and recovers the identical AAFI layout every time. The
/// ⚑ Since 2026-07-31 [`CommitmentSet::root8`] IS the AAFI fold, so `seq` is no longer an
/// additive side column: it is the committed order.
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

    /// The canonical APPEND-ORDERED `(raw commitment, value)` record list — the input the
    /// committed [`Self::root8`] folds. Physical slot 0 is the permanent `BOT` sentinel; the
    /// record at rank `r` occupies slot `r + 1`.
    fn exact_append_records(&self) -> Vec<([u8; 32], u64)> {
        self.iter_in_append_order()
            .map(|(commitment, value, _)| (commitment, value))
            .collect()
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
            .expect("the commitment map's keys are unique and within the 4^16 tree capacity")
    }

    /// The physical AAFI slot the NEXT append would occupy: `len() + 1`
    /// (slot 0 is the MIN sentinel) — the store-side mirror of
    /// [`dregg_circuit::heap_root::CanonicalHeapTree8::next_free_index`] for a
    /// tree replayed from [`Self::exact_dense_leaves`].
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

    /// **THE committed accumulator root of the created-commitment set** — the exact tagged
    /// LINKED-LEAF (indexed-Merkle) append-at-free-index root, `FCI2 ‖ addr17 ‖ value4 ‖ next17`
    /// at depth 16, arity 4, eight BabyBear lanes. The CREATE dual of
    /// [`crate::nullifier_set::NullifierSet::root8`], domain-separated from it.
    ///
    /// ⚑ **WHAT THIS REPLACED, AND WHY THE STATED BLOCKER WAS NOT REAL.** Until 2026-07-31 this
    /// folded `HeapLeaf::entry(fold_bytes32_to_bb(commitment), split_u64(value).0)` through a
    /// `CanonicalHeapTree8` — a 256→31-bit address fold (A2) and a 64→30-bit value truncation
    /// (A3) — and its doc comment said byte-for-byte agreement with the deployed noteCreate
    /// grow-gate was load-bearing. **It was not.** No caller anywhere threads a non-empty
    /// `before_commitments` into that grow-gate: `sdk/src/full_turn_proof.rs:422` and
    /// `sdk/src/cipherclerk.rs:5812` both pass `&[]`, the latter saying so outright ("This path
    /// threads no commitments-set context, so the empty set is the grow-gate's BEFORE"). This
    /// root has never reached a circuit. Nothing threads it into a map-op, so no VK rotates and
    /// no descriptor is re-emitted.
    ///
    /// The new leaf carries the address as a tag plus sixteen little-endian `u16` limbs (`2^256`
    /// on the nose, no reduction), the value as four (`2^64`, no truncation), AND a full-width
    /// `next_addr` pointer — so it is injective in every argument *and* keeps the IMT absence
    /// bracket a non-membership opening straddles.
    pub fn root8(&self) -> Faithful8 {
        let records = self.exact_append_records();
        let lanes = exact_linked_append_root8(EXACT_COMMITMENT_LINKED_DOMAINS, &records).expect(
            "the commitment map's keys are unique by construction (a BTreeMap over all 32 raw \
             bytes, and the tagged-key encoding is injective on them), and its length is bounded \
             by the 4^16 tree capacity",
        );
        faithful8_from_exact_lanes(lanes)
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
    fn root8_empty_is_the_bot_sentinel_tree_and_is_domain_separated() {
        use dregg_circuit::exact_nullifier_aafi::ExactTaggedKey;

        let set = CommitmentSet::new();
        // The empty accumulator is NOT an empty tree: physical slot 0 permanently holds the
        // `BOT(value=0, next=TOP)` sentinel — the low endpoint every absence bracket straddles.
        let leaves = set.exact_dense_leaves();
        assert_eq!(leaves.len(), 1);
        assert_eq!(leaves[0].addr(), ExactTaggedKey::Bot);
        assert_eq!(leaves[0].next_addr(), ExactTaggedKey::Top);
        assert_eq!(leaves[0].value(), 0);

        // ⚠ NO LONGER the native `CanonicalHeapTree8` empty root: this accumulator left that
        // (lossy, arity-3, one-felt-address) tree on 2026-07-31. Asserted, not stated.
        assert_ne!(
            set.root8(),
            dregg_circuit::heap_root::empty_heap_root_8(),
            "the committed root is the exact linked-leaf tree, not the legacy heap tree"
        );
        assert_ne!(
            set.root8(),
            crate::nullifier_set::NullifierSet::new().root8(),
            "even the EMPTY create/spend roots must be domain-separated (FCI2 vs FNI2)"
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

    /// ⚑ **THE COMMITTED CREATE ROOT IS THE EXACT LINKED-LEAF TREE, AND IT ROUND-TRIPS.**
    ///
    /// The retired encoding folded `HeapLeaf::entry(fold_bytes32_to_bb(cm), split_u64(value).0)`
    /// through a `CanonicalHeapTree8`; its doc comment claimed byte-identity with the deployed
    /// noteCreate grow-gate was load-bearing. It was not — no caller anywhere threads a
    /// non-empty `before_commitments` into that grow-gate (`sdk/src/full_turn_proof.rs:422` and
    /// `sdk/src/cipherclerk.rs:5812` both pass `&[]`). This tooth pins the replacement and,
    /// crucially, that it DECODES: a scrambling "fix" would pass a difference-only test.
    #[test]
    fn the_committed_create_root_encoding_round_trips_and_is_not_the_legacy_fold() {
        use dregg_circuit::exact_nullifier_aafi::ExactTaggedKey;

        let creates = [
            (make_commitment(7), make_value(7)),
            (make_commitment(42), 1u64 << 40),
            (make_commitment(99), u64::MAX),
        ];
        let mut set = CommitmentSet::new();
        for (c, v) in &creates {
            set.insert(*c, *v).unwrap();
        }

        // (a) ADDRESS + VALUE round-trip at the physical slot the record occupies.
        let leaves = set.exact_dense_leaves();
        assert_eq!(leaves.len(), creates.len() + 1);
        for (rank, (c, v)) in creates.iter().enumerate() {
            assert_eq!(leaves[rank + 1].addr().real_raw_bytes(), Some(c.0));
            assert_eq!(leaves[rank + 1].value(), *v);
        }

        // (b) The pointer chain is the total sorted linked list — the absence bracket.
        let mut by_key = leaves.clone();
        by_key.sort_by_key(|leaf| leaf.addr());
        assert_eq!(by_key[0].addr(), ExactTaggedKey::Bot);
        for window in by_key.windows(2) {
            assert!(window[0].addr() < window[1].addr());
            assert_eq!(window[0].next_addr(), window[1].addr());
        }
        assert_eq!(by_key[by_key.len() - 1].next_addr(), ExactTaggedKey::Top);

        // (c) Non-vacuity: it is emphatically not the retired grow-gate encoding.
        assert_ne!(
            set.root8(),
            legacy_committed_root8(&creates),
            "the committed create root must not be the retired lossy fold"
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

    /// The legacy committed encoding, computed here so the aliasing exhibits below name a REAL
    /// object rather than a remembered one: `HeapLeaf::entry(fold_bytes32_to_bb(cm),
    /// split_u64(value).0)` folded through a `CanonicalHeapTree8`. This is what
    /// `CommitmentSet::root8` was until 2026-07-31.
    fn legacy_committed_root8(records: &[(NoteCommitment, u64)]) -> dregg_circuit::Faithful8 {
        use dregg_circuit::effect_vm::{fold_bytes32_to_bb, split_u64};
        use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};
        CanonicalHeapTree8::new(
            records
                .iter()
                .map(|(c, v)| HeapLeaf::entry(fold_bytes32_to_bb(&c.0), split_u64(*v).0))
                .collect(),
            HEAP_TREE_DEPTH,
        )
        .root8()
    }

    /// ⚑ **A3 CLOSED, CREATE SIDE.** The retired leaf value was `split_u64(value).0`, so the
    /// committed create root was `2^30`-periodic: two ordinary note values `2^30` apart
    /// published a BYTE-IDENTICAL `commitments_root`. Both poles — the alias was real on the
    /// legacy root, and the committed root now SEPARATES them at full `u64` width without
    /// capping the value.
    #[test]
    fn the_committed_create_root_binds_bit_30_the_legacy_leaf_erased() {
        let c = make_commitment(3);
        let low = 17u64;
        let aliased = low + (1u64 << 30);

        // Vacuity guard: the two values must genuinely share the legacy leaf felt.
        assert_eq!(
            dregg_circuit::effect_vm::split_u64(low).0,
            dregg_circuit::effect_vm::split_u64(aliased).0,
            "vacuity guard: the pair must share the legacy low-30-bit leaf value"
        );
        assert_ne!(low, aliased);

        let mut low_set = CommitmentSet::new();
        low_set.insert(c, low).unwrap();
        let mut aliased_set = CommitmentSet::new();
        aliased_set.insert(c, aliased).unwrap();

        assert_eq!(
            legacy_committed_root8(&[(c, low)]),
            legacy_committed_root8(&[(c, aliased)]),
            "vacuity guard: the LEGACY committed root really did erase bit 30 of the \
             created-note value"
        );
        assert_ne!(
            low_set.root8(),
            aliased_set.root8(),
            "the committed create root must bind bit 30 of the created-note value"
        );
        assert_eq!(low_set.exact_dense_leaves()[1].value(), low);
        assert_eq!(aliased_set.exact_dense_leaves()[1].value(), aliased);
    }

    /// ⚑ **THE `as u32` POLE.** `split_u64`'s high limb is `(value >> 30) as u32`,
    /// which TRUNCATES for `value >= 2^62` — so `split_u64(2^62)` equals
    /// `split_u64(0)` in BOTH limbs, not just the low one. The value is therefore
    /// not recoverable from the pair either, and the exact root must still separate.
    #[test]
    fn the_committed_create_root_binds_bit_62_the_split_u64_cast_truncated() {
        let c = make_commitment(4);
        let base = 0u64;
        let truncating = 1u64 << 62;

        let (lo_a, hi_a) = dregg_circuit::effect_vm::split_u64(base);
        let (lo_b, hi_b) = dregg_circuit::effect_vm::split_u64(truncating);
        assert_eq!(
            (lo_a, hi_a),
            (lo_b, hi_b),
            "vacuity guard: `(value >> 30) as u32` must genuinely truncate at 2^62, \
             so BOTH published limbs collide"
        );

        let mut base_set = CommitmentSet::new();
        base_set.insert(c, base).unwrap();
        let mut trunc_set = CommitmentSet::new();
        trunc_set.insert(c, truncating).unwrap();

        assert_eq!(
            legacy_committed_root8(&[(c, base)]),
            legacy_committed_root8(&[(c, truncating)]),
            "vacuity guard: the LEGACY committed root really did collapse 2^62 onto 0"
        );
        assert_ne!(
            base_set.root8(),
            trunc_set.root8(),
            "the committed create root must bind bit 62 of the created-note value"
        );
        assert_eq!(base_set.exact_dense_leaves()[1].value(), base);
        assert_eq!(trunc_set.exact_dense_leaves()[1].value(), truncating);
    }

    /// ⚑ **ANTI-CAP POLE.** A LEGAL LARGE value — far above `2^30`, above `2^32`,
    /// and up to `u64::MAX` — must still record, still commit, and still be
    /// distinguished from its neighbours. The exact root is a WIDENING, not a
    /// domain restriction: nothing here is refused.
    #[test]
    fn the_committed_create_root_admits_and_separates_legal_large_values() {
        let c = make_commitment(5);
        let large = [
            (1u64 << 30),
            (1u64 << 30) + 1,
            1_000_000_000_000u64,
            (1u64 << 40),
            (1u64 << 62),
            u64::MAX,
            u64::MAX - 1,
        ];

        let mut roots = Vec::new();
        for value in large {
            let mut set = CommitmentSet::new();
            set.insert(c, value)
                .expect("a large legal note value must still be recordable");
            assert_eq!(set.value_of(&c), Some(value), "the full u64 is retained");
            roots.push(set.root8());
        }
        for i in 0..roots.len() {
            for j in (i + 1)..roots.len() {
                assert_ne!(
                    roots[i], roots[j],
                    "distinct large legal values {} and {} must commit differently",
                    large[i], large[j]
                );
            }
        }
    }

    /// ⚑ **A2 CLOSED, CREATE SIDE.** The committed root binds the commitment bytes the legacy
    /// one-felt fold aliased — and the bytes DECODE back out of the leaf.
    #[test]
    fn the_committed_create_root_binds_high_commitment_bytes_the_legacy_fold_aliased() {
        use dregg_circuit::field::BABYBEAR_P;

        let mut base_bytes = [0u8; 32];
        base_bytes[0] = 0xA7;
        let base = NoteCommitment(base_bytes);
        let mut aliased_bytes = base_bytes;
        aliased_bytes[28..32].copy_from_slice(&BABYBEAR_P.to_le_bytes());
        let aliased = NoteCommitment(aliased_bytes);

        assert_ne!(base, aliased);
        assert_eq!(
            dregg_circuit::effect_vm::fold_bytes32_to_bb(&base.0),
            dregg_circuit::effect_vm::fold_bytes32_to_bb(&aliased.0),
            "vacuity guard: the two commitments must alias in the legacy leaf fold"
        );

        let mut base_set = CommitmentSet::new();
        base_set.insert(base, 17).unwrap();
        let mut alias_set = CommitmentSet::new();
        alias_set.insert(aliased, 17).unwrap();

        assert_eq!(
            legacy_committed_root8(&[(base, 17)]),
            legacy_committed_root8(&[(aliased, 17)]),
            "vacuity guard: the LEGACY committed roots really did alias"
        );
        assert_ne!(
            base_set.root8(),
            alias_set.root8(),
            "the committed root must bind the hostile high commitment bytes"
        );
        assert_eq!(
            base_set.exact_dense_leaves()[1].addr().real_raw_bytes(),
            Some(base.0)
        );
        assert_eq!(
            alias_set.exact_dense_leaves()[1].addr().real_raw_bytes(),
            Some(aliased.0)
        );
    }

    /// ⚑ **THE EXPORT GATE, AND ITS RED-PROOF.**
    /// `node::executor_side_state_persistence::capture_executor_accumulators` exports
    /// `(commitment, value, seq)` records and refuses the snapshot unless replaying them
    /// through [`CommitmentSet::from_records`] reproduces the live accumulator's `root8()`.
    /// Both directions:
    ///
    ///  * an honest export round-trips exactly (the gate is satisfiable); and
    ///  * a record codec that narrows the value to what the RETIRED leaf could carry —
    ///    `split_u64(value).0`, the low 30 bits — is caught, and would have been INVISIBLE to
    ///    the retired committed root. Since the gate now runs on the committed root itself,
    ///    that blindness is gone rather than merely worked around.
    ///
    /// The narrowing below is the shape a truncating persistence field would have.
    #[test]
    fn the_export_round_trip_gate_is_faithful_and_can_go_red() {
        let records = [
            (make_commitment(1), 1u64 << 30),
            (make_commitment(2), (1u64 << 40) + 7),
            (make_commitment(3), u64::MAX),
        ];
        let mut live = CommitmentSet::new();
        for (c, v) in records {
            live.insert(c, v).unwrap();
        }

        // GREEN pole: the honest export replays to the identical exact root.
        let honest: Vec<_> = live.iter_in_append_order().collect();
        let replayed = CommitmentSet::from_records(honest.iter().copied()).unwrap();
        assert_eq!(
            replayed.root8(),
            live.root8(),
            "an honest (commitment, value, seq) export must replay to the same exact root"
        );

        // RED pole: a codec that narrows the value to the committed leaf's 30-bit
        // domain produces a DIFFERENT exact root — the gate fires.
        let narrowed: Vec<_> = honest
            .iter()
            .map(|(c, v, seq)| (*c, *v & 0x3FFF_FFFF, *seq))
            .collect();
        let narrowed_set = CommitmentSet::from_records(narrowed.iter().copied()).unwrap();
        assert_ne!(
            narrowed_set.root8(),
            live.root8(),
            "a value-narrowing export MUST be caught — this is the gate going red"
        );

        // ⚑ AND THE MEASUREMENT OF WHAT MOVED. Under the RETIRED committed encoding the
        // narrowed export was BYTE-IDENTICAL to the honest one, so this gate could not have
        // been written on the committed root at all. That is the defect this change removes.
        let honest_legacy: Vec<_> = honest
            .iter()
            .map(|(c, v, _)| (NoteCommitment(*c), *v))
            .collect();
        let narrowed_legacy: Vec<_> = narrowed
            .iter()
            .map(|(c, v, _)| (NoteCommitment(*c), *v))
            .collect();
        assert_eq!(
            legacy_committed_root8(&honest_legacy),
            legacy_committed_root8(&narrowed_legacy),
            "vacuity guard: the RETIRED committed root really was blind to the narrowing"
        );
    }

    /// The committed create root is append-order DEPENDENT (it is the AAFI fold), and the
    /// record round-trip is what makes that deterministic. Both poles.
    #[test]
    fn the_committed_create_root_is_append_order_bound_and_replay_stable() {
        let records = [
            (NoteCommitment([0x71; 32]), 0xfedc_ba98_7654_3210u64),
            (NoteCommitment([0x03; 32]), 7),
            (NoteCommitment([0xa4; 32]), 1u64 << 63),
            (NoteCommitment([0x29; 32]), u64::MAX),
        ];

        let mut forward = CommitmentSet::new();
        for (commitment, value) in records {
            forward.insert(commitment, value).unwrap();
        }
        let mut reverse = CommitmentSet::new();
        for (commitment, value) in records.into_iter().rev() {
            reverse.insert(commitment, value).unwrap();
        }

        assert_ne!(
            forward.iter_in_append_order().collect::<Vec<_>>(),
            reverse.iter_in_append_order().collect::<Vec<_>>(),
            "vacuity guard: append histories must genuinely differ"
        );
        assert_ne!(
            forward.root8(),
            reverse.root8(),
            "two different create SEQUENCES over the same set are two different histories"
        );

        let replayed =
            CommitmentSet::from_records(forward.iter_in_append_order().collect::<Vec<_>>())
                .unwrap();
        assert_eq!(
            forward.root8(),
            replayed.root8(),
            "and the durable record replay reproduces the history exactly"
        );
    }

    /// The create-side exact tree is DOMAIN-SEPARATED from the spend-side one:
    /// the same 32 bytes recorded at the same value in the two accumulators must
    /// NOT produce the same exact root, or one tree's opening would be replayable
    /// as the other's.
    #[test]
    fn the_committed_create_root_is_domain_separated_from_the_spend_side_dual() {
        let raw = [0x5a; 32];
        let value = 0x0123_4567_89ab_cdefu64;

        let mut creates = CommitmentSet::new();
        creates.insert(NoteCommitment(raw), value).unwrap();
        let mut spends = crate::nullifier_set::NullifierSet::new();
        spends.insert(crate::note::Nullifier(raw), value).unwrap();

        assert_ne!(
            creates.root8(),
            spends.root8(),
            "the create-side exact root must not alias the spend-side one"
        );
        assert_ne!(
            CommitmentSet::new().root8(),
            crate::nullifier_set::NullifierSet::new().root8(),
            "even the EMPTY roots must differ — the domain tags, not the contents, \
             are what keep the two accumulators apart"
        );
    }

    /// **CONTINUITY tooth (INV-2), RESTATED AT THE APPEND-ORDER ROOT.** Turn N's *after*-root
    /// equals turn N+1's *before*-root over the same history, reconstructed the way every real
    /// replay reconstructs it — through the persisted `seq` column and
    /// [`CommitmentSet::from_records`], not by re-inserting in some other order.
    #[test]
    fn root8_is_cross_turn_continuous_through_the_append_order() {
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

        let mut records: Vec<([u8; 32], u64, u64)> = turn_n.iter_in_append_order().collect();
        records.sort_by_key(|(c, _, _)| *c);
        let turn_n1 = CommitmentSet::from_records(records).unwrap();

        assert_eq!(
            after_root_n,
            turn_n1.root8(),
            "turn N after-root must equal turn N+1 before-root over the same history, \
             reconstructed through the persisted seq column"
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

        // The committed leaf sequence follows tau order: the i-th created commitment and its
        // value are at physical slot i + 1, decoded back out of the leaf.
        let leaves = set.exact_dense_leaves();
        for (i, cm) in cms.iter().enumerate() {
            assert_eq!(leaves[i + 1].addr().real_raw_bytes(), Some(cm.0));
            assert_eq!(leaves[i + 1].value(), 100 + i as u64);
        }
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
        assert_eq!(rebuilt.exact_dense_leaves(), original.exact_dense_leaves());
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
