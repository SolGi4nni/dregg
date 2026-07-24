//! Shielded-note accumulator: an append-only set of **hiding** shielded output
//! note commitments — the SHIELDED-side sibling of
//! [`crate::commitment_set::CommitmentSet`] (created cleartext notes),
//! [`crate::nullifier_set::NullifierSet`] (spent nullifiers), and
//! [`crate::revoked_set::RevokedSet`] (revoked credentials).
//!
//! This is the **fourth ledger accumulator** the shielded-apex redesign's L0
//! introduces (`docs/DESIGN-shielded-apex-tree-reconciliation.md` §3 R1). It is
//! the committed STATE half that lets the already-proven shielded descriptors
//! (`shieldedSpendDesc`, `metatheory/Dregg2/Circuit/Emit/ShieldedSpendDescriptor.lean`)
//! close seam #15 (the theft seam): the descriptor's in-AIR `piROOT ≡ piCOMMITTED`
//! pin needs a committed root that genuinely contains the shielded notes, and its
//! `NoteAccumulatorCR` hypothesis is exactly what THIS accumulator discharges in
//! reality. Before it existed, a shielded transfer's outputs landed **nowhere
//! committed** (`apply.rs` placeholder: "0 is a placeholder until the shielded
//! accumulator wiring is designed"), so `merkle_root` was pinned to nothing.
//!
//! # The HIDING leaf — why this is NOT [`crate::commitment_set::CommitmentSet`]
//!
//! The three sibling accumulators key a **value-carrying** leaf
//! `HeapLeaf::entry(fold(key), split_u64(value).0)` — the cleartext note value /
//! revocation height is a public leaf column, the SAME `NOTE_VALUE_LO` felt the
//! deployed grow-gate reads. **A shielded note MUST NOT reveal its value**, so it
//! has no public value to put in that column. This accumulator therefore keys a
//! **hiding** leaf: `HeapLeaf::entry(fold(hiding_commitment), 0)` — the folded
//! shielded note commitment as the sort key, and a **ZERO value column** (no
//! cleartext value). The value lives inside the hiding commitment, never as a
//! leaf field. This is the design's explicit R1 leaf shape (§3: "with **no
//! cleartext value column**") and is precisely why R2 (reusing the cleartext
//! `note_commitments`, whose leaf value column is load-bearing for the noteCreate
//! grow-gate) was rejected.
//!
//! GROW-ONLY: a duplicate shielded commitment is rejected (a shielded note
//! commitment cannot be created twice — the shielded-side analog of the nullifier
//! double-spend / commitment duplicate gate). The ONLY committed observable is the
//! felt-domain [`Self::root8`].
//!
//! # Root width — 8 felts, retiring the ~31-bit #15 entry point
//!
//! Like every sibling, [`Self::root8`] is a `CanonicalHeapTree8` (sorted-Poseidon2)
//! **8-felt (~124-bit) Faithful8** root. The sort-key felt is the lossy ~31-bit
//! `fold_bytes32_to_bb(commitment)` (as for all siblings), but the ROOT is 8 felts —
//! so wiring this root8() into the committed carrier (L1) and sourcing it as
//! `piCOMMITTED` (L4) retires the ~31-bit width of the wire-supplied `merkle_root`
//! that opens #15.
//!
//! # ⚑ HONEST L0 SCOPE — what this does and does NOT yet do
//!
//! This module is the **byte-safe** state foundation (L0): a new Rust type + the
//! executor's append/rollback threading. It carries **ZERO** VK/descriptor/AIR
//! cost. It does NOT (all named as dependent lanes in the DESIGN §6 table):
//!   * **L1** — land [`Self::root8`] as a rotation carrier *base limb* so the
//!     circuit commits it cross-turn (a VK epoch that re-baselines the rotated
//!     cohort, precedented by `revoked_root`); today root8() is live executor
//!     state, NOT yet in the AIR-bound `V9RotationContext` carrier.
//!   * **L2** — the in-AIR *append grow-gate* (Lean-authored, generalizing the
//!     `ShieldedWholeNoteSwapSubstrate` aafi32 append).
//!   * **L4** — *pin membership* against this root (source `piCOMMITTED` from
//!     root8() + retire the wire `merkle_root`).
//! The single committed-tree ENCODING decision (arity-4 plain Merkle membership
//! vs. this depth-16 arity-2 sorted IMT — DESIGN §7 Q2) is L2/L4 work; L0 mirrors
//! the sibling sorted-IMT `CanonicalHeapTree8` encoding the other three commit to.
//!
//! # Performance
//!
//! Uses `BTreeMap<[u8; 32], AppendRecord>` internally for O(log N) insert and
//! lookup, iterating keys in sorted order. The append-seq column (gap-#5 AAFI)
//! records the canonical tau append order so an order-dependent AAFI root is
//! reconstructible; see `iter_in_append_order` / `from_records`. Unlike the
//! siblings there is **no** value column.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::note::{NoteError, ShieldedNoteCommitment};

/// A stored accumulator entry: the entry's **append sequence** (`seq`) — the
/// gap-#5 AAFI (append-at-free-index) order column. AAFI roots are
/// insertion-order-dependent (the append order IS the canonical tau append
/// sequence, INV-6), so the store persists WHERE in the append sequence each
/// entry landed; a reconstruction replays the records sorted by `seq` and
/// recovers the identical AAFI layout every time. The sorted-compacted
/// [`ShieldedNoteSet::root8`] layer ignores `seq` (order-independent), so this is
/// purely ADDITIVE.
///
/// UNLIKE the sibling accumulators there is **no `value` field** — a shielded
/// leaf is hiding and carries no cleartext value column.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct AppendRecord {
    /// 0-based append index: this entry was the `seq`-th commitment appended.
    /// Mirrors [`dregg_circuit::heap_root::CanonicalHeapTree8::next_free_index`]
    /// semantics — the entry with append rank `seq` occupies physical AAFI
    /// slot `seq + 1` (slot 0 is the MIN sentinel).
    seq: u64,
}

/// Append-only accumulator of **hiding** shielded output note commitments. The
/// SHIELDED-side sibling of [`crate::commitment_set::CommitmentSet`]. GROW-ONLY: a
/// duplicate commitment is rejected.
///
/// Uses `BTreeMap<[u8; 32], AppendRecord>` for O(log N) insert and contains
/// operations and sorted-key iteration. There is **no value column** — the leaf
/// is hiding, keyed on the folded commitment alone with a ZERO value felt.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShieldedNoteSet {
    /// Every appended shielded note commitment mapped to its append sequence,
    /// kept in a BTreeMap for O(log N) operations and sorted-key iteration. The
    /// seq is the AAFI append-order column; there is intentionally no value.
    commitments: BTreeMap<[u8; 32], AppendRecord>,
    /// The next append sequence number (0-based). Every insert records the
    /// current `next_seq` and bumps it — the store-side mirror of the AAFI
    /// tree's `next_free_index` cursor (offset by 1 for the MIN sentinel).
    next_seq: u64,
}

impl ShieldedNoteSet {
    /// Create an empty shielded-note set.
    pub fn new() -> Self {
        Self {
            commitments: BTreeMap::new(),
            next_seq: 0,
        }
    }

    /// Number of shielded note commitments in the set.
    pub fn len(&self) -> usize {
        self.commitments.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.commitments.is_empty()
    }

    /// Append a shielded output note's hiding commitment (the note is now a
    /// committed, spendable shielded note). Returns error if the commitment is
    /// already present (duplicate append).
    ///
    /// Takes NO value: the shielded note's value is hidden inside the commitment
    /// and MUST NOT be a leaf column. O(log N) via BTreeMap insertion (does not
    /// overwrite on collision).
    pub fn insert(&mut self, commitment: ShieldedNoteCommitment) -> Result<(), NoteError> {
        if self.commitments.contains_key(&commitment.0) {
            return Err(NoteError::DuplicateShieldedNote { commitment });
        }
        self.commitments
            .insert(commitment.0, AppendRecord { seq: self.next_seq });
        self.next_seq += 1;
        Ok(())
    }

    /// Check if a shielded note commitment is in the set (the note is committed).
    ///
    /// O(log N) via BTreeMap key lookup.
    pub fn contains(&self, commitment: &ShieldedNoteCommitment) -> bool {
        self.commitments.contains_key(&commitment.0)
    }

    /// The append sequence recorded for a commitment, if present — the 0-based
    /// rank at which it was appended (the canonical tau append order, INV-6).
    /// This is the column a persistence layer must carry per entry so an AAFI
    /// (order-dependent) root is reconstructible; see [`Self::from_records`].
    pub fn seq_of(&self, commitment: &ShieldedNoteCommitment) -> Option<u64> {
        self.commitments.get(&commitment.0).map(|r| r.seq)
    }

    /// Iterate the commitments in sorted key order.
    pub fn iter(&self) -> impl Iterator<Item = &[u8; 32]> {
        self.commitments.keys()
    }

    /// Iterate the full `(commitment, seq)` records **in append order**
    /// (ascending `seq`) — the canonical tau append sequence (INV-6). This is
    /// BOTH the persistence export (each record carries its seq column) and the
    /// AAFI replay order: a reconstruction that re-applies these records in this
    /// order rebuilds the order-dependent AAFI tree identically.
    ///
    /// Ties on `seq` (impossible for records minted by [`Self::insert`], which
    /// assigns unique seqs; possible only for hand-built record sets) are broken
    /// deterministically by the commitment key, so the order is TOTAL.
    pub fn iter_in_append_order(&self) -> impl Iterator<Item = ([u8; 32], u64)> {
        let mut records: Vec<([u8; 32], u64)> =
            self.commitments.iter().map(|(c, r)| (*c, r.seq)).collect();
        records.sort_by_key(|(c, seq)| (*seq, *c));
        records.into_iter()
    }

    /// Reconstruct the set from durable `(commitment, seq)` records, **fixing the
    /// append order** from the persisted seq column: records are replayed sorted
    /// by `(seq, key)` and keep their persisted seqs verbatim, so the
    /// reconstruction is deterministic in the canonical tau order no matter what
    /// order the storage layer yields the records in. This is the AAFI-order
    /// reconstruction path — under AAFI the accumulator root depends on the
    /// append order, so "reconstruct from the store" must recover the ORIGINAL
    /// order, not the store's key order.
    ///
    /// Returns the duplicate-shielded-note error on a duplicate key.
    pub fn from_records(
        records: impl IntoIterator<Item = ([u8; 32], u64)>,
    ) -> Result<Self, NoteError> {
        let mut sorted: Vec<([u8; 32], u64)> = records.into_iter().collect();
        sorted.sort_by_key(|(c, seq)| (*seq, *c));
        let mut set = Self::new();
        for (commitment, seq) in sorted {
            if set.commitments.contains_key(&commitment) {
                return Err(NoteError::DuplicateShieldedNote {
                    commitment: ShieldedNoteCommitment(commitment),
                });
            }
            set.commitments.insert(commitment, AppendRecord { seq });
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
            .map(|(c, _)| Self::accumulator_leaf(&c))
            .collect()
    }

    /// The physical AAFI slot the NEXT append would occupy: `len() + 1` (slot 0
    /// is the MIN sentinel) — the store-side mirror of
    /// [`dregg_circuit::heap_root::CanonicalHeapTree8::next_free_index`] for a
    /// tree replayed from [`Self::aafi_leaves`].
    pub fn aafi_next_free_index(&self) -> usize {
        self.commitments.len() + 1
    }

    /// Remove a commitment from the set.
    ///
    /// Used ONLY by the turn-journal rollback path to undo a speculative append
    /// when a turn fails after the commitment was recorded. Outside of rollback
    /// the set is append-only.
    ///
    /// Returns `true` if the commitment was present and removed, `false`
    /// otherwise. O(log N) via BTreeMap remove (plus an O(N) append-cursor
    /// recompute — rollback is rare and off the hot path).
    ///
    /// The append cursor rolls back with the entry: `next_seq` is recomputed to
    /// one past the highest surviving seq, so rolling back the LAST append frees
    /// its seq and the re-executed turn's insert lands at the SAME append rank —
    /// the deterministic tau order is preserved across a speculative-append
    /// rollback.
    pub fn remove(&mut self, commitment: &ShieldedNoteCommitment) -> bool {
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

    /// The circuit-faithful node8 leaf for a single **hiding** shielded note
    /// commitment: `addr` is the folded commitment felt
    /// (`dregg_circuit::effect_vm::fold_bytes32_to_bb`, the SAME fold the sibling
    /// accumulators apply to their key), and `value` is **ZERO** — a shielded
    /// leaf is HIDING and carries no cleartext value column (contrast the sibling
    /// leaves, which fold a cleartext `split_u64(value).0` there). This is the
    /// DESIGN §3 R1 hiding-leaf shape `HeapLeaf::entry(fold(hiding_commitment), 0)`.
    ///
    /// The commitment is folded through the circuit's OWN `fold_bytes32_to_bb`
    /// helper so the sort-key encoding cannot drift from the sibling accumulators;
    /// the IMT `next_addr` pointer is relinked by the tree builder.
    pub fn accumulator_leaf(commitment: &[u8; 32]) -> dregg_circuit::heap_root::HeapLeaf {
        dregg_circuit::heap_root::HeapLeaf::entry(
            dregg_circuit::effect_vm::fold_bytes32_to_bb(commitment),
            // HIDING leaf: no cleartext value column.
            dregg_circuit::field::BabyBear::ZERO,
        )
    }

    /// **The faithful 8-felt (~124-bit) accumulator root of the shielded-note
    /// set** — the value destined to become the committed rotated state's
    /// shielded-note-root group (L1: a new carrier base limb) and, sourced as
    /// `piCOMMITTED`, the committed root the shielded spend descriptor's
    /// membership pin binds to (L4). A node that has accepted a shielded output
    /// carries a DIFFERENT `root8` than one that has not.
    ///
    /// This is the native `CanonicalHeapTree8` (arity-16 sorted-Poseidon2, depth
    /// [`dregg_circuit::heap_root::HEAP_TREE_DEPTH`]) root the sibling accumulators
    /// use — built from [`Self::accumulator_leaf`] over every hiding commitment in
    /// the set. The empty set folds to the native empty root
    /// (`dregg_circuit::heap_root::empty_heap_root_8`).
    pub fn root8(&self) -> dregg_circuit::Faithful8 {
        let leaves: Vec<dregg_circuit::heap_root::HeapLeaf> = self
            .commitments
            .keys()
            .map(|c| Self::accumulator_leaf(c))
            .collect();
        dregg_circuit::heap_root::CanonicalHeapTree8::new(
            leaves,
            dregg_circuit::heap_root::HEAP_TREE_DEPTH,
        )
        .root8()
    }
}

impl Default for ShieldedNoteSet {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_commitment(seed: u8) -> ShieldedNoteCommitment {
        let mut c = [0u8; 32];
        c[0] = seed;
        c[1] = seed.wrapping_mul(3).wrapping_add(1);
        ShieldedNoteCommitment(c)
    }

    #[test]
    fn test_shielded_note_set_insert_and_contains() {
        let mut set = ShieldedNoteSet::new();
        let c = make_commitment(1);

        assert!(!set.contains(&c));
        set.insert(c).unwrap();
        assert!(set.contains(&c));
    }

    #[test]
    fn test_shielded_note_set_duplicate_rejected() {
        let mut set = ShieldedNoteSet::new();
        let c = make_commitment(1);

        set.insert(c).unwrap();
        let result = set.insert(c);
        assert_eq!(
            result,
            Err(NoteError::DuplicateShieldedNote { commitment: c })
        );
    }

    #[test]
    fn test_shielded_note_set_multiple_inserts() {
        let mut set = ShieldedNoteSet::new();
        for i in 0..10 {
            set.insert(make_commitment(i)).unwrap();
        }
        assert_eq!(set.len(), 10);
        for i in 0..10 {
            assert!(set.contains(&make_commitment(i)));
        }
    }

    #[test]
    fn test_shielded_note_set_remove_rollback() {
        let mut set = ShieldedNoteSet::new();
        let c = make_commitment(1);
        set.insert(c).unwrap();
        assert!(set.remove(&c));
        assert!(!set.contains(&c));
        // Re-insertable after rollback (the set is grow-only outside rollback).
        set.insert(c).unwrap();
        assert!(set.contains(&c));
    }

    /// The empty set's faithful accumulator root is the NATIVE `CanonicalHeapTree8`
    /// empty root — the value a producer must fill for a no-shielded-note accumulator.
    #[test]
    fn root8_empty_matches_native_empty_heap_root_8() {
        let set = ShieldedNoteSet::new();
        assert_eq!(
            set.root8(),
            dregg_circuit::heap_root::empty_heap_root_8(),
            "an empty shielded-note set must fold to the native empty node8 root"
        );
    }

    /// A non-empty accumulator fills ALL 8 lanes of the root group: the
    /// completion lanes (`limbs()[1..8]`) are NON-ZERO and the root ADVANCES on
    /// every distinct append (the cross-node observable — the whole point of the
    /// faithful 8-felt fill retiring the ~31-bit #15 width).
    #[test]
    fn root8_grows_nonzero_completion_lanes_and_advances() {
        use dregg_circuit::field::BabyBear;

        let mut set = ShieldedNoteSet::new();
        let empty8 = set.root8();

        set.insert(make_commitment(1)).unwrap();
        let one8 = set.root8();
        assert_ne!(
            empty8, one8,
            "appending a shielded commitment must ADVANCE the accumulator root"
        );
        assert!(
            one8.limbs()[1..8].iter().any(|f| *f != BabyBear::ZERO),
            "a non-empty accumulator's completion lanes must be NON-ZERO — the \
             8-felt fill that retires the ~31-bit #15 width"
        );

        set.insert(make_commitment(2)).unwrap();
        let two8 = set.root8();
        assert_ne!(
            one8, two8,
            "a second distinct append must again advance the root (monotone accumulator)"
        );
    }

    /// **Hiding-leaf encoding tooth:** `root8` over the set equals a
    /// `CanonicalHeapTree8` built from the DESIGN §3 R1 hiding leaf
    /// `HeapLeaf::entry(fold_bytes32_to_bb(commitment), ZERO)` — folded through
    /// the circuit's OWN helper, so this is genuine byte-identity with the hiding
    /// encoding, not a re-assertion of a private formula.
    #[test]
    fn root8_matches_hiding_leaf_encoding() {
        use dregg_circuit::effect_vm::fold_bytes32_to_bb;
        use dregg_circuit::field::BabyBear;
        use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};

        let commitments = [make_commitment(7), make_commitment(42), make_commitment(99)];
        let mut set = ShieldedNoteSet::new();
        for c in &commitments {
            set.insert(*c).unwrap();
        }

        let hiding_leaves: Vec<HeapLeaf> = commitments
            .iter()
            .map(|c| HeapLeaf::entry(fold_bytes32_to_bb(&c.0), BabyBear::ZERO))
            .collect();
        let expected = CanonicalHeapTree8::new(hiding_leaves, HEAP_TREE_DEPTH).root8();

        assert_eq!(
            set.root8(),
            expected,
            "root8 must fold through the hiding (addr, ZERO) node8 leaf encoding"
        );
    }

    /// **The leaf carries NO cleartext value:** the shielded set's leaf is keyed
    /// on the commitment alone with a ZERO value column, so it is DISTINCT from a
    /// cleartext-value `CommitmentSet` leaf over the same commitment felt. This is
    /// the hiding property the whole accumulator exists to preserve — the value
    /// never enters the leaf.
    #[test]
    fn hiding_leaf_value_column_is_zero() {
        use dregg_circuit::field::BabyBear;

        let c = make_commitment(3);
        let leaf = ShieldedNoteSet::accumulator_leaf(&c.0);
        assert_eq!(
            leaf.value,
            BabyBear::ZERO,
            "a hiding shielded leaf must carry NO cleartext value (value column = 0)"
        );
    }

    /// Distinct commitments fold to distinct roots (the commitment is genuinely
    /// bound into the committed root even without a value column).
    #[test]
    fn root8_depends_on_the_commitment() {
        let mut a = ShieldedNoteSet::new();
        a.insert(make_commitment(3)).unwrap();

        let mut b = ShieldedNoteSet::new();
        b.insert(make_commitment(4)).unwrap();

        assert_ne!(
            a.root8(),
            b.root8(),
            "the committed accumulator root MUST depend on the shielded commitment"
        );
    }

    /// **CONTINUITY tooth:** turn N's *after*-root over `S ∪ {cm}` equals turn
    /// N+1's *before*-root over the same set (insertion-order-independent — a
    /// BTreeMap sorts).
    #[test]
    fn root8_is_cross_turn_continuous() {
        let base = [make_commitment(10), make_commitment(20)];
        let new_note = make_commitment(30);

        let mut turn_n = ShieldedNoteSet::new();
        for c in &base {
            turn_n.insert(*c).unwrap();
        }
        turn_n.insert(new_note).unwrap();
        let after_root_n = turn_n.root8();

        let mut turn_n1 = ShieldedNoteSet::new();
        turn_n1.insert(new_note).unwrap();
        for c in base.iter().rev() {
            turn_n1.insert(*c).unwrap();
        }
        let before_root_n1 = turn_n1.root8();

        assert_eq!(
            after_root_n, before_root_n1,
            "turn N after-root must equal turn N+1 before-root over the same \
             commitment set (INV-2 continuity, insertion-order-independent)"
        );
    }

    /// **A8 tooth — the append order is RECORDED:** seqs are assigned in
    /// insertion order regardless of key sort order, and the append-order
    /// iteration / AAFI leaf sequence follow the INSERTION order. Non-vacuous:
    /// the keys are inserted in reverse-sorted order so the orders differ.
    #[test]
    fn append_seq_records_insertion_order_not_key_order() {
        let mut cms: Vec<ShieldedNoteCommitment> = (1u8..=4).map(make_commitment).collect();
        cms.sort_by_key(|c| c.0);
        cms.reverse();

        let mut set = ShieldedNoteSet::new();
        for (i, cm) in cms.iter().enumerate() {
            set.insert(*cm).unwrap();
            assert_eq!(
                set.seq_of(cm),
                Some(i as u64),
                "the i-th insert must record append seq i"
            );
        }
        assert_eq!(set.aafi_next_free_index(), cms.len() + 1);

        let append_order: Vec<[u8; 32]> = set.iter_in_append_order().map(|(c, _)| c).collect();
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
            .map(|cm| ShieldedNoteSet::accumulator_leaf(&cm.0))
            .collect();
        assert_eq!(set.aafi_leaves(), expected_leaves);
    }

    /// **A8 tooth — reconstruction FIXES the append order:** records exported
    /// with their seq column and handed back sorted by KEY (the hostile storage
    /// order) reconstruct the IDENTICAL append order, AAFI leaf sequence, seqs,
    /// and (sorted-compacted) root8.
    #[test]
    fn reconstruction_from_records_fixes_the_append_order() {
        let mut cms: Vec<ShieldedNoteCommitment> = (1u8..=5).map(make_commitment).collect();
        cms.sort_by_key(|c| c.0);
        cms.reverse();

        let mut original = ShieldedNoteSet::new();
        for cm in cms.iter() {
            original.insert(*cm).unwrap();
        }

        let mut records: Vec<([u8; 32], u64)> = original.iter_in_append_order().collect();
        records.sort_by_key(|(c, _)| *c);

        let rebuilt = ShieldedNoteSet::from_records(records).unwrap();
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
    /// duplicate-append gate as the live insert path).
    #[test]
    fn from_records_rejects_duplicate_keys() {
        let c = make_commitment(1);
        match ShieldedNoteSet::from_records([(c.0, 0), (c.0, 1)]) {
            Err(NoteError::DuplicateShieldedNote { commitment }) => assert_eq!(commitment, c),
            other => panic!("duplicate key must be refused, got {other:?}"),
        }
    }

    /// **A8 tooth — rollback frees the LAST seq:** removing the most recent
    /// speculative append rolls the cursor back, so the re-executed turn's
    /// append lands at the SAME rank.
    #[test]
    fn rollback_frees_the_last_append_seq() {
        let mut set = ShieldedNoteSet::new();
        let a = make_commitment(1);
        let b = make_commitment(2);
        let c = make_commitment(3);

        set.insert(a).unwrap();
        set.insert(b).unwrap();
        assert_eq!(set.seq_of(&b), Some(1));

        assert!(set.remove(&b));
        set.insert(c).unwrap();
        assert_eq!(
            set.seq_of(&c),
            Some(1),
            "the re-executed append must reuse the rolled-back append rank"
        );
        assert_eq!(set.aafi_next_free_index(), 3);
    }
}
