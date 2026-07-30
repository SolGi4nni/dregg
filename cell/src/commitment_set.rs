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
use std::sync::LazyLock;

use dregg_circuit::Faithful8;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_many_8;
use serde::{Deserialize, Serialize};

use crate::note::{NoteCommitment, NoteError};

/// Depth of the exact created-commitment tree (`4^16 = 2^32` leaves) — the same
/// fixed geometry as the spent-nullifier dual
/// (`crate::nullifier_set::EXACT_NULLIFIER_TREE_DEPTH`), so the root shape is
/// protocol data rather than a function of the current set size.
pub const EXACT_COMMITMENT_TREE_DEPTH: usize = 16;
/// Number of BabyBear lanes in every hashed node and root.
pub const EXACT_COMMITMENT_ROOT_LANES: usize = 8;

/// Exact-leaf Poseidon2 domain, ASCII `"FCL8"`.
///
/// Deliberately DISTINCT from the spend side's `"FNL8"`
/// (`nullifier_set::EXACT_NULLIFIER_LEAF_DOMAIN`): a created commitment and a
/// spent nullifier are different statements about different sets, and a shared
/// domain would let one tree's leaf digest be replayed as the other's.
pub const EXACT_COMMITMENT_LEAF_DOMAIN: u32 = 0x4643_4c38;
/// Exact 4-ary internal-node Poseidon2 domain, ASCII `"FCN8"`.
pub const EXACT_COMMITMENT_NODE_DOMAIN: u32 = 0x4643_4e38;
/// Exact empty-leaf Poseidon2 domain, ASCII `"FCE8"`.
pub const EXACT_COMMITMENT_EMPTY_DOMAIN: u32 = 0x4643_4538;

fn exact_hash_to_8(domain: u32, inputs: &[BabyBear]) -> [BabyBear; EXACT_COMMITMENT_ROOT_LANES] {
    let mut preimage = Vec::with_capacity(1 + inputs.len());
    preimage.push(BabyBear::new(domain));
    preimage.extend_from_slice(inputs);
    hash_many_8(&preimage)
}

/// Exact faithful-eight leaf digest of `(raw 32-byte commitment, full u64 value)`.
///
/// Preimage geometry is fixed and descriptor-friendly:
/// `FCL8 || commitment_u16_le[16] || value_u16_le[4]`.
///
/// Both codecs are the PROMOTED deployed ones
/// (`dregg_circuit::exact_nullifier_aafi::{raw_to_u16_le, u64_to_u16_le}`), so
/// bytes and integers share ONE endianness rule and every limb is `< 2^16 ≪ p`
/// — the felt lift is the identity and NO reduction occurs. That is what makes
/// this leaf injective in both arguments, unlike [`CommitmentSet::accumulator_leaf`],
/// which folds the commitment to one felt and the value to its low 30 bits.
pub fn exact_commitment_leaf8(
    commitment: &[u8; 32],
    value: u64,
) -> [BabyBear; EXACT_COMMITMENT_ROOT_LANES] {
    let key = dregg_circuit::exact_nullifier_aafi::raw_to_u16_le(*commitment);
    let val = dregg_circuit::exact_nullifier_aafi::u64_to_u16_le(value);
    let mut inputs = [BabyBear::ZERO; 20];
    for (lane, limb) in key.iter().enumerate() {
        inputs[lane] = BabyBear::new(u32::from(*limb));
    }
    for (lane, limb) in val.iter().enumerate() {
        inputs[16 + lane] = BabyBear::new(u32::from(*limb));
    }
    exact_hash_to_8(EXACT_COMMITMENT_LEAF_DOMAIN, &inputs)
}

/// Exact 4-ary internal-node compression:
/// `FCN8 || child0[8] || child1[8] || child2[8] || child3[8]`.
pub fn exact_commitment_node8(
    children: &[[BabyBear; EXACT_COMMITMENT_ROOT_LANES]; 4],
) -> [BabyBear; EXACT_COMMITMENT_ROOT_LANES] {
    let mut inputs = [BabyBear::ZERO; 4 * EXACT_COMMITMENT_ROOT_LANES];
    for (child_index, child) in children.iter().enumerate() {
        let start = child_index * EXACT_COMMITMENT_ROOT_LANES;
        inputs[start..start + EXACT_COMMITMENT_ROOT_LANES].copy_from_slice(child);
    }
    exact_hash_to_8(EXACT_COMMITMENT_NODE_DOMAIN, &inputs)
}

static EXACT_COMMITMENT_EMPTY_HASHES: LazyLock<
    [[BabyBear; EXACT_COMMITMENT_ROOT_LANES]; EXACT_COMMITMENT_TREE_DEPTH + 1],
> = LazyLock::new(|| {
    let mut empty =
        [[BabyBear::ZERO; EXACT_COMMITMENT_ROOT_LANES]; EXACT_COMMITMENT_TREE_DEPTH + 1];
    empty[0] = exact_hash_to_8(EXACT_COMMITMENT_EMPTY_DOMAIN, &[]);
    for level in 1..=EXACT_COMMITMENT_TREE_DEPTH {
        empty[level] = exact_commitment_node8(&[empty[level - 1]; 4]);
    }
    empty
});

/// Canonical exact empty-subtree digest at `level` (`0` is an empty leaf and
/// `16` is the empty protocol root).
pub fn exact_commitment_empty_hash8_at_level(
    level: usize,
) -> [BabyBear; EXACT_COMMITMENT_ROOT_LANES] {
    assert!(
        level <= EXACT_COMMITMENT_TREE_DEPTH,
        "exact commitment empty level {level} exceeds depth {EXACT_COMMITMENT_TREE_DEPTH}"
    );
    EXACT_COMMITMENT_EMPTY_HASHES[level]
}

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

    /// **Exact faithful-eight root of the created-commitment accumulator** — the
    /// CREATE-side dual of [`crate::nullifier_set::NullifierSet::faithful_root8_exact`],
    /// which existed on the spend side alone until this landed.
    ///
    /// ⚑ WHY IT EXISTS. [`Self::root8`] is the accumulator the deployed noteCreate
    /// grow-gate opens against, and its leaf value is `split_u64(value).0` — the
    /// note value's LOW 30 BITS. So `root8` is a deterministic `2^30`-periodic
    /// function of every recorded value: a set that recorded `v` and a set that
    /// recorded `v + 2^30` publish the SAME committed `commitments_root`, hence the
    /// same [`dregg_turn::state_commit::consensus_state_commitment`], hence the same
    /// executor signature and receipt QC. That is a testimony gap, not a width
    /// nicety, and the Lean tooth for it is
    /// `metatheory/Dregg2/Bignum/LedgerBalance.lean` `accumulatorLeaf_aliases_at_2_30`.
    /// The spend side has carried its exact dual since the FNSP-v3 work; the create
    /// side had NOTHING — `root8` was its only observable at any width.
    ///
    /// This root is **additive**: `root8` is untouched, so the rotated proof's
    /// grow-gate keeps opening against the byte-identical legacy leaves and NO
    /// verification key rotates. Each leaf here binds all 32 raw commitment bytes as
    /// sixteen `u16` limbs and all 64 value bits as four `u16` limbs before any
    /// hashing, so it has no `2^30` value alias and no high-byte commitment alias.
    /// Its layout is insertion-order-INDEPENDENT (the `BTreeMap`'s canonical sorted
    /// key order supplies dense leaf positions), unlike the AAFI append order.
    ///
    /// ⚠ It is NOT yet the value any consensus object commits to — putting a
    /// value-faithful accumulator root into the anchor is the AIR/VK flag day (the
    /// leaf's value column is `param::NOTE_VALUE_LO` BY CONSTRAINT, so a wider leaf
    /// is a descriptor re-emit). What it IS today: the value-faithful reference the
    /// durable capture path checks itself against, so a record codec that narrows a
    /// note value fails closed instead of aliasing silently.
    pub fn faithful_root8_exact(&self) -> Faithful8 {
        const CAPACITY: u128 = 1u128 << (2 * EXACT_COMMITMENT_TREE_DEPTH);
        assert!(
            (self.commitments.len() as u128) <= CAPACITY,
            "exact commitment tree capacity exceeded: {} entries > 4^{}",
            self.commitments.len(),
            EXACT_COMMITMENT_TREE_DEPTH
        );

        if self.commitments.is_empty() {
            return faithful8_from_exact_lanes(
                EXACT_COMMITMENT_EMPTY_HASHES[EXACT_COMMITMENT_TREE_DEPTH],
            );
        }

        let mut nodes: Vec<[BabyBear; EXACT_COMMITMENT_ROOT_LANES]> = self
            .commitments
            .iter()
            .map(|(commitment, record)| exact_commitment_leaf8(commitment, record.value))
            .collect();

        for level in 0..EXACT_COMMITMENT_TREE_DEPTH {
            let parent_count = nodes.len().div_ceil(4);
            let mut parents = Vec::with_capacity(parent_count);
            for chunk in nodes.chunks(4) {
                let mut children = [EXACT_COMMITMENT_EMPTY_HASHES[level]; 4];
                children[..chunk.len()].copy_from_slice(chunk);
                parents.push(exact_commitment_node8(&children));
            }
            nodes = parents;
        }

        debug_assert_eq!(nodes.len(), 1);
        faithful8_from_exact_lanes(nodes[0])
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

    /// ⚑ **THE A8 EXHIBIT, CREATE SIDE.** `root8`'s leaf value is
    /// `split_u64(value).0`, so it is `2^30`-periodic in the recorded value: two
    /// perfectly ordinary note values a mere `2^30` apart publish a BYTE-IDENTICAL
    /// committed `commitments_root`. Both poles are asserted here — the alias is
    /// real on the legacy root, and the exact root SEPARATES them at full `u64`
    /// width WITHOUT capping the value.
    #[test]
    fn exact_root_separates_the_legacy_2_30_value_alias() {
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
            low_set.root8(),
            aliased_set.root8(),
            "vacuity guard: the deployed grow-gate root really does erase bit 30 of \
             the created-note value — if this ever stops holding, the leaf encoding \
             changed and the exact dual below is measuring the wrong thing"
        );
        assert_ne!(
            low_set.faithful_root8_exact(),
            aliased_set.faithful_root8_exact(),
            "the exact create-side root must bind bit 30 of the created-note value"
        );
    }

    /// ⚑ **THE `as u32` POLE.** `split_u64`'s high limb is `(value >> 30) as u32`,
    /// which TRUNCATES for `value >= 2^62` — so `split_u64(2^62)` equals
    /// `split_u64(0)` in BOTH limbs, not just the low one. The value is therefore
    /// not recoverable from the pair either, and the exact root must still separate.
    #[test]
    fn exact_root_separates_the_split_u64_2_62_truncation_alias() {
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

        assert_eq!(base_set.root8(), trunc_set.root8());
        assert_ne!(
            base_set.faithful_root8_exact(),
            trunc_set.faithful_root8_exact(),
            "the exact create-side root must bind bit 62 of the created-note value"
        );
    }

    /// ⚑ **ANTI-CAP POLE.** A LEGAL LARGE value — far above `2^30`, above `2^32`,
    /// and up to `u64::MAX` — must still record, still commit, and still be
    /// distinguished from its neighbours. The exact root is a WIDENING, not a
    /// domain restriction: nothing here is refused.
    #[test]
    fn exact_root_admits_and_separates_legal_large_values() {
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
            roots.push(set.faithful_root8_exact());
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

    /// The exact root binds the commitment bytes the legacy one-felt fold aliases.
    #[test]
    fn exact_root_binds_high_commitment_bytes_the_legacy_fold_aliases() {
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
            base_set.root8(),
            alias_set.root8(),
            "vacuity guard: legacy accumulator roots really do alias"
        );
        assert_ne!(
            base_set.faithful_root8_exact(),
            alias_set.faithful_root8_exact(),
            "the exact tree must bind the hostile high commitment bytes"
        );
    }

    /// ⚑ **THE EXPORT GATE, AND ITS RED-PROOF.**
    /// `node::executor_side_state_persistence::capture_executor_accumulators` exports
    /// `(commitment, value, seq)` records and refuses the snapshot unless replaying
    /// them through [`CommitmentSet::from_records`] reproduces the live accumulator's
    /// `faithful_root8_exact()`. This pins BOTH directions of why that gate is on the
    /// exact root and not on `root8`:
    ///
    ///  * an honest export round-trips exactly (the gate is satisfiable); and
    ///  * a record codec that narrows the value to what the COMMITTED leaf can carry
    ///    — `split_u64(value).0`, the low 30 bits — is caught by the exact root and
    ///    **invisible to `root8`**. `root8` cannot witness this check; that is the
    ///    whole reason the gate does not use it.
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
            replayed.faithful_root8_exact(),
            live.faithful_root8_exact(),
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
            narrowed_set.faithful_root8_exact(),
            live.faithful_root8_exact(),
            "a value-narrowing export MUST be caught — this is the gate going red"
        );

        // And the reason the gate cannot be written on `root8`: the narrowed export
        // is BYTE-IDENTICAL to the honest one there.
        assert_eq!(
            narrowed_set.root8(),
            live.root8(),
            "the committed accumulator root is blind to the narrowing — a round-trip \
             check written on `root8` would be vacuous against exactly this defect"
        );
    }

    /// The exact layout is the canonical SORTED one, so the append history does
    /// not move the root (unlike the AAFI leaves).
    #[test]
    fn exact_root_is_insertion_order_independent() {
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
        assert_eq!(
            forward.faithful_root8_exact(),
            reverse.faithful_root8_exact(),
            "sorted BTreeMap order must define one canonical exact root"
        );
    }

    /// The create-side exact tree is DOMAIN-SEPARATED from the spend-side one:
    /// the same 32 bytes recorded at the same value in the two accumulators must
    /// NOT produce the same exact root, or one tree's opening would be replayable
    /// as the other's.
    #[test]
    fn exact_root_is_domain_separated_from_the_spend_side_dual() {
        let raw = [0x5a; 32];
        let value = 0x0123_4567_89ab_cdefu64;

        let mut creates = CommitmentSet::new();
        creates.insert(NoteCommitment(raw), value).unwrap();
        let mut spends = crate::nullifier_set::NullifierSet::new();
        spends.insert(crate::note::Nullifier(raw), value).unwrap();

        assert_ne!(
            creates.faithful_root8_exact(),
            spends.faithful_root8_exact(),
            "the create-side exact root must not alias the spend-side one"
        );
        assert_ne!(
            CommitmentSet::new().faithful_root8_exact(),
            crate::nullifier_set::NullifierSet::new().faithful_root8_exact(),
            "even the EMPTY roots must differ — the domain tags, not the contents, \
             are what keep the two accumulators apart"
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
