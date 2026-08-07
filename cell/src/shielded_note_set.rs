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
//! # Root width — 8 felts over an EXACT (injective) leaf
//!
//! [`Self::root8`] is the exact tagged-LINKED-LEAF (indexed-Merkle) append-at-free-index
//! root, `FSI2 ‖ addr17 ‖ value4 ‖ next17` at depth 16, arity 4, eight BabyBear lanes —
//! the same object the three sibling accumulators committed to on 2026-07-31, under its
//! own domain triple.
//!
//! ⚑ **WHAT THIS REPLACED (2026-08-01), AND WHY IT WAS THE WORST OF THE FOUR.** Until
//! today this folded `HeapLeaf::entry(fold_bytes32_to_bb(commitment), ZERO)` through a
//! `CanonicalHeapTree8`. `fold_bytes32_to_bb` is an **onto `F_p`-linear form** over the
//! mod-`p` limb split (its own doc: "NOT collision-resistant — `O(1)`, and `O(1)` even
//! for a CHOSEN TARGET"), so the address was a ~31-bit image of the 32-byte commitment
//! that an attacker SOLVES for rather than searches. The three siblings at least carried
//! a cleartext value column beside it; this leaf's value column is **ZERO by design**
//! (hiding), so the degraded address was the leaf's ENTIRE content — two distinct
//! shielded note commitments were **literally the same leaf**, and the set's only
//! committed observable could not tell them apart. It was the last of the four still on
//! the retired encoding, and the only one where the fold stood alone.
//!
//! The new leaf carries the address as a tag plus sixteen little-endian `u16` limbs
//! (`2^256` on the nose, no reduction) and a full-width `next_addr` pointer, so it is
//! injective in the commitment *and* keeps the IMT absence bracket a non-membership
//! opening straddles. **The hiding property is unchanged**: the value column is four
//! zero `u16` limbs — the same "no cleartext value" the design's R1 shape requires.
//!
//! ⓘ **Nothing re-emits and no VK rotates.** `root8()` is not yet in the AIR-bound
//! `V9RotationContext` carrier (L1 below is still open) and `accumulator_leaf` had no
//! call site outside this module's own tests, so this changes a value that no circuit,
//! descriptor or signed anchor reads today. What DOES change: any persisted
//! shielded-accumulator root recorded before this commit no longer reproduces —
//! re-genesis, as ever.
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

use dregg_circuit::Faithful8;
use dregg_circuit::exact_nullifier_aafi::{
    Digest8, ExactLinkedDomains, ExactLinkedLeaf, ExactPath4, ExactTaggedKey, TREE_ARITY,
    exact_empty_hash_ladder, exact_leaf_digest_in, exact_linked_append_root8,
    exact_linked_dense_leaves, exact_node_digest_in,
};
use dregg_circuit::field::BabyBear;
use serde::{Deserialize, Serialize};

use crate::note::{NoteError, ShieldedNoteCommitment};

/// Depth of the exact shielded-note tree (`4^16 = 2^32` leaves) — the same fixed
/// geometry as the three sibling accumulators, so the root shape is protocol data
/// rather than a function of the current set size.
pub const EXACT_SHIELDED_TREE_DEPTH: usize = dregg_circuit::exact_nullifier_aafi::TREE_DEPTH;
/// Number of BabyBear lanes in every hashed node and root.
pub const EXACT_SHIELDED_ROOT_LANES: usize = dregg_circuit::exact_nullifier_aafi::ROOT_LANES;

/// The shielded-side exact tagged-linked-leaf domain triple: `FSI2`/`FSN2`/`FSE2`.
///
/// Deliberately DISTINCT from the create side's `FCI2`/`FCN2`/`FCE2`
/// ([`crate::commitment_set::EXACT_COMMITMENT_LINKED_DOMAINS`]), the spend side's
/// `FNI2`/`FNN2`/`FNE2` and the revocation side's `FRI2`/`FRN2`/`FRE2`. A shielded output
/// commitment, a cleartext created commitment, a spent nullifier and a revoked credential
/// are four different statements about four different sets; a shared domain would let one
/// tree's leaf digest — or its EMPTY root — be replayed as another's.
///
/// The separation matters most HERE: a shielded leaf's value column is all zeros, which is
/// exactly the shape a `CommitmentSet` leaf for a zero-valued note would have, so without a
/// distinct leaf tag the two trees' leaf digests would coincide on a shared commitment.
pub const EXACT_SHIELDED_LINKED_DOMAINS: ExactLinkedDomains = ExactLinkedDomains {
    leaf: 0x4653_4932,  // `FSI2`
    node: 0x4653_4e32,  // `FSN2`
    empty: 0x4653_4532, // `FSE2`
};

/// The hiding leaf's value column, in the exact encoding: **zero**, which
/// [`dregg_circuit::exact_nullifier_aafi::exact_linked_append_root8`] carries as four zero
/// `u16` limbs. A shielded note MUST NOT reveal its value, so unlike the three sibling
/// accumulators there is no cleartext value to place here — the value lives inside the
/// hiding commitment, never as a leaf field (DESIGN §3 R1, "with no cleartext value column").
const HIDING_VALUE: u64 = 0;

fn faithful8_from_exact_lanes(lanes: [BabyBear; EXACT_SHIELDED_ROOT_LANES]) -> Faithful8 {
    dregg_circuit::exact_nullifier_aafi::exact_root_faithful8(lanes)
}

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

    // ⚑ `aafi_leaves` — the `Vec<HeapLeaf>` view built from `accumulator_leaf` — is DELETED
    // (2026-08-01), together with `accumulator_leaf` itself. Both were the retired
    // `fold_bytes32_to_bb`-addressed encoding, and neither had a call site outside this
    // module's own tests. Keeping a `HeapLeaf` view "so downstream forwards remain valid"
    // would mean two leaf shapes for one accumulator, which is how the encoding drifts back.
    // The replacement view is [`Self::exact_dense_leaves`], indexed by PHYSICAL SLOT rather
    // than append rank (slot 0 is the `BOT` sentinel, append rank `r` sits at slot `r + 1`),
    // which is what the exact fold actually hashes.

    /// The physical AAFI slot the NEXT append would occupy: `len() + 1` (slot 0
    /// is the permanent `BOT` sentinel) — the store-side mirror of the append cursor for a
    /// tree replayed from [`Self::exact_dense_leaves`].
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

    /// The append-ordered `(commitment, value)` record list the exact root folds — the
    /// value is [`HIDING_VALUE`] (zero) for every leaf, because a shielded leaf carries no
    /// cleartext value column.
    fn exact_append_records(&self) -> Vec<([u8; 32], u64)> {
        self.iter_in_append_order()
            .map(|(commitment, _)| (commitment, HIDING_VALUE))
            .collect()
    }

    /// **THE committed accumulator root of the shielded-note set** — the exact tagged
    /// LINKED-LEAF (indexed-Merkle) append-at-free-index root, `FSI2 ‖ addr17 ‖ value4 ‖
    /// next17` at depth 16, arity 4, eight BabyBear lanes. The SHIELDED dual of
    /// [`crate::commitment_set::CommitmentSet::root8`], domain-separated from it and from
    /// both the spend and revocation sides.
    ///
    /// The address rides sixteen little-endian `u16` limbs of the raw 32-byte commitment
    /// (`2^256`, no reduction), so the leaf is INJECTIVE in the commitment: no two distinct
    /// shielded notes share it. That is the property the retired
    /// `HeapLeaf::entry(fold_bytes32_to_bb(commitment), ZERO)` leaf did not have at any root
    /// width — see the ⚑ block in the module docs.
    ///
    /// **Hiding is preserved.** The leaf's value column is [`HIDING_VALUE`] = 0 for every
    /// entry, carried as four zero `u16` limbs; nothing about the note's value enters the
    /// leaf. The four-zero column is why the leaf DOMAIN tag has to differ from the create
    /// side's, and it does ([`EXACT_SHIELDED_LINKED_DOMAINS`]).
    ///
    /// A node that has accepted a shielded output carries a DIFFERENT root8 than one that
    /// has not. The empty set folds to the domain's own empty-ladder root.
    pub fn root8(&self) -> Faithful8 {
        let records = self.exact_append_records();
        let lanes = exact_linked_append_root8(EXACT_SHIELDED_LINKED_DOMAINS, &records).expect(
            "the shielded commitment map's keys are unique by construction (a BTreeMap over \
             all 32 raw bytes, and the tagged-key encoding is injective on them), and its \
             length is bounded by the 4^16 tree capacity",
        );
        faithful8_from_exact_lanes(lanes)
    }

    /// The committed accumulator's **dense physical leaf vector** — exactly what
    /// [`Self::root8`] hashes, indexed by physical slot. Slot 0 is the permanent `BOT`
    /// sentinel; the record at append rank `r` sits at slot `r + 1`.
    ///
    /// Exposed because it is the readable form of the property the root has and its
    /// predecessor did not: every leaf's `addr()` recovers the FULL 32-byte commitment and
    /// every leaf's `next_addr()` is the next larger present address (the absence bracket),
    /// so a test can assert the encoding ROUND-TRIPS rather than merely that two digests
    /// differ.
    pub fn exact_dense_leaves(&self) -> Vec<dregg_circuit::exact_nullifier_aafi::ExactLinkedLeaf> {
        dregg_circuit::exact_nullifier_aafi::exact_linked_dense_leaves(&self.exact_append_records())
            .expect("the shielded commitment map's keys are unique and within the 4^16 capacity")
    }

    /// **The membership authentication path for a committed shielded note** — the
    /// input a shielded-spend proof needs to prove `commitment` is a GENUINE member
    /// of THIS set at [`Self::root8`]. `None` if the commitment is not committed.
    ///
    /// This is the L4 half of DESIGN §6: a spend proof pins membership against
    /// `root8()` (sourced by the executor, never the wire), and to build that proof
    /// the prover must exhibit the note's real place in the committed tree. That
    /// place is what this returns.
    ///
    /// The fold and the sibling/position convention are exactly the circuit's
    /// [`dregg_circuit::exact_nullifier_aafi::exact_linked_fold_root8`] — `cur` at
    /// child slot `position`, the three siblings in increasing child-slot order (the
    /// `recompose` convention), least-significant level first — under the shielded
    /// domain triple. So recomposing the returned path from the leaf digest
    /// reproduces `root8()`, and the Lean-authored shielded-spend membership AIR
    /// (`ShieldedSpendExactMembershipEmit`, whose `childExpr` realizes the same
    /// `exactChildren4`/`recompose`) folds the SAME object. The
    /// [`ShieldedMembershipPath::leaf`] carries the note's 32-byte address, its ZERO
    /// hiding value column, and its linked `next_addr` successor — the leaf content a
    /// satisfying spend trace is forced to open.
    pub fn membership_path(
        &self,
        commitment: &ShieldedNoteCommitment,
    ) -> Option<ShieldedMembershipPath> {
        let records = self.exact_append_records();
        let dense = exact_linked_dense_leaves(&records).ok()?;
        let target_key = ExactTaggedKey::from_raw(commitment.0);
        let target_slot = dense.iter().position(|leaf| leaf.addr() == target_key)?;

        let empty = exact_empty_hash_ladder(EXACT_SHIELDED_LINKED_DOMAINS);
        let mut level_digests: Vec<Digest8> = dense
            .iter()
            .map(|leaf| exact_leaf_digest_in(EXACT_SHIELDED_LINKED_DOMAINS, *leaf))
            .collect();

        let mut index = target_slot as u32;
        let mut positions = [0u8; EXACT_SHIELDED_TREE_DEPTH];
        let mut siblings = [[[BabyBear::ZERO; EXACT_SHIELDED_ROOT_LANES]; TREE_ARITY - 1];
            EXACT_SHIELDED_TREE_DEPTH];
        for level in 0..EXACT_SHIELDED_TREE_DEPTH {
            let position = (index % TREE_ARITY as u32) as u8;
            let parent = index / TREE_ARITY as u32;
            positions[level] = position;
            // The co-path: the three children of `parent` other than the target,
            // in increasing child-slot order (the `recompose` convention).
            let mut sib = 0usize;
            for child_slot in 0..TREE_ARITY {
                if child_slot as u8 == position {
                    continue;
                }
                let child_index = parent as usize * TREE_ARITY + child_slot;
                siblings[level][sib] = level_digests
                    .get(child_index)
                    .copied()
                    .unwrap_or(empty[level]);
                sib += 1;
            }
            // Fold this level to its parents exactly as `exact_linked_fold_root8`
            // does, so the extracted co-path is the real one all the way up.
            let parent_count = level_digests.len().div_ceil(TREE_ARITY).max(1);
            let mut parents = Vec::with_capacity(parent_count);
            for p in 0..parent_count {
                let mut children = [empty[level]; TREE_ARITY];
                let first = p * TREE_ARITY;
                for (slot, child) in children.iter_mut().enumerate() {
                    if let Some(d) = level_digests.get(first + slot) {
                        *child = *d;
                    }
                }
                parents.push(exact_node_digest_in(
                    EXACT_SHIELDED_LINKED_DOMAINS,
                    children,
                ));
            }
            level_digests = parents;
            index = parent;
        }

        Some(ShieldedMembershipPath {
            leaf: dense[target_slot],
            path: ExactPath4 {
                positions,
                siblings,
            },
        })
    }
}

/// A membership authentication path for a committed shielded note — the witness a
/// shielded-spend proof folds up to [`ShieldedNoteSet::root8`]. Produced by
/// [`ShieldedNoteSet::membership_path`].
///
/// `leaf` is the note's committed [`ExactLinkedLeaf`] (its 32-byte address, its ZERO
/// hiding value column, and its linked `next_addr` successor); `path` is the
/// depth-16 arity-4 authentication path (a position digit + three sibling digests
/// per level, least-significant level first). `recompose`-ing `path` from
/// `exact_leaf_digest_in(FSI2, leaf)` reproduces `root8()`.
#[derive(Clone, Debug)]
pub struct ShieldedMembershipPath {
    /// The committed leaf: address (the 32-byte commitment as a tagged key), the
    /// ZERO hiding value column, and the linked `next_addr` successor.
    pub leaf: ExactLinkedLeaf,
    /// The depth-16 arity-4 authentication path (positions + sibling digests).
    pub path: ExactPath4,
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

    /// The empty set's root is the EXACT tree's own empty fold under the shielded domain
    /// triple, and — the part that matters — it is **distinct from every sibling
    /// accumulator's empty root**.
    ///
    /// ⚑ This replaced an assertion against `heap_root::empty_heap_root_8()` (the retired
    /// `CanonicalHeapTree8` empty root), which is no longer the object this accumulator
    /// commits to. The domain-separation half is the load-bearing one: with a shared leaf
    /// tag, an empty shielded root would be byte-identical to an empty create/spend/revoke
    /// root and one tree's "I hold nothing" could be replayed as another's.
    #[test]
    fn root8_empty_is_the_shielded_domain_empty_and_not_a_siblings() {
        let set = ShieldedNoteSet::new();
        let expected = faithful8_from_exact_lanes(
            exact_linked_append_root8(EXACT_SHIELDED_LINKED_DOMAINS, &[]).unwrap(),
        );
        assert_eq!(set.root8(), expected);

        for (name, domains) in [
            (
                "create",
                crate::commitment_set::EXACT_COMMITMENT_LINKED_DOMAINS,
            ),
            (
                "spend",
                crate::nullifier_set::EXACT_NULLIFIER_LINKED_DOMAINS,
            ),
            ("revoke", crate::revoked_set::EXACT_REVOKED_LINKED_DOMAINS),
        ] {
            let sibling =
                faithful8_from_exact_lanes(exact_linked_append_root8(domains, &[]).unwrap());
            assert_ne!(
                set.root8(),
                sibling,
                "the empty shielded root must be domain-separated from the empty {name} root, \
                 or one tree's empty commitment is replayable as another's"
            );
        }
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

    /// Two DISTINCT 32-byte shielded commitments that the retired leaf encoding mapped to
    /// the **identical** address, exhibited at `O(1)` with no search.
    ///
    /// `fold_bytes32_to_bb` is `Σ limbᵢ · MIX^i (mod p)` over `bytes32_to_8_limbs`, whose
    /// limb `i` is `u32::from_le_bytes(b[4i..4i+4]) % p`. Since `2p < 2^32`, the chunk
    /// values `v` and `v + p` reduce to the SAME limb — so flipping chunk 0 from `0` to `p`
    /// and leaving the other 28 bytes alone produces a second commitment with a
    /// byte-identical fold. One addition; no grind, no birthday bound.
    fn retired_fold_collision_pair() -> (ShieldedNoteCommitment, ShieldedNoteCommitment) {
        let mut a = [0u8; 32];
        let mut b = [0u8; 32];
        for i in 4..32 {
            a[i] = i as u8;
            b[i] = i as u8;
        }
        a[0..4].copy_from_slice(&0u32.to_le_bytes());
        b[0..4].copy_from_slice(&dregg_circuit::field::BABYBEAR_P.to_le_bytes());
        (ShieldedNoteCommitment(a), ShieldedNoteCommitment(b))
    }

    /// **THE FALSIFIER for the 2026-08-01 migration.** The pair above is a genuine `O(1)`
    /// collision of the RETIRED address fold — asserted here, so the exhibit cannot rot into
    /// a pair that merely happens to differ — and the LIVE `root8` separates them.
    ///
    /// Under the retired `HeapLeaf::entry(fold_bytes32_to_bb(c), ZERO)` leaf these two
    /// shielded notes were literally the same leaf: same address, and a ZERO value column
    /// carrying nothing to tell them apart. A set holding both committed as if it held one,
    /// and dropping either left the committed root byte-identical.
    #[test]
    fn root8_separates_a_retired_fold_collision_pair() {
        use dregg_circuit::effect_vm::fold_bytes32_to_bb;

        let (a, b) = retired_fold_collision_pair();
        assert_ne!(a.0, b.0, "the pair must be DISTINCT 32-byte commitments");
        assert_eq!(
            fold_bytes32_to_bb(&a.0),
            fold_bytes32_to_bb(&b.0),
            "vacuity guard: the pair must genuinely collide under the RETIRED address fold, \
             or this test proves nothing about the migration"
        );

        let mut only_a = ShieldedNoteSet::new();
        only_a.insert(a).unwrap();

        let mut both = ShieldedNoteSet::new();
        both.insert(a).unwrap();
        both.insert(b).unwrap();

        assert_eq!(both.len(), 2, "both commitments are distinct set members");
        assert_ne!(
            only_a.root8(),
            both.root8(),
            "the exact tagged-key leaf must SEPARATE a pair the retired ~31-bit linear fold \
             merged: a shielded note whose sibling collides must still move the committed root"
        );
    }

    /// **Hiding is preserved by the exact leaf:** every committed leaf's value column is
    /// zero, so no cleartext value enters the commitment. This is the property the whole
    /// accumulator exists to preserve (DESIGN §3 R1, "no cleartext value column") and it
    /// survives the move off the folded address unchanged.
    #[test]
    fn every_exact_leaf_value_column_is_zero() {
        let mut set = ShieldedNoteSet::new();
        for seed in [3u8, 17, 200] {
            set.insert(make_commitment(seed)).unwrap();
        }
        let leaves = set.exact_dense_leaves();
        assert_eq!(leaves.len(), 4, "3 entries + the BOT sentinel at slot 0");
        for (slot, leaf) in leaves.iter().enumerate() {
            assert_eq!(
                leaf.value(),
                0,
                "slot {slot}: a hiding shielded leaf must carry NO cleartext value"
            );
        }
    }

    /// **The address round-trips**: the committed leaf recovers the FULL 32 bytes of the
    /// commitment. This is what the retired fold could not do at any root width — it is the
    /// difference between an injective encoding and a ~31-bit image.
    #[test]
    fn exact_leaf_address_recovers_all_thirty_two_bytes() {
        use dregg_circuit::exact_nullifier_aafi::ExactTaggedKey;

        let c = make_commitment(91);
        let mut set = ShieldedNoteSet::new();
        set.insert(c).unwrap();

        let leaves = set.exact_dense_leaves();
        let addr = leaves[1].addr();
        assert_eq!(
            addr,
            ExactTaggedKey::from_raw(c.0),
            "the committed address must be the raw 32 bytes, not a projection of them"
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

    /// Recompose an authentication path from a leaf digest, matching the circuit's
    /// private `recompose`: `cur` at child slot `position`, siblings elsewhere in
    /// increasing slot order, under the shielded domain triple.
    fn recompose_path(mut current: Digest8, path: &ExactPath4) -> Digest8 {
        for level in 0..EXACT_SHIELDED_TREE_DEPTH {
            let position = usize::from(path.positions[level]);
            let mut children = [[BabyBear::ZERO; EXACT_SHIELDED_ROOT_LANES]; TREE_ARITY];
            let mut sib = 0usize;
            for (slot, child) in children.iter_mut().enumerate() {
                if slot == position {
                    *child = current;
                } else {
                    *child = path.siblings[level][sib];
                    sib += 1;
                }
            }
            current = exact_node_digest_in(EXACT_SHIELDED_LINKED_DOMAINS, children);
        }
        current
    }

    /// **The membership path folds a committed note back up to `root8()`** — for
    /// EVERY member of a multi-member set (so the positions are non-trivial), the
    /// auth path recomposes to the committed root. This is the invariant a
    /// shielded-spend proof relies on: the note's real place in the committed tree,
    /// pinned to `root8()`.
    #[test]
    fn membership_path_recomposes_to_root8() {
        let mut set = ShieldedNoteSet::new();
        // Reverse-insert so the append order is not the key-sorted order and the
        // members land at non-trivial physical slots (multi-level positions).
        let mut cms: Vec<ShieldedNoteCommitment> = (1u8..=5).map(make_commitment).collect();
        cms.sort_by_key(|c| c.0);
        cms.reverse();
        for cm in &cms {
            set.insert(*cm).unwrap();
        }
        let root = set.root8();

        let mut saw_multilevel = false;
        for cm in &cms {
            let mp = set
                .membership_path(cm)
                .expect("a committed note has a membership path");
            assert_eq!(
                mp.leaf.addr(),
                ExactTaggedKey::from_raw(cm.0),
                "the leaf address is the note's 32-byte commitment"
            );
            assert_eq!(mp.leaf.value(), 0, "the hiding value column is zero");
            if mp.path.positions[1..].iter().any(|&p| p != 0) {
                saw_multilevel = true;
            }
            let leaf_digest = exact_leaf_digest_in(EXACT_SHIELDED_LINKED_DOMAINS, mp.leaf);
            assert_eq!(
                root.limbs(),
                recompose_path(leaf_digest, &mp.path),
                "the membership path must fold the leaf up to root8()"
            );
        }
        assert!(
            saw_multilevel,
            "vacuity guard: at least one member must sit past level 0 (non-trivial position)"
        );

        // A non-member has no path.
        assert!(
            set.membership_path(&make_commitment(200)).is_none(),
            "a commitment not in the set has no membership path"
        );
    }

    /// **CONTINUITY tooth, restated at the encoding that is actually committed.**
    ///
    /// ⚑ **WHAT CHANGED AND WHY (2026-08-01).** This test used to build the same SET twice
    /// in DIFFERENT insertion orders and assert the roots were equal, on the strength of the
    /// retired sorted-compacted `CanonicalHeapTree8` being order-independent. The exact
    /// append-at-free-index root is order-DEPENDENT **by construction** — the append order
    /// IS the canonical tau sequence (INV-6), the same trade the three sibling accumulators
    /// took on 2026-07-31 — so that assertion is now FALSE, and it should be: two different
    /// append histories over the same set are two different states, and a root that could
    /// not tell them apart would be hiding a reordering.
    ///
    /// The property that continuity actually needs is stated here instead, in two halves:
    /// turn N's after-root equals turn N+1's before-root along the REAL carry (the set is
    /// carried forward, not rebuilt), and a reconstruction from persisted records recovers
    /// it from a hostile storage order — the latter is
    /// `reconstruction_from_records_fixes_the_append_order`, and the seq column is what makes
    /// it hold.
    #[test]
    fn root8_is_cross_turn_continuous_along_the_carry() {
        let base = [make_commitment(10), make_commitment(20)];
        let new_note = make_commitment(30);

        let mut turn_n = ShieldedNoteSet::new();
        for c in &base {
            turn_n.insert(*c).unwrap();
        }
        turn_n.insert(new_note).unwrap();
        let after_root_n = turn_n.root8();

        // Turn N+1's BEFORE state is turn N's AFTER state, carried forward.
        let turn_n1 = turn_n.clone();
        assert_eq!(
            after_root_n,
            turn_n1.root8(),
            "turn N after-root must equal turn N+1 before-root along the carry (INV-2)"
        );

        // And it survives a round-trip through the durable record form, whatever order the
        // store yields the records in.
        let mut records: Vec<([u8; 32], u64)> = turn_n1.iter_in_append_order().collect();
        records.sort_by_key(|(c, _)| *c);
        let rebuilt = ShieldedNoteSet::from_records(records).unwrap();
        assert_eq!(
            after_root_n,
            rebuilt.root8(),
            "the persisted seq column must recover the committed root from a hostile \
             storage order"
        );

        // NON-VACUITY: the root is genuinely order-dependent, so the two assertions above
        // are not free. A different APPEND HISTORY over the identical set is a different
        // committed state.
        let mut reordered = ShieldedNoteSet::new();
        reordered.insert(new_note).unwrap();
        for c in base.iter().rev() {
            reordered.insert(*c).unwrap();
        }
        assert_eq!(
            reordered.iter().copied().collect::<Vec<_>>(),
            turn_n1.iter().copied().collect::<Vec<_>>(),
            "the two sets must hold the identical commitments"
        );
        assert_ne!(
            after_root_n,
            reordered.root8(),
            "the AAFI root is order-DEPENDENT by construction; a root equal across two \
             append histories would mean a reordering is invisible to the commitment"
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

        // The dense physical leaf vector: slot 0 is the BOT sentinel, and append rank `r`
        // sits at slot `r + 1` carrying the raw 32-byte commitment as its address.
        use dregg_circuit::exact_nullifier_aafi::ExactTaggedKey;
        let leaves = set.exact_dense_leaves();
        assert_eq!(leaves.len(), cms.len() + 1);
        assert_eq!(leaves[0].addr(), ExactTaggedKey::Bot);
        for (rank, cm) in cms.iter().enumerate() {
            assert_eq!(
                leaves[rank + 1].addr(),
                ExactTaggedKey::from_raw(cm.0),
                "append rank {rank} must occupy physical slot {}",
                rank + 1
            );
        }
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
