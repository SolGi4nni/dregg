//! Revoked-credential accumulator: an append-only `(credential-nullifier →
//! revocation-height)` map of revoked credentials — the REVOCATION-side sibling
//! of [`crate::nullifier_set::NullifierSet`] and [`crate::commitment_set::CommitmentSet`].
//!
//! When a credential is revoked, its credential nullifier is recorded here TOGETHER with the
//! height at which the revocation took effect. The accumulator is therefore an auditable
//! `(credential, revocation height)` record, and the root is an audit witness — WHEN a
//! credential was revoked is bound into the committed state.
//!
//! ⚑ **THE COMMITTED LEAF, 2026-07-31.** [`RevokedSet::root8`] is the exact tagged LINKED-LEAF
//! root `FRI2 ‖ addr17 ‖ value4 ‖ next17`, domain-separated from both note accumulators. It
//! replaced `HeapLeaf::entry(fold_bytes32_to_bb(cred_nul), split_u64(height).0)`, whose
//! credential was a 256→31-bit fold and whose height was the low 30 bits — so the audit witness
//! could not distinguish a revocation at height `h` from one at `h + 2^30`.
//!
//! ⚠ The committed root is APPEND-ORDER dependent (it is the AAFI fold). Reconstruction must go
//! through the persisted `seq` column — [`RevokedSet::from_records`].
//!
//! WHY THIS EXISTS: the runtime authorization gate today trusts a WIRE-SUPPLIED
//! revocation root (`authorize.rs` `proof.revocation_channel`), so a node can
//! supply an empty root and the commitment faithfully records the lie — a light
//! client cannot detect it (Lean hole #3 / #139: `revoked` must be read off
//! committed state, NOT the wire-supplied `NodeAuth.rev`). The canonical Lean
//! already models `revokedRoot` on the same `Heap8Scheme` accumulator as
//! `nullifierRoot` (`toNfAccState { nullifierRoot, revokedRoot }`;
//! `kernel_revoked_gate_fails` proves fail-closed). This is the native runtime
//! registry that Lean model assumes.
//!
//! GROW-ONLY: revocation is monotone — a credential once revoked stays revoked.
//! A duplicate revocation is rejected (a credential cannot be revoked twice),
//! the revocation-side analog of the nullifier double-spend / commitment
//! duplicate gate. Like the commitments accumulator there is no
//! non-membership-proof machinery: the revoked set is a pure grow-only map whose
//! ONLY committed observable is the felt-domain [`Self::root8`].
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

use serde::{Deserialize, Serialize};

use crate::note::NoteError;

/// A stored accumulator entry: the revocation-height `value` PLUS the entry's
/// **append sequence** (`seq`) — the gap-#5 AAFI (append-at-free-index) order
/// column. AAFI roots are insertion-order-dependent (the append order IS the
/// canonical tau revocation sequence, INV-6), so the store persists WHERE in
/// the append sequence each entry landed; a reconstruction replays the
/// records sorted by `seq` and recovers the identical AAFI layout every time.
/// The sorted-compacted [`RevokedSet::root8`] layer ignores `seq` (order-
/// independent), so this is purely ADDITIVE.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct AppendRecord {
    /// The revocation height (the audit felt folded into the leaf).
    value: u64,
    /// 0-based append index: this entry was the `seq`-th revocation appended.
    /// Mirrors [`dregg_circuit::heap_root::CanonicalHeapTree8::next_free_index`]
    /// semantics — the entry with append rank `seq` occupies physical AAFI
    /// slot `seq + 1` (slot 0 is the MIN sentinel).
    seq: u64,
}

/// Append-only `(credential-nullifier → revocation-height)` accumulator of
/// revoked credentials. The revocation-side sibling of
/// [`crate::nullifier_set::NullifierSet`] / [`crate::commitment_set::CommitmentSet`].
/// GROW-ONLY: a duplicate credential is rejected.
///
/// Uses `BTreeMap<[u8; 32], (value, seq)>` for O(log N) insert and contains operations
/// and sorted-key iteration. The value is the revocation height — the AUDIT FELT
/// carried into the circuit-faithful [`Self::root8`] leaf, so a different
/// revocation height yields a different committed root.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RevokedSet {
    /// Every revoked credential nullifier mapped to the height at which it was
    /// revoked AND its append sequence, kept in a BTreeMap for O(log N)
    /// operations and sorted-key iteration. The value is the audit felt folded
    /// into the accumulator leaf; the seq is the AAFI append-order column.
    revoked: BTreeMap<[u8; 32], AppendRecord>,
    /// The next append sequence number (0-based). Every insert records the
    /// current `next_seq` and bumps it — the store-side mirror of the AAFI
    /// tree's `next_free_index` cursor (offset by 1 for the MIN sentinel).
    next_seq: u64,
}

/// The revocation-side exact tagged-linked-leaf domain triple: `FRI2`/`FRN2`/`FRE2`.
///
/// Distinct from the note accumulators' `FNI2`/`FNN2`/`FNE2` (spend) and `FCI2`/`FCN2`/`FCE2`
/// (create): three different statements about three different sets, so one tree's opening — or
/// its EMPTY root — cannot be replayed as another's.
pub const EXACT_REVOKED_LINKED_DOMAINS: ExactLinkedDomains = ExactLinkedDomains {
    leaf: 0x4652_4932,  // `FRI2`
    node: 0x4652_4e32,  // `FRN2`
    empty: 0x4652_4532, // `FRE2`
};

impl RevokedSet {
    /// Create an empty revoked-credential set.
    pub fn new() -> Self {
        Self {
            revoked: BTreeMap::new(),
            next_seq: 0,
        }
    }

    /// Number of revoked credentials in the set.
    pub fn len(&self) -> usize {
        self.revoked.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.revoked.is_empty()
    }

    /// Record a credential nullifier as revoked at `revocation_height`. Returns
    /// error if the credential is already present (double-revoke).
    ///
    /// The `revocation_height` is the AUDIT FELT — the height at which the
    /// revocation took effect. It is folded into the grow-gate leaf
    /// (`split_u64(height).0`); carrying it here is what keeps [`Self::root8`]
    /// cross-turn-continuous AND makes the committed root an audit witness of
    /// WHEN each credential was revoked.
    ///
    /// O(log N) via BTreeMap insertion (does not overwrite on collision, so a
    /// double-revoke never mutates the recorded height).
    pub fn insert(&mut self, cred_nul: [u8; 32], revocation_height: u64) -> Result<(), NoteError> {
        if self.revoked.contains_key(&cred_nul) {
            return Err(NoteError::AlreadyRevoked {
                credential_nullifier: cred_nul,
            });
        }
        self.revoked.insert(
            cred_nul,
            AppendRecord {
                value: revocation_height,
                seq: self.next_seq,
            },
        );
        self.next_seq += 1;
        Ok(())
    }

    /// Check if a credential nullifier is in the set (credential is revoked).
    ///
    /// O(log N) via BTreeMap key lookup.
    pub fn contains(&self, cred_nul: &[u8; 32]) -> bool {
        self.revoked.contains_key(cred_nul)
    }

    /// The revocation height recorded for a credential, if present.
    pub fn value_of(&self, cred_nul: &[u8; 32]) -> Option<u64> {
        self.revoked.get(cred_nul).map(|r| r.value)
    }

    /// The append sequence recorded for a credential, if present — the 0-based
    /// rank at which it was appended (the canonical tau revocation order,
    /// INV-6). This is the column a persistence layer must carry per entry so
    /// an AAFI (order-dependent) root is reconstructible; see
    /// [`Self::from_records`].
    pub fn seq_of(&self, cred_nul: &[u8; 32]) -> Option<u64> {
        self.revoked.get(cred_nul).map(|r| r.seq)
    }

    /// Iterate the revoked credentials in sorted key order (the universal-memory
    /// projection walks the set: every revoked credential is a present
    /// `revoked`-domain cell).
    pub fn iter(&self) -> impl Iterator<Item = &[u8; 32]> {
        self.revoked.keys()
    }

    /// Iterate `(credential, revocation-height)` pairs in sorted key order — the
    /// full accumulator record (the projection/persistence path that must carry
    /// the height to reconstruct a matching [`Self::root8`]).
    pub fn iter_with_values(&self) -> impl Iterator<Item = (&[u8; 32], u64)> {
        self.revoked.iter().map(|(c, r)| (c, r.value))
    }

    /// Iterate the full `(credential, height, seq)` records **in append order**
    /// (ascending `seq`) — the canonical tau revocation sequence (INV-6). This
    /// is BOTH the persistence export (each record carries its seq column) and
    /// the AAFI replay order: a reconstruction that re-applies these records
    /// in this order rebuilds the order-dependent AAFI tree identically.
    ///
    /// Ties on `seq` (impossible for records minted by [`Self::insert`], which
    /// assigns unique seqs; possible only for hand-built record sets) are
    /// broken deterministically by the credential key, so the order is TOTAL.
    pub fn iter_in_append_order(&self) -> impl Iterator<Item = ([u8; 32], u64, u64)> {
        let mut records: Vec<([u8; 32], u64, u64)> = self
            .revoked
            .iter()
            .map(|(c, r)| (*c, r.value, r.seq))
            .collect();
        records.sort_by_key(|(c, _, seq)| (*seq, *c));
        records.into_iter()
    }

    /// Reconstruct the set from durable `(credential, height, seq)` records,
    /// **fixing the append order** from the persisted seq column: records are
    /// replayed sorted by `(seq, key)` and keep their persisted seqs verbatim,
    /// so the reconstruction is deterministic in the canonical tau order no
    /// matter what order the storage layer yields the records in. This is the
    /// AAFI-order reconstruction path — under AAFI the accumulator root
    /// depends on the append order, so "reconstruct from the store" must
    /// recover the ORIGINAL order, not the store's key order.
    ///
    /// Returns the already-revoked error on a duplicate credential key.
    pub fn from_records(
        records: impl IntoIterator<Item = ([u8; 32], u64, u64)>,
    ) -> Result<Self, NoteError> {
        let mut sorted: Vec<([u8; 32], u64, u64)> = records.into_iter().collect();
        sorted.sort_by_key(|(c, _, seq)| (*seq, *c));
        let mut set = Self::new();
        for (cred_nul, value, seq) in sorted {
            if set.revoked.contains_key(&cred_nul) {
                return Err(NoteError::AlreadyRevoked {
                    credential_nullifier: cred_nul,
                });
            }
            set.revoked.insert(cred_nul, AppendRecord { value, seq });
            set.next_seq = set.next_seq.max(seq + 1);
        }
        Ok(set)
    }

    /// The canonical APPEND-ORDERED `(credential, revocation height)` record list — the input
    /// the committed [`Self::root8`] folds. Physical slot 0 is the permanent `BOT` sentinel; the
    /// record at rank `r` occupies slot `r + 1`.
    fn exact_append_records(&self) -> Vec<([u8; 32], u64)> {
        self.iter_in_append_order()
            .map(|(credential, height, _)| (credential, height))
            .collect()
    }

    /// The committed accumulator's **dense physical leaf vector** — exactly what [`Self::root8`]
    /// hashes, indexed by physical slot. Every leaf's `value()` is the FULL `u64` revocation
    /// height and every leaf's `next_addr()` is the next larger present credential (the absence
    /// bracket the `spendAncestorFreshOp` `.absent` open straddles).
    pub fn exact_dense_leaves(&self) -> Vec<dregg_circuit::exact_nullifier_aafi::ExactLinkedLeaf> {
        dregg_circuit::exact_nullifier_aafi::exact_linked_dense_leaves(&self.exact_append_records())
            .expect("the revoked map's keys are unique and within the 4^16 tree capacity")
    }

    /// The physical AAFI slot the NEXT append would occupy: `len() + 1`
    /// (slot 0 is the MIN sentinel) — the store-side mirror of
    /// [`dregg_circuit::heap_root::CanonicalHeapTree8::next_free_index`] for a
    /// tree replayed from [`Self::exact_dense_leaves`].
    pub fn aafi_next_free_index(&self) -> usize {
        self.revoked.len() + 1
    }

    /// Remove a credential from the set.
    ///
    /// Used ONLY by the turn-journal rollback path to undo a speculative insert
    /// when a turn fails after the revocation was recorded. Outside of rollback
    /// the set is append-only.
    ///
    /// Returns `true` if the credential was present and removed, `false`
    /// otherwise. O(log N) via BTreeMap remove (plus an O(N) append-cursor
    /// recompute — rollback is rare and off the hot path).
    ///
    /// The append cursor rolls back with the entry: `next_seq` is recomputed
    /// to one past the highest surviving seq, so rolling back the LAST append
    /// frees its seq and the re-executed turn's insert lands at the SAME
    /// append rank — the deterministic tau order is preserved across a
    /// speculative-insert rollback.
    pub fn remove(&mut self, cred_nul: &[u8; 32]) -> bool {
        let removed = self.revoked.remove(cred_nul).is_some();
        if removed {
            self.next_seq = self.revoked.values().map(|r| r.seq + 1).max().unwrap_or(0);
        }
        removed
    }

    /// **THE committed accumulator root of the revoked-credential set** — the exact tagged
    /// LINKED-LEAF (indexed-Merkle) append-at-free-index root, `FRI2 ‖ addr17 ‖ value4 ‖ next17`
    /// at depth 16, arity 4, eight BabyBear lanes. Domain-separated from both note accumulators.
    ///
    /// ⚑ **WHAT THIS REPLACED, AND WHY THE STATED BLOCKER WAS NOT REAL.** Until 2026-07-31 this
    /// folded `HeapLeaf::entry(fold_bytes32_to_bb(cred_nul), split_u64(height).0)` through a
    /// `CanonicalHeapTree8` — a 256→31-bit credential fold and a 64→30-bit height truncation —
    /// and its doc comment said the committed `revoked_root` group "is opened in-circuit against
    /// a `CanonicalHeapTree8` built from these leaves", so the encoding could not move.
    /// **The in-circuit open is real, but it is never handed THESE leaves:** every live producer
    /// passes `SpendRevocationWitness::undelegated(&[])` — an EMPTY revoked leaf vector
    /// (`sdk/src/full_turn_proof.rs:584`, `sdk/src/cipherclerk.rs:5791`,
    /// `turn/src/executor/proof_verify.rs:1321`). The executor's revoked accumulator has never
    /// reached a circuit, so no VK rotates and no descriptor is re-emitted; this is a re-genesis
    /// (`CANONICAL_STATE_SCHEMA_EPOCH` 14 → 15) exactly like its two note siblings.
    ///
    /// The new leaf carries the credential as a tag plus sixteen little-endian `u16` limbs
    /// (`2^256` on the nose) and the revocation height as four (`2^64`, so an audit height above
    /// `2^30` is no longer indistinguishable from `height mod 2^30`), plus a full-width
    /// `next_addr` pointer — the bracket a non-membership opening straddles.
    pub fn root8(&self) -> Faithful8 {
        let records = self.exact_append_records();
        let lanes = exact_linked_append_root8(EXACT_REVOKED_LINKED_DOMAINS, &records).expect(
            "the revoked map's keys are unique by construction and its length is bounded by the \
             4^16 tree capacity",
        );
        let mut bytes = [0u8; 32];
        for (lane, felt) in lanes.iter().enumerate() {
            bytes[lane * 4..lane * 4 + 4].copy_from_slice(&felt.as_u32().to_le_bytes());
        }
        Faithful8::from_bytes32(&bytes)
    }
}

impl Default for RevokedSet {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_cred_nul(seed: u8) -> [u8; 32] {
        let mut c = [0u8; 32];
        c[0] = seed;
        c[1] = seed.wrapping_mul(5).wrapping_add(7);
        c
    }

    /// A deterministic revocation height for a seed — distinct per credential so
    /// the `(credential, height)` leaves are genuinely audit-felt-carrying.
    fn make_height(seed: u8) -> u64 {
        3_000 + (seed as u64) * 13
    }

    #[test]
    fn test_revoked_set_insert_and_contains() {
        let mut set = RevokedSet::new();
        let c = make_cred_nul(1);

        assert!(!set.contains(&c));
        set.insert(c, make_height(1)).unwrap();
        assert!(set.contains(&c));
        assert_eq!(set.value_of(&c), Some(make_height(1)));
    }

    #[test]
    fn test_revoked_set_duplicate_rejected() {
        let mut set = RevokedSet::new();
        let c = make_cred_nul(1);

        set.insert(c, make_height(1)).unwrap();
        // A double-revoke is rejected AND must not overwrite the recorded height.
        let result = set.insert(c, 999_999);
        assert_eq!(
            result,
            Err(NoteError::AlreadyRevoked {
                credential_nullifier: c
            })
        );
        assert_eq!(set.value_of(&c), Some(make_height(1)));
    }

    #[test]
    fn test_revoked_set_multiple_inserts() {
        let mut set = RevokedSet::new();
        for i in 0..10 {
            set.insert(make_cred_nul(i), make_height(i)).unwrap();
        }
        assert_eq!(set.len(), 10);
        for i in 0..10 {
            assert!(set.contains(&make_cred_nul(i)));
        }
    }

    #[test]
    fn test_revoked_set_remove_rollback() {
        let mut set = RevokedSet::new();
        let c = make_cred_nul(1);
        set.insert(c, make_height(1)).unwrap();
        assert!(set.remove(&c));
        assert!(!set.contains(&c));
        // Re-insertable after rollback (the set is grow-only outside rollback).
        set.insert(c, make_height(1)).unwrap();
        assert!(set.contains(&c));
    }

    /// (a) The empty set is the lone `BOT(value=0, next=TOP)` sentinel under the `FRI2` domain —
    /// NOT an empty tree, and (since 2026-07-31) NOT the native `CanonicalHeapTree8` empty root.
    #[test]
    fn root8_empty_is_the_bot_sentinel_tree_and_is_domain_separated() {
        use dregg_circuit::exact_nullifier_aafi::ExactTaggedKey;

        let set = RevokedSet::new();
        let leaves = set.exact_dense_leaves();
        assert_eq!(leaves.len(), 1);
        assert_eq!(leaves[0].addr(), ExactTaggedKey::Bot);
        assert_eq!(leaves[0].next_addr(), ExactTaggedKey::Top);

        assert_ne!(
            set.root8(),
            dregg_circuit::heap_root::empty_heap_root_8(),
            "the committed revoked root is the exact linked-leaf tree, not the legacy heap tree"
        );
        assert_ne!(
            set.root8(),
            crate::nullifier_set::NullifierSet::new().root8(),
            "FRI2 must be domain-separated from FNI2 even at the empty root"
        );
        assert_ne!(
            set.root8(),
            crate::commitment_set::CommitmentSet::new().root8(),
            "FRI2 must be domain-separated from FCI2 even at the empty root"
        );
    }

    /// (b) A non-empty accumulator fills ALL 8 lanes of the committed revoked-root
    /// group: the completion lanes (`limbs()[1..8]`) are NON-ZERO and the root
    /// ADVANCES on every distinct insert (the light-client observable: a node that
    /// accepted a revocation carries a different root).
    #[test]
    fn root8_grows_nonzero_completion_lanes_and_advances() {
        use dregg_circuit::field::BabyBear;

        let mut set = RevokedSet::new();
        let empty8 = set.root8();

        set.insert(make_cred_nul(1), make_height(1)).unwrap();
        let one8 = set.root8();
        assert_ne!(
            empty8, one8,
            "revoking a credential must ADVANCE the committed accumulator root"
        );
        assert!(
            one8.limbs()[1..8].iter().any(|f| *f != BabyBear::ZERO),
            "a non-empty accumulator's completion lanes must be NON-ZERO — the \
             whole point of the faithful 8-felt fill"
        );

        set.insert(make_cred_nul(2), make_height(2)).unwrap();
        let two8 = set.root8();
        assert_ne!(
            one8, two8,
            "a second distinct revocation must again advance the root (monotone accumulator)"
        );
    }

    /// (c) ⚑ **A2/A3 CLOSED ON THE REVOCATION AUDIT ROOT, AND IT ROUND-TRIPS.** The retired
    /// encoding folded `HeapLeaf::entry(fold_bytes32_to_bb(cred_nul), split_u64(height).0)`, so
    /// the committed audit witness was `2^30`-periodic in the revocation HEIGHT and blind to a
    /// free `+p` mutation of the credential's top four bytes. Both poles, plus the decode that
    /// separates a binding from a scramble.
    #[test]
    fn the_committed_revoked_root_binds_the_full_credential_and_height() {
        use dregg_circuit::effect_vm::{fold_bytes32_to_bb, split_u64};
        use dregg_circuit::field::BABYBEAR_P;
        use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};

        let legacy = |records: &[([u8; 32], u64)]| {
            CanonicalHeapTree8::new(
                records
                    .iter()
                    .map(|(c, h)| HeapLeaf::entry(fold_bytes32_to_bb(c), split_u64(*h).0))
                    .collect(),
                HEAP_TREE_DEPTH,
            )
            .root8()
        };

        // A3 — the revocation height above the 2^30 period.
        let cred = make_cred_nul(3);
        let low = 17u64;
        let aliased = low + (1u64 << 30);
        assert_eq!(
            legacy(&[(cred, low)]),
            legacy(&[(cred, aliased)]),
            "vacuity guard: the RETIRED revoked root really was 2^30-periodic in the height"
        );
        let mut low_set = RevokedSet::new();
        low_set.insert(cred, low).unwrap();
        let mut alias_set = RevokedSet::new();
        alias_set.insert(cred, aliased).unwrap();
        assert_ne!(low_set.root8(), alias_set.root8());
        assert_eq!(low_set.exact_dense_leaves()[1].value(), low);
        assert_eq!(alias_set.exact_dense_leaves()[1].value(), aliased);

        // A2 — the credential's high bytes.
        let mut base_bytes = [0u8; 32];
        base_bytes[0] = 0xA7;
        let mut high_bytes = base_bytes;
        high_bytes[28..32].copy_from_slice(&BABYBEAR_P.to_le_bytes());
        assert_eq!(
            fold_bytes32_to_bb(&base_bytes),
            fold_bytes32_to_bb(&high_bytes),
            "vacuity guard: the two credentials must collide in the one-felt fold"
        );
        assert_eq!(legacy(&[(base_bytes, 9)]), legacy(&[(high_bytes, 9)]));
        let mut base_set = RevokedSet::new();
        base_set.insert(base_bytes, 9).unwrap();
        let mut high_set = RevokedSet::new();
        high_set.insert(high_bytes, 9).unwrap();
        assert_ne!(base_set.root8(), high_set.root8());
        assert_eq!(
            base_set.exact_dense_leaves()[1].addr().real_raw_bytes(),
            Some(base_bytes)
        );
        assert_eq!(
            high_set.exact_dense_leaves()[1].addr().real_raw_bytes(),
            Some(high_bytes)
        );
    }

    /// (d) **The `revocation_height` (audit felt) is load-bearing:** two
    /// accumulators over the SAME credential but DIFFERENT revocation heights fold
    /// to DIFFERENT `root8`s. This is the regression guard against a `value: 1`
    /// degeneration — the height must be genuinely bound into the committed root so
    /// WHEN a credential was revoked is an audit witness.
    #[test]
    fn root8_depends_on_the_revocation_height() {
        let c = make_cred_nul(3);

        let mut lo = RevokedSet::new();
        lo.insert(c, 5).unwrap();

        let mut hi = RevokedSet::new();
        hi.insert(c, 500).unwrap();

        assert_ne!(
            lo.root8(),
            hi.root8(),
            "the committed accumulator root MUST depend on the revocation height — \
             the audit felt (a value:1 degeneration would erase it)"
        );
    }

    /// (e) **CONTINUITY tooth (INV-2), RESTATED AT THE APPEND-ORDER ROOT.** Turn N's after-root
    /// equals turn N+1's before-root over the same history, reconstructed through the persisted
    /// `seq` column — which is the path every real replay takes. The committed root is now the
    /// AAFI fold, so it is append-order DEPENDENT; that is asserted as the second pole.
    #[test]
    fn root8_is_cross_turn_continuous_through_the_append_order() {
        let base = [
            (make_cred_nul(10), make_height(10)),
            (make_cred_nul(20), make_height(20)),
        ];
        let new_revocation = (make_cred_nul(30), make_height(30));

        let mut turn_n = RevokedSet::new();
        for (c, h) in &base {
            turn_n.insert(*c, *h).unwrap();
        }
        turn_n.insert(new_revocation.0, new_revocation.1).unwrap();
        let after_root_n = turn_n.root8();

        let mut records: Vec<([u8; 32], u64, u64)> = turn_n.iter_in_append_order().collect();
        records.sort_by_key(|(c, _, _)| *c);
        let turn_n1 = RevokedSet::from_records(records).unwrap();
        assert_eq!(
            after_root_n,
            turn_n1.root8(),
            "turn N after-root must equal turn N+1 before-root over the same history, \
             reconstructed through the persisted seq column"
        );

        let mut reordered = RevokedSet::new();
        reordered
            .insert(new_revocation.0, new_revocation.1)
            .unwrap();
        for (c, h) in base.iter().rev() {
            reordered.insert(*c, *h).unwrap();
        }
        assert_ne!(
            after_root_n,
            reordered.root8(),
            "the committed root is append-order dependent — a different revocation sequence \
             over the same set is a different history"
        );
    }

    /// **A8 tooth — the append order is RECORDED:** seqs are assigned in
    /// insertion order regardless of key sort order, and the append-order
    /// iteration / AAFI leaf sequence follow the INSERTION order. Non-vacuous:
    /// the keys are inserted in reverse-sorted order so the orders differ.
    #[test]
    fn append_seq_records_insertion_order_not_key_order() {
        let mut creds: Vec<[u8; 32]> = (1u8..=4).map(make_cred_nul).collect();
        creds.sort();
        creds.reverse();

        let mut set = RevokedSet::new();
        for (i, c) in creds.iter().enumerate() {
            set.insert(*c, 100 + i as u64).unwrap();
            assert_eq!(
                set.seq_of(c),
                Some(i as u64),
                "the i-th insert must record append seq i"
            );
        }
        assert_eq!(set.aafi_next_free_index(), creds.len() + 1);

        let append_order: Vec<[u8; 32]> = set.iter_in_append_order().map(|(c, _, _)| c).collect();
        assert_eq!(
            append_order, creds,
            "append-order iteration must follow INSERTION order"
        );
        let key_order: Vec<[u8; 32]> = set.iter().copied().collect();
        assert_ne!(
            append_order, key_order,
            "vacuity guard: insertion order must differ from sorted-key order"
        );

        let expected_leaves: Vec<([u8; 32], u64)> = creds
            .iter()
            .enumerate()
            .map(|(i, c)| (*c, 100 + i as u64))
            .collect::<Vec<_>>();
        let leaves = set.exact_dense_leaves();
        for (i, (cred, height)) in expected_leaves.iter().enumerate() {
            assert_eq!(leaves[i + 1].addr().real_raw_bytes(), Some(*cred));
            assert_eq!(leaves[i + 1].value(), *height);
        }
    }

    /// **A8 tooth — reconstruction FIXES the append order:** records exported
    /// with their seq column and handed back sorted by KEY (the hostile
    /// storage order) reconstruct the IDENTICAL append order, AAFI leaf
    /// sequence, seqs, and (sorted-compacted) root8.
    #[test]
    fn reconstruction_from_records_fixes_the_append_order() {
        let mut creds: Vec<[u8; 32]> = (1u8..=5).map(make_cred_nul).collect();
        creds.sort();
        creds.reverse();

        let mut original = RevokedSet::new();
        for (i, c) in creds.iter().enumerate() {
            original.insert(*c, make_height(i as u8)).unwrap();
        }

        let mut records: Vec<([u8; 32], u64, u64)> = original.iter_in_append_order().collect();
        records.sort_by_key(|(c, _, _)| *c);

        let rebuilt = RevokedSet::from_records(records).unwrap();
        assert_eq!(
            rebuilt.iter_in_append_order().collect::<Vec<_>>(),
            original.iter_in_append_order().collect::<Vec<_>>(),
            "reconstruction must recover the CANONICAL append order from the \
             persisted seq column, not the storage yield order"
        );
        assert_eq!(rebuilt.exact_dense_leaves(), original.exact_dense_leaves());
        for c in &creds {
            assert_eq!(rebuilt.seq_of(c), original.seq_of(c));
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
    /// double-revoke gate as the live insert path).
    #[test]
    fn from_records_rejects_duplicate_keys() {
        let c = make_cred_nul(1);
        match RevokedSet::from_records([(c, 5, 0), (c, 7, 1)]) {
            Err(NoteError::AlreadyRevoked {
                credential_nullifier,
            }) => assert_eq!(credential_nullifier, c),
            other => panic!("duplicate key must be refused, got {other:?}"),
        }
    }

    /// **A8 tooth — rollback frees the LAST seq:** removing the most recent
    /// speculative insert rolls the append cursor back, so the re-executed
    /// turn's insert lands at the SAME append rank.
    #[test]
    fn rollback_frees_the_last_append_seq() {
        let mut set = RevokedSet::new();
        let a = make_cred_nul(1);
        let b = make_cred_nul(2);
        let c = make_cred_nul(3);

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
