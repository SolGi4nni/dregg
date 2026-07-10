//! Revoked-credential accumulator: an append-only `(credential-nullifier →
//! revocation-height)` map of revoked credentials — the REVOCATION-side sibling
//! of [`crate::nullifier_set::NullifierSet`] and [`crate::commitment_set::CommitmentSet`].
//!
//! When a credential is revoked, its credential nullifier is recorded here
//! TOGETHER with the height at which the revocation took effect — the SAME
//! `(addr, value)` [`dregg_circuit::heap_root::HeapLeaf`] shape the sibling
//! grow-gates use (`HeapLeaf { addr: fold(cred_nul), value: split_u64(height).0
//! }`). The accumulator is therefore an auditable `(credential, revocation
//! height)` record: keeping the height is what makes the committed
//! [`Self::root8`] cross-turn-continuous (turn N's after-root == turn N+1's
//! before-root over the same leaves) AND turns the root into an audit witness —
//! WHEN a credential was revoked is bound into the committed state.
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
//! Uses `BTreeMap<[u8; 32], u64>` internally for O(log N) insert and lookup,
//! iterating keys in sorted order.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::note::NoteError;

/// Append-only `(credential-nullifier → revocation-height)` accumulator of
/// revoked credentials. The revocation-side sibling of
/// [`crate::nullifier_set::NullifierSet`] / [`crate::commitment_set::CommitmentSet`].
/// GROW-ONLY: a duplicate credential is rejected.
///
/// Uses `BTreeMap<[u8; 32], u64>` for O(log N) insert and contains operations
/// and sorted-key iteration. The value is the revocation height — the AUDIT FELT
/// carried into the circuit-faithful [`Self::root8`] leaf, so a different
/// revocation height yields a different committed root.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RevokedSet {
    /// Every revoked credential nullifier mapped to the height at which it was
    /// revoked, kept in a BTreeMap for O(log N) operations and sorted-key
    /// iteration. The value is the audit felt folded into the accumulator leaf.
    revoked: BTreeMap<[u8; 32], u64>,
}

impl RevokedSet {
    /// Create an empty revoked-credential set.
    pub fn new() -> Self {
        Self {
            revoked: BTreeMap::new(),
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
        self.revoked.insert(cred_nul, revocation_height);
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
        self.revoked.get(cred_nul).copied()
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
        self.revoked.iter().map(|(c, v)| (c, *v))
    }

    /// Remove a credential from the set.
    ///
    /// Used ONLY by the turn-journal rollback path to undo a speculative insert
    /// when a turn fails after the revocation was recorded. Outside of rollback
    /// the set is append-only.
    ///
    /// Returns `true` if the credential was present and removed, `false`
    /// otherwise. O(log N) via BTreeMap remove.
    pub fn remove(&mut self, cred_nul: &[u8; 32]) -> bool {
        self.revoked.remove(cred_nul).is_some()
    }

    /// The circuit-faithful node8 leaf for a single `(credential, revocation
    /// height)` — the EXACT [`dregg_circuit::heap_root::HeapLeaf`] shape the
    /// sibling accumulator grow-gates use: `addr` is the folded credential
    /// nullifier felt (`dregg_circuit::effect_vm::fold_bytes32_to_bb`, the SAME
    /// fold the sibling sets apply to their key) and `value` is the revocation
    /// height folded through the circuit's `split_u64(height).0` — the low-30-bit
    /// BabyBear audit felt.
    ///
    /// Both fields are folded through the circuit's OWN
    /// `fold_bytes32_to_bb`/`split_u64` helpers so the encoding cannot drift from
    /// the deployed accumulator: the committed `revoked_root` group is opened
    /// in-circuit against a `CanonicalHeapTree8` built from these leaves, so the
    /// executor-derived accumulator root must fold through the identical leaf
    /// encoding or the published commitment would not match the proof.
    pub fn accumulator_leaf(
        cred_nul: &[u8; 32],
        revocation_height: u64,
    ) -> dregg_circuit::heap_root::HeapLeaf {
        dregg_circuit::heap_root::HeapLeaf {
            addr: dregg_circuit::effect_vm::fold_bytes32_to_bb(cred_nul),
            // The leaf value is `split_u64(revocation_height).0` — the low 30 bits
            // of the audit height as a BabyBear. Fold through the circuit's OWN
            // helper so the encoding cannot drift.
            value: dregg_circuit::effect_vm::split_u64(revocation_height).0,
        }
    }

    /// **The faithful 8-felt (~124-bit) accumulator root of the revoked-credential
    /// set** — the value that BELONGS in the committed rotated state's
    /// `revoked_root` group (the same `Heap8Scheme` slot the canonical Lean's
    /// `toNfAccState { nullifierRoot, revokedRoot }` models), so a light client
    /// can READ revocation off committed state instead of trusting the wire: a
    /// node that has accepted a revocation carries a DIFFERENT `root8` than one
    /// that has not.
    ///
    /// This is the native `CanonicalHeapTree8` (arity-16 sorted-Poseidon2, depth
    /// [`dregg_circuit::heap_root::HEAP_TREE_DEPTH`]) root — built from
    /// [`Self::accumulator_leaf`] over every `(credential, revocation-height)` in
    /// the map. The empty set folds to the native empty root
    /// (`dregg_circuit::heap_root::empty_heap_root_8`).
    pub fn root8(&self) -> dregg_circuit::Faithful8 {
        let leaves: Vec<dregg_circuit::heap_root::HeapLeaf> = self
            .revoked
            .iter()
            .map(|(c, v)| Self::accumulator_leaf(c, *v))
            .collect();
        dregg_circuit::heap_root::CanonicalHeapTree8::new(
            leaves,
            dregg_circuit::heap_root::HEAP_TREE_DEPTH,
        )
        .root8()
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

    /// (a) The empty set's faithful accumulator root is the NATIVE
    /// `CanonicalHeapTree8` empty root — the value a producer must fill for a
    /// no-revocation accumulator.
    #[test]
    fn root8_empty_matches_native_empty_heap_root_8() {
        let set = RevokedSet::new();
        assert_eq!(
            set.root8(),
            dregg_circuit::heap_root::empty_heap_root_8(),
            "an empty revoked set must fold to the native empty node8 root the \
             revoked-credential grow-gate defaults to"
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

    /// (c) **Encoding-match tooth:** `root8` over the set equals a
    /// `CanonicalHeapTree8` built by REPRODUCING the grow-gate's exact after-tree
    /// construction: each inserted leaf is `HeapLeaf { addr:
    /// fold_bytes32_to_bb(cred_nul), value: split_u64(height).0 }`. Both are folded
    /// through the circuit's OWN helpers, so this is genuine byte-identity with the
    /// grow-gate, not a re-assertion of a private formula.
    #[test]
    fn root8_matches_growgate_after_tree_encoding() {
        use dregg_circuit::effect_vm::{fold_bytes32_to_bb, split_u64};
        use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};

        let revocations = [
            (make_cred_nul(7), make_height(7)),
            (make_cred_nul(42), make_height(42)),
            (make_cred_nul(99), make_height(99)),
        ];
        let mut set = RevokedSet::new();
        for (c, h) in &revocations {
            set.insert(*c, *h).unwrap();
        }

        let growgate_leaves: Vec<HeapLeaf> = revocations
            .iter()
            .map(|(c, h)| HeapLeaf {
                addr: fold_bytes32_to_bb(c),
                value: split_u64(*h).0,
            })
            .collect();
        let expected = CanonicalHeapTree8::new(growgate_leaves, HEAP_TREE_DEPTH).root8();

        assert_eq!(
            set.root8(),
            expected,
            "root8 must fold through the EXACT (addr, value) node8 leaf encoding the \
             deployed revoked-credential grow-gate inserts"
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

    /// (e) **CONTINUITY tooth:** turn N's *after*-root over `S ∪ {cred, height}`
    /// equals turn N+1's *before*-root over the same set (insertion-order-independent
    /// — a BTreeMap sorts).
    #[test]
    fn root8_is_cross_turn_continuous() {
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

        let mut turn_n1 = RevokedSet::new();
        turn_n1.insert(new_revocation.0, new_revocation.1).unwrap();
        for (c, h) in base.iter().rev() {
            turn_n1.insert(*c, *h).unwrap();
        }
        let before_root_n1 = turn_n1.root8();

        assert_eq!(
            after_root_n, before_root_n1,
            "turn N after-root must equal turn N+1 before-root over the same \
             (credential, height) set (INV-2 continuity, insertion-order-independent)"
        );
    }
}
