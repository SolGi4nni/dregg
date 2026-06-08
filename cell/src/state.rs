use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// A generic 32-byte field element.
/// Could represent a BabyBear element, a BLAKE3 hash, a scalar, etc.
pub type FieldElement = [u8; 32];

/// The zero field element.
pub const FIELD_ZERO: FieldElement = [0u8; 32];

/// Number of user-defined state slots per cell.
pub const STATE_SLOTS: usize = 8;

/// Visibility level for a cell state field.
///
/// Controls progressive disclosure: fields can be fully public, committed (hidden
/// behind a hash), or selectively disclosable (committed but provable via ZK).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldVisibility {
    /// Value stored in plaintext — anyone can read it.
    Public,
    /// Only a hash commitment is stored publicly. The actual value is private.
    Committed,
    /// Committed, but the holder can produce membership/predicate proofs
    /// over the value without revealing it.
    SelectivelyDisclosable,
}

impl Default for FieldVisibility {
    fn default() -> Self {
        FieldVisibility::Public
    }
}

/// The mutable state of an agent cell.
///
/// Audit P0-1 sealing: `nonce`, `balance`, `proved_state`, and
/// `delegation_epoch` are `pub(crate)` — external code reads them via
/// accessors ([`CellState::nonce`], [`CellState::balance`],
/// [`CellState::proved_state`], [`CellState::delegation_epoch`]) and mutates
/// them only through `apply_balance_change`, `increment_nonce`,
/// `bump_delegation_epoch`, and `set_proved_state`. `fields[]`,
/// `field_visibility[]`, and `commitments[]` remain public arrays because the
/// executor mutates them by index in tight loops.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellState {
    /// 8 user-defined state fields (like Mina's app_state).
    pub fields: [FieldElement; STATE_SLOTS],
    /// Visibility level for each field slot.
    pub field_visibility: [FieldVisibility; STATE_SLOTS],
    /// Hash commitments for non-public fields (BLAKE3 hash of value || nonce).
    /// `None` for Public fields, `Some(hash)` for Committed/SelectivelyDisclosable.
    pub commitments: [Option<[u8; 32]>; STATE_SLOTS],
    /// Monotonically increasing action counter. Sealed (P0-1); mutate via
    /// `increment_nonce`, read via `nonce()`.
    pub(crate) nonce: u64,
    /// Computron balance (execution budget). Sealed (P0-1); mutate via
    /// `apply_balance_change`, read via `balance()`.
    pub(crate) balance: u64,
    /// Whether all 8 state fields were last set by a verified proof.
    /// Becomes `true` only when ALL 8 fields are set by a single proof-authorized action.
    /// Becomes `false` if any field is modified by a non-proof authorization.
    /// Sealed (P0-1); mutate via `set_proved_state`, read via `proved_state()`.
    pub(crate) proved_state: bool,
    /// Delegation epoch counter. Parent cells bump this to signal their children
    /// should refresh their capability snapshots. Children whose snapshot epoch is
    /// behind the parent's current epoch are considered stale.
    /// Sealed (P0-1); mutate via `bump_delegation_epoch`, read via
    /// `delegation_epoch()`.
    #[serde(default)]
    pub(crate) delegation_epoch: u64,
    /// Stage 1 / `DESIGN-captp-integration.md` §4.1: per-cell CapTP swiss
    /// table Merkle root. Initialised to the empty-tree sentinel; populated
    /// by `Effect::ExportSturdyRef` and `Effect::EnlivenRef` in Stage 7.
    ///
    /// Included in `compute_canonical_state_commitment` so the cell's
    /// state commitment binds its CapTP exports.
    #[serde(default)]
    pub swiss_table_root: [u8; 32],
    /// Stage 1 / `DESIGN-captp-integration.md` §4.3: per-cell CapTP refcount
    /// table Merkle root (cross-federation reference counts). Initialised
    /// to the empty-tree sentinel; populated by `Effect::ExportSturdyRef`
    /// and `Effect::DropRef` in Stage 7.
    #[serde(default)]
    pub refcount_table_root: [u8; 32],
    /// `_RECORD-LAYER-UPGRADE.md` §B (Stage 0): the committed root of the
    /// **user-field MAP** — an unbounded `key → FieldElement` accumulator over
    /// keys `>= STATE_SLOTS` (8). The hybrid unsqueeze of the 8-fixed-slot
    /// cell: keys `0..7` stay in `fields[]` (existing access byte-identical);
    /// keys `>= 8` live in [`fields_map`] and are committed here.
    ///
    /// `fields_root` is the **committed** root (the on-cell/in-circuit
    /// witness); [`fields_map`] is the prover-side store whose digest this is.
    /// Initialised to [`empty_fields_root`] — the digest of the empty map — so
    /// a legacy cell (no map entries) carries the FIXED empty-map constant and
    /// its canonical commitment is unchanged when this is later folded in
    /// (Stage 1). `#[serde(default)]` keeps every existing serialized cell
    /// deserializing (the additive pattern already used for
    /// `swiss_table_root`/`refcount_table_root`).
    ///
    /// Stage 0 is strictly additive: this is NOT yet absorbed into
    /// `compute_canonical_state_commitment` (that is Stage 1, with a `v2->v3`
    /// bump). It is present, load-bearing for the map read/write path, and
    /// recomputed on every map write.
    #[serde(default = "empty_fields_root")]
    pub fields_root: [u8; 32],
    /// `_RECORD-LAYER-UPGRADE.md` §B.3: the **prover-side witness** store for
    /// the user-field map — the actual `key (>= 8) -> value` entries whose
    /// digest is [`fields_root`]. Not itself committed (its digest is).
    /// `BTreeMap` for a canonical (sorted-key) iteration order so the digest is
    /// deterministic. `#[serde(default)]` ⇒ old cells deserialize with an empty
    /// map.
    #[serde(default)]
    pub fields_map: BTreeMap<u64, FieldElement>,
}

/// Domain-separation context for the user-field-map keyed digest
/// ([`CellState::fields_root`]). Distinct from the canonical-state-commitment
/// context so a map root can never be confused with a full-cell commitment.
pub const FIELDS_ROOT_CONTEXT: &str = "dregg-cell:fields-root v1";

/// The digest of the **empty** user-field map — the fixed `fields_root`
/// constant a legacy (no-overflow) cell carries. Because every legacy cell has
/// the same empty map, this constant is cell-independent: folding it into the
/// canonical commitment is a no-op for legacy cells (the Stage 0 backward-compat
/// keystone, mirrored in Lean by `FieldsMap.fieldsRoot_empty_legacy`).
pub fn empty_fields_root() -> [u8; 32] {
    compute_fields_root(&BTreeMap::new())
}

/// Compute the keyed digest committing a user-field map.
///
/// The Rust shadow of the Lean `FieldsMap.fieldsRoot`
/// (`ListCommit.listDigest` over the user tail): a length-seeded BLAKE3 sponge
/// over the canonically-ordered `(key, value)` leaves. `BTreeMap` iteration is
/// already sorted by key, so the digest is order-canonical and injective enough
/// that two distinct maps cannot share a root (the anti-vacuity guarantee — a
/// `:= 0` stub is forbidden). An empty map yields the fixed [`empty_fields_root`].
pub fn compute_fields_root(map: &BTreeMap<u64, FieldElement>) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(FIELDS_ROOT_CONTEXT);
    // Length prefix (seed): pins the entry count so a drop is rejected.
    hasher.update(&(map.len() as u64).to_le_bytes());
    for (key, value) in map.iter() {
        hasher.update(&key.to_le_bytes());
        hasher.update(value);
    }
    *hasher.finalize().as_bytes()
}

/// The public view of a field — either the actual value (if public) or its commitment hash.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PublicFieldView {
    /// The field value is revealed (public).
    Revealed(FieldElement),
    /// The field value is hidden; only the commitment hash is visible.
    Committed([u8; 32]),
}

impl CellState {
    /// Read accessor for `nonce`. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use dregg_cell::CellState;
    /// let mut s = CellState::new(0);
    /// s.nonce = 42;
    /// ```
    #[inline]
    pub fn nonce(&self) -> u64 {
        self.nonce
    }

    /// Read accessor for `balance`. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use dregg_cell::CellState;
    /// let mut s = CellState::new(0);
    /// s.balance = u64::MAX;
    /// ```
    #[inline]
    pub fn balance(&self) -> u64 {
        self.balance
    }

    /// Read accessor for `proved_state`. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use dregg_cell::CellState;
    /// let mut s = CellState::new(0);
    /// s.proved_state = true;
    /// ```
    #[inline]
    pub fn proved_state(&self) -> bool {
        self.proved_state
    }

    /// Read accessor for `delegation_epoch`. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use dregg_cell::CellState;
    /// let mut s = CellState::new(0);
    /// s.delegation_epoch = 7;
    /// ```
    #[inline]
    pub fn delegation_epoch(&self) -> u64 {
        self.delegation_epoch
    }

    /// Set the `proved_state` flag. Sealed-write accessor (P0-1).
    ///
    /// The executor calls this after applying a proof-authorized action: it
    /// passes `true` only when all 8 fields were set by a single proof, and
    /// `false` when any non-proof authorization touched the cell.
    #[inline]
    pub fn set_proved_state(&mut self, value: bool) {
        self.proved_state = value;
    }

    /// Raw write of `balance`. Sealed-write accessor (P0-1).
    ///
    /// **Low-level**: callers are expected to be the executor's effect-apply
    /// pipeline or the journal-rollback path. Application code should never
    /// touch this — go through `Effect::Transfer`/`NoteSpend`/`NoteCreate` via
    /// the executor so authorization and conservation are enforced. Provided
    /// because journal restoration needs to put balance back to an exact prior
    /// value on rollback.
    #[inline]
    pub fn set_balance(&mut self, value: u64) {
        self.balance = value;
    }

    /// Raw write of `nonce`. Sealed-write accessor (P0-1).
    ///
    /// **Low-level**: same caveats as `set_balance`. Use `increment_nonce()`
    /// for the common +1 path; this exists for journal-rollback restoration
    /// to an exact prior value.
    #[inline]
    pub fn set_nonce(&mut self, value: u64) {
        self.nonce = value;
    }

    /// Raw write of `delegation_epoch`. Sealed-write accessor (P0-1).
    ///
    /// **Low-level**: same caveats as `set_balance`. Use
    /// `bump_delegation_epoch()` for the common +1 path; this exists for
    /// journal-rollback restoration.
    #[inline]
    pub fn set_delegation_epoch(&mut self, value: u64) {
        self.delegation_epoch = value;
    }

    /// Credit balance by `amount`. Returns `false` on overflow (caller must
    /// check). Sealed-write semantic accessor.
    #[inline]
    #[must_use = "balance credit may overflow; the caller must handle the false return"]
    pub fn credit_balance(&mut self, amount: u64) -> bool {
        match self.balance.checked_add(amount) {
            Some(new) => {
                self.balance = new;
                true
            }
            None => false,
        }
    }

    /// Debit balance by `amount`. Returns `false` on underflow (caller must
    /// check). Sealed-write semantic accessor.
    #[inline]
    #[must_use = "balance debit may underflow; the caller must handle the false return"]
    pub fn debit_balance(&mut self, amount: u64) -> bool {
        match self.balance.checked_sub(amount) {
            Some(new) => {
                self.balance = new;
                true
            }
            None => false,
        }
    }

    /// Create a fresh cell state with zero fields and the given balance.
    pub fn new(balance: u64) -> Self {
        CellState {
            fields: [FIELD_ZERO; STATE_SLOTS],
            field_visibility: [FieldVisibility::Public; STATE_SLOTS],
            commitments: [None; STATE_SLOTS],
            nonce: 0,
            balance,
            proved_state: false,
            delegation_epoch: 0,
            // Stage 1 CapTP-prep: empty-tree sentinels.
            swiss_table_root: [0u8; 32],
            refcount_table_root: [0u8; 32],
            // Record-layer Stage 0: empty user-field map.
            fields_root: empty_fields_root(),
            fields_map: BTreeMap::new(),
        }
    }

    /// Set a field's visibility level. If transitioning to Committed or
    /// SelectivelyDisclosable, computes and stores the commitment hash.
    /// The `commitment_nonce` is mixed into the hash to prevent rainbow attacks.
    pub fn set_field_visibility(
        &mut self,
        index: usize,
        visibility: FieldVisibility,
        commitment_nonce: u64,
    ) -> bool {
        if index >= STATE_SLOTS {
            return false;
        }
        self.field_visibility[index] = visibility;
        match visibility {
            FieldVisibility::Public => {
                self.commitments[index] = None;
            }
            FieldVisibility::Committed | FieldVisibility::SelectivelyDisclosable => {
                self.commitments[index] = Some(Self::compute_commitment(
                    &self.fields[index],
                    commitment_nonce,
                ));
            }
        }
        true
    }

    /// Compute a BLAKE3 commitment: H(value || nonce_bytes).
    fn compute_commitment(value: &FieldElement, nonce: u64) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(value);
        hasher.update(&nonce.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Get the public view of a field: returns the value if Public, or the
    /// commitment hash if Committed/SelectivelyDisclosable.
    ///
    /// Audit P1-2: previously, if the visibility was `Committed` or
    /// `SelectivelyDisclosable` but the stored `commitments[index]` was `None`
    /// (because `set_field` invalidated the stale hash), this function fell
    /// through to `PublicFieldView::Revealed(self.fields[index])` and silently
    /// leaked the supposedly-private value. We now return a sentinel
    /// `PublicFieldView::Committed([0u8; 32])` instead — callers MUST treat
    /// the zero-hash as "commitment is stale; ask the holder to re-commit
    /// with `set_field_visibility`," not as a free plaintext disclosure.
    pub fn get_field_public(&self, index: usize) -> Option<PublicFieldView> {
        if index >= STATE_SLOTS {
            return None;
        }
        match self.field_visibility[index] {
            FieldVisibility::Public => Some(PublicFieldView::Revealed(self.fields[index])),
            FieldVisibility::Committed | FieldVisibility::SelectivelyDisclosable => {
                match self.commitments[index] {
                    Some(hash) => Some(PublicFieldView::Committed(hash)),
                    // Stale commitment after `set_field`: refuse to reveal the
                    // plaintext. Return the all-zero sentinel so the public
                    // view is non-informative until the holder re-commits.
                    None => Some(PublicFieldView::Committed([0u8; 32])),
                }
            }
        }
    }

    /// Get a state field by index.
    pub fn get_field(&self, index: usize) -> Option<&FieldElement> {
        self.fields.get(index)
    }

    /// Set a state field by index.
    ///
    /// Invalidates any stale commitment for this field. Callers that need the
    /// commitment to remain valid must call `set_field_visibility` with a fresh
    /// nonce after updating the value.
    pub fn set_field(&mut self, index: usize, value: FieldElement) -> bool {
        if index < STATE_SLOTS {
            self.fields[index] = value;
            // Invalidate stale commitment — old hash no longer matches new value.
            if self.commitments[index].is_some() {
                self.commitments[index] = None;
            }
            true
        } else {
            false
        }
    }

    // ───────────────────────────────────────────────────────────────────────
    // `_RECORD-LAYER-UPGRADE.md` §B.3 — the committed user-field MAP (Stage 0).
    //
    // The hybrid read/write: keys `< STATE_SLOTS` (8) hit the existing fixed
    // `fields[]` array (byte-identical to before); keys `>= STATE_SLOTS` hit the
    // committed map. These are NEW methods — every existing `get_field`/
    // `set_field` call (which takes a `usize` slot index) is untouched.
    // ───────────────────────────────────────────────────────────────────────

    /// Read a field by its **unbounded key**. Keys `< STATE_SLOTS` read the
    /// fixed cell `fields[key]`; keys `>= STATE_SLOTS` read the committed map
    /// (returning `None` if the key is absent — the negative membership case).
    ///
    /// The Rust shadow of the Lean `FieldsMap.tailLookup` / `Value.scalar`
    /// uniform name-keyed read.
    pub fn get_field_ext(&self, key: u64) -> Option<FieldElement> {
        if (key as usize) < STATE_SLOTS {
            Some(self.fields[key as usize])
        } else {
            self.fields_map.get(&key).copied()
        }
    }

    /// Write a field by its **unbounded key**. Keys `< STATE_SLOTS` write the
    /// fixed cell (delegating to [`set_field`](Self::set_field), so stale-
    /// commitment invalidation is preserved); keys `>= STATE_SLOTS` insert into
    /// the committed map and recompute [`fields_root`](Self::fields_root).
    /// Returns `true` on success.
    pub fn set_field_ext(&mut self, key: u64, value: FieldElement) -> bool {
        if (key as usize) < STATE_SLOTS {
            self.set_field(key as usize, value)
        } else {
            self.fields_map.insert(key, value);
            self.fields_root = compute_fields_root(&self.fields_map);
            true
        }
    }

    /// Recompute and store `fields_root` from the current `fields_map`. Idempotent;
    /// callers that mutate `fields_map` out-of-band must call this to re-seal the
    /// root (the normal [`set_field_ext`](Self::set_field_ext) path does it
    /// automatically).
    pub fn reseal_fields_root(&mut self) {
        self.fields_root = compute_fields_root(&self.fields_map);
    }

    /// **Membership witness** for a committed user-map key: returns the value
    /// `Some(v)` iff `key` is present in the map AND the recomputed root over
    /// the current map equals the stored `fields_root` (i.e. the value `v` is
    /// genuinely committed by `fields_root`). This is the end-to-end read-back
    /// the subscription app uses: a read proves the value is committed.
    ///
    /// The Rust shadow of the Lean `FieldsMap.fieldsRoot_membership` read law.
    pub fn fields_root_membership(&self, key: u64) -> Option<FieldElement> {
        let v = self.fields_map.get(&key).copied()?;
        if compute_fields_root(&self.fields_map) == self.fields_root {
            Some(v)
        } else {
            None
        }
    }

    /// Increment the nonce by 1, returning `true` on success and `false` on
    /// overflow.
    ///
    /// Audit P2-2: previously used `wrapping_add`, which would silently wrap
    /// after 2^64 increments and re-enable replay of historical actions.
    /// Callers must check the return value and refuse to proceed on `false`.
    #[must_use = "nonce overflow must be handled; ignoring the return value re-introduces P2-2"]
    pub fn increment_nonce(&mut self) -> bool {
        match self.nonce.checked_add(1) {
            Some(n) => {
                self.nonce = n;
                true
            }
            None => false,
        }
    }

    /// Apply a balance change (positive or negative). Returns false on underflow.
    pub fn apply_balance_change(&mut self, delta: i64) -> bool {
        if delta >= 0 {
            match self.balance.checked_add(delta as u64) {
                Some(new_bal) => {
                    self.balance = new_bal;
                    true
                }
                None => false,
            }
        } else {
            let abs = delta.unsigned_abs();
            if self.balance >= abs {
                self.balance -= abs;
                true
            } else {
                false
            }
        }
    }

    /// Bump the delegation epoch (signals children to refresh).
    ///
    /// Audit P2-2: previously used `wrapping_add`. Returns `false` on overflow;
    /// in practice 2^64 epoch bumps is unreachable but a wrap would let stale
    /// delegations regain freshness.
    #[must_use = "delegation epoch overflow must be handled"]
    pub fn bump_delegation_epoch(&mut self) -> bool {
        match self.delegation_epoch.checked_add(1) {
            Some(e) => {
                self.delegation_epoch = e;
                true
            }
            None => false,
        }
    }
}

impl Default for CellState {
    fn default() -> Self {
        Self::new(0)
    }
}

#[cfg(test)]
mod fields_map_tests {
    //! `_RECORD-LAYER-UPGRADE.md` Stage 0: the committed user-field MAP. The
    //! Rust shadow of `Dregg2/Exec/FieldsMap.lean`'s pos/neg vacuity guard.

    use super::*;

    fn fe(byte: u8) -> FieldElement {
        let mut f = [0u8; 32];
        f[31] = byte;
        f
    }

    /// A fresh cell has the FIXED empty-map root (legacy backward-compat
    /// constant) and an empty map.
    #[test]
    fn fresh_cell_has_empty_fields_root() {
        let s = CellState::new(0);
        assert!(s.fields_map.is_empty());
        assert_eq!(
            s.fields_root,
            empty_fields_root(),
            "a no-overflow cell carries the fixed empty-map constant"
        );
    }

    /// POSITIVE membership: a written key `>= 8` reads back exactly its value,
    /// and the membership witness confirms it is committed by `fields_root`.
    #[test]
    fn map_field_write_then_membership_readback() {
        let mut s = CellState::new(0);
        assert!(s.set_field_ext(8, fe(42)));
        assert!(s.set_field_ext(9, fe(7)));
        assert_eq!(s.get_field_ext(8), Some(fe(42)));
        assert_eq!(s.get_field_ext(9), Some(fe(7)));
        // The committed read-back: value is genuinely committed by fields_root.
        assert_eq!(s.fields_root_membership(8), Some(fe(42)));
        assert_eq!(s.fields_root_membership(9), Some(fe(7)));
    }

    /// NEGATIVE membership: an absent key reads `None` (the tail does not commit
    /// it) — the anti-vacuity negative witness.
    #[test]
    fn absent_map_field_reads_none() {
        let mut s = CellState::new(0);
        s.set_field_ext(8, fe(42));
        assert_eq!(s.get_field_ext(10), None);
        assert_eq!(s.fields_root_membership(10), None);
    }

    /// Keys `< 8` fall through to the fixed array (existing access unchanged):
    /// `set_field_ext`/`get_field_ext` on a low key mirror `set_field`/`get_field`.
    #[test]
    fn low_keys_hit_the_fixed_array() {
        let mut s = CellState::new(0);
        assert!(s.set_field_ext(3, fe(99)));
        assert_eq!(s.fields[3], fe(99));
        assert_eq!(s.get_field_ext(3), Some(fe(99)));
        // The map and its root are untouched by a low-key write.
        assert!(s.fields_map.is_empty());
        assert_eq!(s.fields_root, empty_fields_root());
    }

    /// ANTI-VACUITY: a map with data has a root DIFFERENT from the empty
    /// constant, and a tampered value FLIPS the root (the digest genuinely
    /// commits the map — a `:= 0` stub is forbidden).
    #[test]
    fn fields_root_is_not_vacuous() {
        let mut s = CellState::new(0);
        s.set_field_ext(8, fe(42));
        assert_ne!(
            s.fields_root,
            empty_fields_root(),
            "a populated map must not collapse to the empty constant"
        );
        let root_before = s.fields_root;
        // Tamper the value at the same key.
        s.set_field_ext(8, fe(43));
        assert_ne!(root_before, s.fields_root, "tampering a value must flip the root");
        // Distinct maps cannot share a root: a drop also flips it.
        s.set_field_ext(9, fe(1));
        let two_entries = s.fields_root;
        s.fields_map.remove(&9);
        s.reseal_fields_root();
        assert_ne!(two_entries, s.fields_root, "dropping an entry must flip the root");
    }

    /// `fields_root` is deterministic and order-canonical (BTreeMap key order):
    /// inserting the same entries in a different order yields the same root.
    #[test]
    fn fields_root_is_order_canonical() {
        let mut a = CellState::new(0);
        a.set_field_ext(8, fe(1));
        a.set_field_ext(9, fe(2));
        let mut b = CellState::new(0);
        b.set_field_ext(9, fe(2));
        b.set_field_ext(8, fe(1));
        assert_eq!(a.fields_root, b.fields_root);
    }

    /// An existing serialized cell (no `fields_root`/`fields_map`) deserializes
    /// unchanged: the `#[serde(default)]` fields populate to the empty map.
    #[test]
    fn legacy_serialized_cell_deserializes() {
        // A JSON blob with the pre-Stage-0 field set only (no fields_root /
        // fields_map). Deserialization must succeed and default the new fields.
        // Built by serializing a fresh cell, then stripping the new keys — so
        // the blob is exactly a pre-upgrade serialized cell.
        let fresh = CellState::new(100);
        let mut blob = serde_json::to_value(&fresh).expect("serialize");
        let obj = blob.as_object_mut().unwrap();
        obj.remove("fields_root");
        obj.remove("fields_map");
        obj.insert("nonce".into(), serde_json::json!(5));
        let s: CellState = serde_json::from_value(blob).expect("legacy cell deserializes");
        assert_eq!(s.nonce(), 5);
        assert_eq!(s.balance(), 100);
        assert!(s.fields_map.is_empty());
        assert_eq!(s.fields_root, empty_fields_root());
    }
}
