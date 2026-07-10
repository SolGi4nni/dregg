use serde::{Deserialize, Serialize};

use crate::derivation::{cap_provenance, mint_provenance};
use crate::facet::{EffectMask, FacetConstraint};
use crate::id::CellId;
use crate::permissions::AuthRequired;
use crate::predicate::WitnessedPredicate;

/// The `created_by_turn` fed to [`cap_provenance`] when a capability is minted
/// OUTSIDE a turn context (the low-level, context-free `grant*` primitives).
/// Real derivations pass the creating turn hash through the `*_provenanced`
/// constructors so a revoke-then-regrant at the same slot yields a distinct
/// provenance; a context-free grant is a root/mint and uses this sentinel.
const NO_TURN_CONTEXT: [u8; 32] = [0u8; 32];

/// A typed capability caveat — the unified "constraint on cap exercise"
/// shape per PREDICATE-INVENTORY §3.5 + §7.6.
///
/// Existing capability authority predicates (the lattice attenuation
/// shape: `allowed_effects: Option<EffectMask>` on
/// [`CapabilityRef`] / [`AttenuatedCap`], and the order-theoretic
/// `is_narrower_or_equal`/`is_facet_attenuation` checks) stay in their
/// current shape — they are *order-theoretic*, not witness-attached, and
/// PREDICATE-INVENTORY §3.6 case 3 explicitly excludes them from the
/// unification.
///
/// `CapabilityCaveat` is the *additive* surface for cap holders to
/// carry witness-attached predicates on their exercise (e.g. "this cap
/// only fires when you produce a DFA-match proof against the
/// governance-bound route table"), and to declare per-cap
/// `FacetConstraint`s as first-class typed caveats rather than via the
/// bitmask + side-channel constraint shape on `ExtendedFacet`.
///
/// v1 ships the type and a serde round-trip; production wiring (cap
/// exercise reaching for `caveats: Vec<CapabilityCaveat>` on every
/// `CapabilityRef`) is the PREDICATE-INVENTORY §7.6 Phase-6 payoff and
/// stays additive.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CapabilityCaveat {
    /// A typed facet constraint (rate limit, max-transfer, allowed
    /// targets, budget). The existing `FacetConstraint` enum is the
    /// canonical shape; this variant carries one of them.
    FacetConstraint(FacetConstraint),
    /// A witness-attached predicate gating cap exercise. The cap
    /// holder must produce a proof that satisfies the registered
    /// verifier kind. Per PREDICATE-INVENTORY §3.5 + §8.3.
    Witnessed(WitnessedPredicate),
}

/// A reference to a capability — an entry in a cell's c-list.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapabilityRef {
    /// Which cell this capability points to.
    pub target: CellId,
    /// Local slot number (position in the c-list).
    pub slot: u32,
    /// What authorization is required to exercise this capability.
    pub permissions: AuthRequired,
    /// Optional capability token hash for verification/revocation.
    pub breadstuff: Option<[u8; 32]>,
    /// Optional expiry height. If set, the capability is considered invalid
    /// after this block height (used for introduction-granted capabilities).
    #[serde(default)]
    pub expires_at: Option<u64>,
    /// Optional facet mask restricting which effect types this capability permits.
    ///
    /// When `None`, all effect types are allowed (unrestricted capability).
    /// When `Some(mask)`, only effect types whose corresponding bit is set in the
    /// mask can be performed via `ExerciseViaCapability` using this capability.
    ///
    /// This implements E-language **facets**: a faceted capability exposes only a
    /// subset of the target cell's interface to the holder. For example, a
    /// transfer-only facet allows sending value but not modifying state fields
    /// or changing permissions.
    ///
    /// Facets compose with attenuation: a delegated faceted capability can only
    /// further restrict (bitwise subset), never amplify.
    ///
    /// SERDE: `#[serde(default)]` only (NOT `skip_serializing_if`). A skipped field
    /// cannot round-trip through the non-self-describing `postcard` codec the
    /// durable image (commit log / checkpoint / `canonical_ledger_root`) uses — the
    /// deserializer reads the next field's bytes for the absent one and desyncs
    /// ("end of buffer" / "Option discriminant"). Emitting the `None` discriminant
    /// makes a cap-carrying cell durable (SESSION RESUME needs this — a logged-in
    /// session's cap-tree must survive a reopen). `#[serde(default)]` still decodes
    /// a legacy blob that lacks the field as `None`.
    #[serde(default)]
    pub allowed_effects: Option<EffectMask>,
    /// R7 (epoch-at-retrieval): the grantor's `delegation_epoch` captured when
    /// this capability was STORED (delegation-snapshot time). `None` = a
    /// direct grant — exempt from the freshness re-check. `Some(e)` = the
    /// executor's `ExerciseViaCapability` re-checks
    /// `e >= grantor.delegation_epoch()` at exercise time, so a stored cap
    /// cannot survive its grantor's revocation (any grantor epoch-bump
    /// conservatively stales earlier-stored caps; the holder's duty is to
    /// refresh). The grantor of authority over `target` IS `target` (the
    /// self-grant origin; `target.delegation_epoch` is bumped by `target`'s
    /// `RevokeDelegation`s).
    ///
    /// ⚠ MIGRATION WINDOW (loud, per DREGG3 §6 R7): `#[serde(default)]`
    /// means legacy persisted caps decode as `None` and are EXEMPT from the
    /// check. Until re-granted/refreshed, pre-R7 stored caps keep the old
    /// (unchecked) semantics.
    ///
    /// NOT part of the canonical 7-field cap leaf (`cap_ref_to_leaf`) this
    /// phase — it is an executor-side gate; absorbing it into the circuit's
    /// cap-root is the Phase-C/W2 follow-up (a VK bump).
    #[serde(default)]
    pub stored_epoch: Option<u64>,
    /// The capability-instance **PROVENANCE** hash — this cap's derivation-node
    /// identity ([`crate::derivation::cap_provenance`]), computed AT CREATION by
    /// CHAINING the parent cap's provenance and the creating turn. It makes the
    /// capability SELF-IDENTIFYING with no CDT lookup during turn execution, and
    /// is the value the committed revoked-credential accumulator keys on as
    /// [`crate::derivation::cred_nul`]`(provenance)` — the `ancestor_hash` the
    /// non-revocation circuit queries.
    ///
    /// Collision-free across slot reuse: `derivation.rs:189-190` documents that a
    /// revoked slot is re-granted (`(cell, slot)` is reused), so `(cell, slot)`
    /// keying would make a regrant inherit the revoked identity and poison the
    /// slot forever. Folding `parent_provenance` + `created_by_turn` in makes the
    /// regrant a DISTINCT identity from the revoked instance.
    ///
    /// A `[0u8; 32]` value is the "legacy/unprovenanced" sentinel: `#[serde(default)]`
    /// decodes a pre-provenance persisted cap to it (a fresh-genesis flip, per the
    /// campaign's VK regen, avoids relying on legacy decode). Direct
    /// (context-free) grants derive a deterministic mint-rooted provenance.
    ///
    /// LEAF NOTE: not yet part of the canonical cap leaf — the geometry lane must
    /// add it so the committed cap-root binds each cap's provenance (see the lane
    /// report). Until then the revocation gate consumes an un-committed provenance,
    /// the same "read off committed state, not the wire" gap for the cap itself.
    #[serde(default)]
    pub provenance: [u8; 32],
}

impl CapabilityRef {
    /// This capability's **credential-revocation nullifier** — the accumulator
    /// key the revocation gate checks for non-membership. Equal to
    /// [`crate::derivation::cred_nul`]`(&self.provenance)`; a revoke of THIS cap
    /// inserts exactly this value into the committed revoked-credential set.
    pub fn cred_nul(&self) -> [u8; 32] {
        crate::derivation::cred_nul(&self.provenance)
    }

    /// The **channel-revocation nullifier** a subscribed capability presents for
    /// the batch (channel-trip) non-revocation check. A convenience wrapper over
    /// [`crate::derivation::chan_nul`] — the `channel_id` a cap subscribes to is
    /// carried out-of-band (e.g. its [`crate::revocation_channel`] subscription),
    /// not on `CapabilityRef` today.
    pub fn chan_nul(channel_id: &[u8; 32]) -> [u8; 32] {
        crate::derivation::chan_nul(channel_id)
    }
}

/// An attenuated capability without a slot assignment.
///
/// Produced by [`CapabilitySet::attenuate`]. This represents a capability with narrowed
/// permissions that has not yet been placed into any c-list. The slot is assigned when
/// inserted into a target `CapabilitySet` via [`CapabilitySet::insert_attenuated`].
///
/// This separation prevents a child from inheriting the parent's internal slot numbering,
/// which could leak information about the parent's c-list layout or collide with existing
/// entries in the child's c-list.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttenuatedCap {
    /// Which cell this capability points to.
    pub target: CellId,
    /// What authorization is required to exercise this capability.
    pub permissions: AuthRequired,
    /// Optional capability token hash for verification/revocation.
    pub breadstuff: Option<[u8; 32]>,
    /// Optional expiry height.
    #[serde(default)]
    pub expires_at: Option<u64>,
    /// Optional facet mask (same semantics as CapabilityRef::allowed_effects).
    /// SERDE: `#[serde(default)]` only — see `CapabilityRef::allowed_effects` (a
    /// skipped field cannot round-trip the durable `postcard` codec).
    #[serde(default)]
    pub allowed_effects: Option<EffectMask>,
    /// R7 stored-epoch (same semantics as `CapabilityRef::stored_epoch`).
    /// Attenuation PRESERVES freshness metadata — narrowing never refreshes.
    #[serde(default)]
    pub stored_epoch: Option<u64>,
    /// The PARENT (source) cap's [`CapabilityRef::provenance`] — carried so
    /// [`CapabilitySet::insert_attenuated`] can derive this attenuated cap's NEW,
    /// CHAINED provenance once its slot is assigned in the target c-list. An
    /// attenuated cap is a NEW derivation node (spec step 4), so it must NOT reuse
    /// the parent's provenance; chaining it here binds the child to the parent so
    /// revoking the parent's `cred_nul` also blocks the child via the ancestor
    /// chain — closing "attenuate around a revocation".
    #[serde(default)]
    pub parent_provenance: [u8; 32],
}

/// Per-cell-state sub-root cache for the capability tree
/// (`docs/INCREMENTAL-COMMITMENT.md` step 2). Holds the last-materialized
/// canonical cap-root felt (as its `u32` value) so a turn that does NOT touch
/// the cap set reuses it instead of re-folding the sorted-Poseidon2 tree.
///
/// **Invalidation completeness is the soundness crux.** This is `None` (dirty)
/// after construction, after deserialization, and after EVERY mutation of the
/// c-list — `grant*`, `revoke`, `attenuate_in_place`, `insert_attenuated`,
/// `restore`, and `iter_mut` (which hands out `&mut CapabilityRef` and so MUST
/// conservatively invalidate). A stale cache would be a silent wrong commitment,
/// so the cache is private and EVERY `&mut self` path through this module clears
/// it; the differential `cap_root_cache_matches_fresh` pins byte-identity.
///
/// An `AtomicU64` gives `Sync` interior mutability so the lazy materialize can
/// run behind the shared `&CapabilitySet` the commitment path holds, AND so a
/// `Cell` carrying it stays `Send + Sync` (the node/app-framework share cells
/// across threads — a `std::cell::Cell` would make the whole type `!Sync`). The
/// `Option<u32>` is packed as `u64`: the present-flag in bit 32, the cap-root
/// felt's `u32` value in the low 32 bits; `DIRTY` (0) means no cached value.
/// It is NOT serialized (a derived value), NOT part of `PartialEq`/`Eq` (two
/// equal c-lists with different cache states are equal), and a `Clone` copies
/// the current cached value (the c-list bytes are identical, so the root is
/// valid for the clone too).
#[derive(Debug, Default)]
pub struct CapRootCache(std::sync::atomic::AtomicU64);

impl CapRootCache {
    const PRESENT: u64 = 1u64 << 32;

    #[inline]
    fn load(&self) -> Option<u32> {
        let packed = self.0.load(std::sync::atomic::Ordering::Relaxed);
        if packed & Self::PRESENT != 0 {
            Some((packed & 0xFFFF_FFFF) as u32)
        } else {
            None
        }
    }

    #[inline]
    fn store(&self, value: Option<u32>) {
        let packed = match value {
            Some(v) => Self::PRESENT | v as u64,
            None => 0,
        };
        self.0.store(packed, std::sync::atomic::Ordering::Relaxed);
    }
}

impl Clone for CapRootCache {
    fn clone(&self) -> Self {
        CapRootCache(std::sync::atomic::AtomicU64::new(
            self.0.load(std::sync::atomic::Ordering::Relaxed),
        ))
    }
}

impl PartialEq for CapRootCache {
    fn eq(&self, _other: &Self) -> bool {
        // The cache is a derived value, not part of the c-list's identity.
        true
    }
}
impl Eq for CapRootCache {}

/// The c-list: the set of capabilities a cell holds.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapabilitySet {
    refs: Vec<CapabilityRef>,
    next_slot: u32,
    /// Cached canonical cap-root felt value (`docs/INCREMENTAL-COMMITMENT.md`
    /// step 2). `#[serde(skip)]` so it is never persisted and always
    /// reconstructs as dirty (`None`) on deserialize — the byte-identical fold
    /// fills it on first read. Excluded from `PartialEq`/`Eq` via the
    /// `CapRootCache` impls above.
    #[serde(skip)]
    cap_root_cache: CapRootCache,
    /// Slot numbers of REVOKED capabilities — the c-list's TOMBSTONE set (cap
    /// crown, the cell↔circuit revoke reconciliation).
    ///
    /// ## Why tombstones (the openable-membership-tree contract)
    ///
    /// The capability commitment ([`crate::commitment::compute_canonical_capability_root`])
    /// is an OPENABLE sorted-Poseidon2 Merkle tree, shared byte-identically with
    /// the EffectVM circuit's `cap_root`. In an openable membership tree a
    /// revoke must NOT compact (re-index) the tree — doing so shifts every key
    /// that sorts after the revoked one, invalidating every OTHER capability's
    /// membership witness. The worthwhile semantics is a TOMBSTONE: the revoked
    /// slot's POSITION stays occupied by the `BabyBear::ZERO` padding leaf, so
    /// all other witnesses stay valid. This is exactly what the in-circuit
    /// sel-24 revoke gate (`dregg_circuit::cap_root::revocation_witness` —
    /// membership-open the held leaf, fold ZERO up its sibling path) enforces.
    ///
    /// So `revoke` drops the cap from `refs` (logical c-list: the cap is gone,
    /// `lookup`/`has_access` no longer see it) AND records the slot here; the
    /// root computation injects a ZERO-digest ghost leaf at each tombstoned
    /// slot's sort key, reproducing the circuit's post-revoke root. A
    /// re-granted slot is shadowed by its live leaf (the live leaf resurrects
    /// the position).
    ///
    /// `#[serde(default)]`: legacy persisted c-lists decode with NO tombstones
    /// (they never revoked under the openable-tree scheme), so their root is
    /// unchanged. A cell that has revoked under this scheme carries its
    /// tombstones explicitly; the `CANONICAL_CAP_ROOT_CONTEXT` bump (v2→v3)
    /// cleanly invalidates any stale compacted root.
    #[serde(default)]
    tombstones: Vec<u32>,
}

impl CapabilitySet {
    /// Create an empty capability set.
    pub fn new() -> Self {
        CapabilitySet {
            refs: Vec::new(),
            next_slot: 0,
            tombstones: Vec::new(),
            cap_root_cache: CapRootCache::default(),
        }
    }

    /// Mark the cached cap-root dirty (`docs/INCREMENTAL-COMMITMENT.md` step 2).
    /// Called by EVERY path that can change the c-list bytes — the completeness
    /// guarantee. Cheap (a single `Cell::set`), so calling it unconditionally
    /// (even when a mutator turns out to be a no-op, e.g. a `revoke` of a missing
    /// slot) is harmless: a dirty cache only costs ONE extra fold on the next
    /// read, never a wrong root.
    #[inline]
    fn invalidate_cap_root_cache(&self) {
        self.cap_root_cache.store(None);
    }

    /// Read the cached canonical cap-root felt, or `None` if dirty. Used by the
    /// commitment path to skip the fold when the cap set has not changed.
    #[inline]
    pub(crate) fn cached_cap_root(&self) -> Option<dregg_circuit::field::BabyBear> {
        self.cap_root_cache
            .load()
            .map(dregg_circuit::field::BabyBear::new)
    }

    /// Store a freshly-computed canonical cap-root felt into the cache. The
    /// commitment path calls this after a dirty-fold so the next read is O(1).
    #[inline]
    pub(crate) fn store_cap_root(&self, felt: dregg_circuit::field::BabyBear) {
        self.cap_root_cache.store(Some(felt.as_u32()));
    }

    /// Grant a capability to reach `target` with the given authorization requirement.
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn grant(&mut self, target: CellId, permissions: AuthRequired) -> Option<u32> {
        self.grant_with_breadstuff(target, permissions, None)
    }

    /// Grant a capability with an optional breadstuff token hash.
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn grant_with_breadstuff(
        &mut self,
        target: CellId,
        permissions: AuthRequired,
        breadstuff: Option<[u8; 32]>,
    ) -> Option<u32> {
        // INVALIDATE the cached cap-root: this method appends to the c-list.
        self.invalidate_cap_root_cache();
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        let provenance = cap_provenance(&target, slot, &mint_provenance(), &NO_TURN_CONTEXT);
        self.refs.push(CapabilityRef {
            target,
            slot,
            permissions,
            breadstuff,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
            provenance,
        });
        Some(slot)
    }

    /// Grant a capability with an expiry block height.
    /// After `expires_at`, the capability is considered invalid.
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn grant_with_expiry(
        &mut self,
        target: CellId,
        permissions: AuthRequired,
        expires_at: u64,
    ) -> Option<u32> {
        // INVALIDATE the cached cap-root: this method appends to the c-list.
        self.invalidate_cap_root_cache();
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        let provenance = cap_provenance(&target, slot, &mint_provenance(), &NO_TURN_CONTEXT);
        self.refs.push(CapabilityRef {
            target,
            slot,
            permissions,
            breadstuff: None,
            expires_at: Some(expires_at),
            allowed_effects: None,
            stored_epoch: None,
            provenance,
        });
        Some(slot)
    }

    /// Grant a capability preserving ALL fields from a CapabilityRef (breadstuff + expires_at).
    ///
    /// Used during delta application to avoid silently dropping the `expires_at` field.
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn grant_full(
        &mut self,
        target: CellId,
        permissions: AuthRequired,
        breadstuff: Option<[u8; 32]>,
        expires_at: Option<u64>,
    ) -> Option<u32> {
        // INVALIDATE the cached cap-root: this method appends to the c-list.
        self.invalidate_cap_root_cache();
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        let provenance = cap_provenance(&target, slot, &mint_provenance(), &NO_TURN_CONTEXT);
        self.refs.push(CapabilityRef {
            target,
            slot,
            permissions,
            breadstuff,
            expires_at,
            allowed_effects: None,
            stored_epoch: None,
            provenance,
        });
        Some(slot)
    }

    /// Grant a capability preserving EVERY field of `cap` except the slot
    /// (which this c-list assigns). The faithful install primitive: the
    /// executor's `GrantCapability` / `Unseal` arms use it so the installed
    /// entry carries the genuinely-attenuated `allowed_effects` + `expires_at`
    /// (+ `breadstuff` + R7 `stored_epoch`) instead of silently widening to
    /// `None`/`None` (the B2 runtime-laxity hole).
    ///
    /// Returns the assigned slot number, or `None` if the slot counter would
    /// overflow.
    pub fn grant_ref(&mut self, cap: &CapabilityRef) -> Option<u32> {
        // INVALIDATE the cached cap-root: this method appends to the c-list.
        self.invalidate_cap_root_cache();
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        // A grant is a NEW derivation node installed at a NEW slot: derive a fresh
        // provenance CHAINING the source cap's provenance (its parent). Copying
        // `cap.provenance` would leave the identity inconsistent with the new slot
        // (provenance folds the slot in) AND would let the installed cap dodge a
        // revoke of the source; chaining binds it to the source instead.
        let provenance = cap_provenance(&cap.target, slot, &cap.provenance, &NO_TURN_CONTEXT);
        self.refs.push(CapabilityRef {
            target: cap.target,
            slot,
            permissions: cap.permissions.clone(),
            breadstuff: cap.breadstuff,
            expires_at: cap.expires_at,
            allowed_effects: cap.allowed_effects,
            stored_epoch: cap.stored_epoch,
            provenance,
        });
        Some(slot)
    }

    /// Grant a capability carrying an R7 delegation-snapshot epoch: the
    /// grantor's `delegation_epoch` at store time. Exercise via the executor
    /// re-checks `stored_epoch >= grantor.delegation_epoch()` so the stored
    /// cap dies with its grantor's next revocation.
    pub fn grant_snapshot(
        &mut self,
        target: CellId,
        permissions: AuthRequired,
        breadstuff: Option<[u8; 32]>,
        stored_epoch: u64,
    ) -> Option<u32> {
        // INVALIDATE the cached cap-root: this method appends to the c-list.
        self.invalidate_cap_root_cache();
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        let provenance = cap_provenance(&target, slot, &mint_provenance(), &NO_TURN_CONTEXT);
        self.refs.push(CapabilityRef {
            target,
            slot,
            permissions,
            breadstuff,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: Some(stored_epoch),
            provenance,
        });
        Some(slot)
    }

    /// Grant a faceted capability: restricted to only certain effect types.
    ///
    /// This implements E-language facets: the capability holder can only exercise
    /// the subset of operations described by `effect_mask`. For example, a
    /// `FACET_TRANSFER_ONLY` capability allows sending value but not modifying
    /// state fields or changing permissions.
    ///
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn grant_faceted(
        &mut self,
        target: CellId,
        permissions: AuthRequired,
        effect_mask: EffectMask,
    ) -> Option<u32> {
        // INVALIDATE the cached cap-root: this method appends to the c-list.
        self.invalidate_cap_root_cache();
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        let provenance = cap_provenance(&target, slot, &mint_provenance(), &NO_TURN_CONTEXT);
        self.refs.push(CapabilityRef {
            target,
            slot,
            permissions,
            breadstuff: None,
            expires_at: None,
            allowed_effects: Some(effect_mask),
            stored_epoch: None,
            provenance,
        });
        Some(slot)
    }

    /// Grant a capability with a FULLY-CHAINED provenance: the executor's
    /// `GrantCapability` / `Introduce` / `SpawnWithDelegation` / `Unseal` arms
    /// (which hold the parent cap's provenance and the creating turn hash) call
    /// this so the installed cap's identity CHAINS the parent and is distinct
    /// across a revoke-then-regrant of the same slot. For an originally-minted
    /// (root) cap, pass [`mint_provenance`] as `parent_provenance`.
    ///
    /// This is the provenanced twin of [`Self::grant_full`]; the low-level
    /// `grant*` primitives derive a context-free mint-rooted provenance instead
    /// (turn = 0), which suffices for direct grants but does not survive slot
    /// reuse.
    ///
    /// Returns the assigned slot number, or `None` if the slot counter would
    /// overflow.
    #[allow(clippy::too_many_arguments)]
    pub fn grant_provenanced(
        &mut self,
        target: CellId,
        permissions: AuthRequired,
        breadstuff: Option<[u8; 32]>,
        expires_at: Option<u64>,
        allowed_effects: Option<EffectMask>,
        stored_epoch: Option<u64>,
        parent_provenance: [u8; 32],
        created_by_turn: [u8; 32],
    ) -> Option<u32> {
        // INVALIDATE the cached cap-root: this method appends to the c-list.
        self.invalidate_cap_root_cache();
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        let provenance = cap_provenance(&target, slot, &parent_provenance, &created_by_turn);
        self.refs.push(CapabilityRef {
            target,
            slot,
            permissions,
            breadstuff,
            expires_at,
            allowed_effects,
            stored_epoch,
            provenance,
        });
        Some(slot)
    }

    /// Revoke a capability by slot number. Returns true if found and removed.
    ///
    /// TOMBSTONE deletion (cap crown, the cell↔circuit revoke reconciliation):
    /// the cap is dropped from the LOGICAL c-list (`refs`) — `lookup` /
    /// `has_access` no longer see it, exactly as before — AND the slot is
    /// recorded in [`Self::tombstones`] so the openable sorted-Poseidon2
    /// capability root keeps a ZERO/padding leaf at the revoked slot's POSITION
    /// instead of compacting (re-indexing) the tree. This matches the in-circuit
    /// sel-24 revoke gate's zero-fold deletion byte-for-byte, so
    /// `cell_cap_root == circuit_cap_root` after a revoke (the seam this closes).
    /// See [`Self::tombstones`] for the full rationale.
    pub fn revoke(&mut self, slot: u32) -> bool {
        // INVALIDATE the cached cap-root: a revoke drops a leaf + tombstones it.
        self.invalidate_cap_root_cache();
        let before = self.refs.len();
        self.refs.retain(|r| r.slot != slot);
        let removed = self.refs.len() < before;
        if removed {
            // Record the tombstone so the cap-root folds ZERO at this slot's
            // sorted position (not a compacted rebuild). Kept SORTED + deduped:
            // tombstone order is semantically irrelevant to the (sorted-tree)
            // cap-root, and a canonical order makes the umem round-trip law
            // (`reconstruct` re-derives them ascending) hold byte-identically.
            if let Err(pos) = self.tombstones.binary_search(&slot) {
                self.tombstones.insert(pos, slot);
            }
        }
        removed
    }

    /// Look up a capability by slot number.
    pub fn lookup(&self, slot: u32) -> Option<&CapabilityRef> {
        self.refs.iter().find(|r| r.slot == slot)
    }

    /// Check if this set contains any non-revoked capability referencing the given target.
    ///
    /// A capability with `permissions: Impossible` is treated as revoked/frozen and
    /// does NOT count as a valid access path.
    ///
    /// NOTE: This method does NOT check expiration. Use `has_access_at()` when you
    /// have a current block height available (e.g., during turn execution).
    pub fn has_access(&self, target: &CellId) -> bool {
        self.refs
            .iter()
            .any(|r| &r.target == target && r.permissions != AuthRequired::Impossible)
    }

    /// Check if this set contains any non-revoked, non-expired capability referencing
    /// the given target at the given block height.
    ///
    /// A capability with `permissions: Impossible` is treated as revoked/frozen.
    /// A capability whose `expires_at` is less than `current_height` is treated as expired.
    pub fn has_access_at(&self, target: &CellId, current_height: u64) -> bool {
        self.refs.iter().any(|r| {
            &r.target == target
                && r.permissions != AuthRequired::Impossible
                && r.expires_at.is_none_or(|exp| current_height <= exp)
        })
    }

    /// Like [`has_access_at`], but additionally requires that some held,
    /// non-revoked, non-expired capability to `target` admits the given
    /// effect-kind bit through its `allowed_effects` FACET mask (E-language
    /// faceting).
    ///
    /// A cap with `allowed_effects: None` is the full-facet node cap (every
    /// effect permitted); `Some(mask)` admits only effects whose bit is set
    /// (and `Some(0)` admits nothing — the P2-1 deny-all). This is the
    /// FACET leg the verified kernel's `authorizedB` enforces on the DIRECT
    /// cross-cell path (an `.endpoint` cap must carry the required facet, not
    /// merely exist) — `CAP-FACET-1`.
    pub fn permits_effect_at(
        &self,
        target: &CellId,
        current_height: u64,
        effect_bit: EffectMask,
    ) -> bool {
        self.refs.iter().any(|r| {
            &r.target == target
                && r.permissions != AuthRequired::Impossible
                && r.expires_at.is_none_or(|exp| current_height <= exp)
                && crate::facet::is_effect_permitted(r.allowed_effects, effect_bit)
        })
    }

    /// Diagnostic: the union of `allowed_effects` facets across the held caps
    /// referencing `target` (a `None`-facet cap contributes [`EFFECT_ALL`]).
    /// Used only to populate the `allowed_mask` field of a `FacetViolation`.
    pub fn effect_mask_union_for(&self, target: &CellId) -> EffectMask {
        self.refs
            .iter()
            .filter(|r| &r.target == target && r.permissions != AuthRequired::Impossible)
            .fold(0u32, |acc, r| {
                acc | r.allowed_effects.unwrap_or(crate::facet::EFFECT_ALL)
            })
    }

    /// Attenuate a capability: produce a slot-free [`AttenuatedCap`] with narrower permissions.
    ///
    /// The returned `AttenuatedCap` does NOT carry a slot number. When delegating to a
    /// child, use [`CapabilitySet::insert_attenuated`] to assign the next available slot
    /// in the child's c-list. This prevents a child from inheriting the parent's internal
    /// slot numbering, which could leak information or collide with existing entries.
    ///
    /// Returns `None` if the slot doesn't exist or if `narrower` is not actually
    /// narrower than the existing permissions.
    pub fn attenuate(&self, slot: u32, narrower: AuthRequired) -> Option<AttenuatedCap> {
        let existing = self.lookup(slot)?;
        // The new permission must be at least as restrictive as the old one.
        if !narrower.is_narrower_or_equal(&existing.permissions) {
            return None;
        }
        Some(AttenuatedCap {
            target: existing.target,
            permissions: narrower,
            breadstuff: existing.breadstuff,
            expires_at: existing.expires_at,
            allowed_effects: existing.allowed_effects,
            stored_epoch: existing.stored_epoch,
            // The attenuated cap is a NEW derivation node: carry the PARENT's
            // provenance so `insert_attenuated` chains a fresh provenance from it.
            parent_provenance: existing.provenance,
        })
    }

    /// Attenuate a capability with a restricted effect mask (faceting).
    ///
    /// Like `attenuate`, but additionally narrows the allowed effects. The new
    /// `effect_mask` must be a subset of the existing capability's mask (bitwise AND
    /// must equal the new mask). This enforces that facets can only restrict, never
    /// expand, the set of permitted operations.
    ///
    /// Returns `None` if:
    /// - The slot doesn't exist
    /// - `narrower` permissions are not actually narrower
    /// - `effect_mask` attempts to enable bits not present in the original
    pub fn attenuate_faceted(
        &self,
        slot: u32,
        narrower: AuthRequired,
        effect_mask: EffectMask,
    ) -> Option<AttenuatedCap> {
        let existing = self.lookup(slot)?;
        if !narrower.is_narrower_or_equal(&existing.permissions) {
            return None;
        }
        // Enforce monotonic narrowing of the effect mask.
        let parent_mask = existing.allowed_effects.unwrap_or(crate::facet::EFFECT_ALL);
        if !crate::facet::is_facet_attenuation(parent_mask, effect_mask) {
            return None;
        }
        Some(AttenuatedCap {
            target: existing.target,
            permissions: narrower,
            breadstuff: existing.breadstuff,
            expires_at: existing.expires_at,
            allowed_effects: Some(effect_mask),
            stored_epoch: existing.stored_epoch,
            // NEW derivation node: chain the parent's provenance at insert time.
            parent_provenance: existing.provenance,
        })
    }

    /// Monotonically narrow an existing capability in-place — *without*
    /// changing its slot identity.
    ///
    /// Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §6.3` / the Silver-Vision
    /// AttenuateCapability primitive: today, narrowing a capability
    /// requires `revoke + reissue`, which (a) races against in-flight
    /// exercises, (b) makes the cap *temporarily absent* during the
    /// swap, and (c) loses the c-list slot identity (consumers must
    /// update their references). The structural primitive *narrows
    /// the caveat set / permissions in-place*: slot and `breadstuff`
    /// are preserved, the cap's identity is unchanged, only the
    /// authority shrinks.
    ///
    /// # Soundness
    ///
    /// Strict subset-refinement only — never expansion:
    /// - `narrower` must satisfy `is_narrower_or_equal(existing.permissions)`
    /// - `narrower_effects`, when provided, must be a bitwise subset of
    ///   the existing `allowed_effects` (or of `EFFECT_ALL` if previously
    ///   unbounded)
    /// - `narrower_expiry`, when provided, must be `≤` the existing
    ///   `expires_at` (passing `None` means "leave expiry unchanged" —
    ///   it can never *extend* a finite expiry)
    ///
    /// # Returns
    ///
    /// On success, returns the 32-byte commitment to the *new* (narrower)
    /// CapabilityRef so callers can update c-list audit indices. Returns
    /// `None` if the slot doesn't exist or any narrowing constraint is
    /// violated.
    pub fn attenuate_in_place(
        &mut self,
        slot: u32,
        narrower: AuthRequired,
        narrower_effects: Option<EffectMask>,
        narrower_expiry: Option<u64>,
    ) -> Option<[u8; 32]> {
        // First pass: find slot + validate strict narrowing without mutating.
        let existing = self.lookup(slot)?;
        if !narrower.is_narrower_or_equal(&existing.permissions) {
            return None;
        }
        // Effect-mask narrowing: subset-only.
        let new_effects = match narrower_effects {
            Some(new_mask) => {
                let parent_mask = existing.allowed_effects.unwrap_or(crate::facet::EFFECT_ALL);
                if !crate::facet::is_facet_attenuation(parent_mask, new_mask) {
                    return None;
                }
                Some(new_mask)
            }
            None => existing.allowed_effects,
        };
        // Expiry narrowing: can only shrink.
        let new_expiry = match (existing.expires_at, narrower_expiry) {
            (Some(e), Some(n)) if n > e => return None, // cannot extend a finite expiry
            (None, Some(n)) => Some(n),                 // unbounded → bounded is narrowing
            (existing_exp, None) => existing_exp,       // None means "leave as-is"
            (_, Some(n)) => Some(n),                    // narrower finite expiry
        };

        // Second pass: mutate in place and compute commitment.
        // INVALIDATE the cached cap-root: this narrows a leaf's fields.
        self.invalidate_cap_root_cache();
        let cap = self.refs.iter_mut().find(|r| r.slot == slot)?;
        cap.permissions = narrower;
        cap.allowed_effects = new_effects;
        cap.expires_at = new_expiry;
        // `provenance` is DELIBERATELY unchanged: in-place attenuation preserves
        // slot IDENTITY (it is the revoke+reissue-free narrowing primitive), so the
        // narrowed cap keeps the SAME derivation-node identity. This is the correct
        // revocation semantics — narrowing your own cap in place must NOT mint a
        // fresh provenance that escapes a revoke of the original. (Delegation
        // attenuation via `attenuate` + `insert_attenuated` DOES mint a new,
        // chained provenance — a genuinely new node in another c-list.)

        // Commit to the narrowed cap so callers can update c-list audit
        // indices. This is the 32-byte encoding of the narrowed cap's openable
        // leaf-digest felt — the SAME 7-field leaf the canonical
        // sorted-Poseidon2 capability root hashes (cap Phase A), so the
        // single-cap commitment is consistent with the c-list root.
        Some(crate::commitment::capability_ref_leaf_commitment(cap))
    }

    /// Insert an attenuated capability into this set, assigning the next available slot.
    ///
    /// This is the proper way to delegate an attenuated capability to a child: the child's
    /// c-list assigns its own slot number rather than inheriting the parent's.
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn insert_attenuated(&mut self, cap: AttenuatedCap) -> Option<u32> {
        self.insert_attenuated_provenanced(cap, NO_TURN_CONTEXT)
    }

    /// Like [`Self::insert_attenuated`] but binds the creating turn hash into the
    /// derived provenance. The executor's delegation/attenuation arms (which hold
    /// `created_by_turn`) call this so a re-delegation after a revoke is a DISTINCT
    /// provenance from the revoked instance — the slot-reuse collision-freedom the
    /// context-free [`Self::insert_attenuated`] (turn = 0) cannot provide.
    pub fn insert_attenuated_provenanced(
        &mut self,
        cap: AttenuatedCap,
        created_by_turn: [u8; 32],
    ) -> Option<u32> {
        // INVALIDATE the cached cap-root: this method appends to the c-list.
        self.invalidate_cap_root_cache();
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        // NEW derivation node: chain the parent's provenance (carried on the
        // `AttenuatedCap`) with this slot + turn — never reuse the parent's, so an
        // attenuated cap cannot dodge a revoke of the parent's `cred_nul`.
        let provenance =
            cap_provenance(&cap.target, slot, &cap.parent_provenance, &created_by_turn);
        self.refs.push(CapabilityRef {
            target: cap.target,
            slot,
            permissions: cap.permissions,
            breadstuff: cap.breadstuff,
            expires_at: cap.expires_at,
            allowed_effects: cap.allowed_effects,
            stored_epoch: cap.stored_epoch,
            provenance,
        });
        Some(slot)
    }

    /// Restore a previously revoked capability by re-inserting it directly.
    /// Used by journal rollback to undo a revocation.
    ///
    /// Clears the slot's TOMBSTONE if present (the live leaf resurrects the
    /// position), so an undone revoke returns the cap-root EXACTLY to its
    /// pre-revoke value — the rollback is a true inverse of [`Self::revoke`].
    pub fn restore(&mut self, cap: CapabilityRef) {
        // INVALIDATE the cached cap-root: clears a tombstone and may re-insert a leaf.
        self.invalidate_cap_root_cache();
        self.tombstones.retain(|&s| s != cap.slot);
        if !self.refs.iter().any(|r| r.slot == cap.slot) {
            self.refs.push(cap);
        }
    }

    /// Reconstruct a c-list DIRECTLY from its projected planes — the LIVE caps
    /// (each carrying its ORIGINAL slot) and the REVOKED-slot tombstones. The
    /// umem reify primitive (`turn::umem::reify_cell`).
    ///
    /// Unlike [`Self::grant_ref`] (which re-assigns slots contiguously from
    /// `next_slot`), this PRESERVES each cap's original slot — so a revocation
    /// gap survives — and re-derives `next_slot = max(live slot, tombstoned
    /// slot) + 1` from BOTH planes. That is exactly the monotone high-water mark
    /// the original set carried after its revokes, so a revoked cell round-trips
    /// byte-identically through `project_cell` → `reify_cell` (the former
    /// reify_seam residuals #3/#4, closed).
    ///
    /// `live` need not be sorted; `refs` are stored in slot order and the
    /// tombstones canonically ascending (deduped) — matching the projection's
    /// `CapSlot`/`CapTombstone` plane emission, so the reconstructed set is
    /// `==` to the original (whose tombstones [`Self::revoke`] keeps sorted).
    pub fn reconstruct(live: Vec<CapabilityRef>, tombstones: Vec<u32>) -> Self {
        let mut refs = live;
        refs.sort_by_key(|c| c.slot);
        let mut tombstones = tombstones;
        tombstones.sort_unstable();
        tombstones.dedup();
        let max_live = refs.iter().map(|c| c.slot).max();
        let max_tomb = tombstones.iter().copied().max();
        let next_slot = max_live
            .into_iter()
            .chain(max_tomb)
            .max()
            .map_or(0, |m| m.saturating_add(1));
        CapabilitySet {
            refs,
            next_slot,
            tombstones,
            cap_root_cache: CapRootCache::default(),
        }
    }

    /// Number of active capabilities.
    pub fn len(&self) -> usize {
        self.refs.len()
    }

    /// Whether the capability set is empty.
    pub fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }

    /// Iterate over all capability refs.
    pub fn iter(&self) -> impl Iterator<Item = &CapabilityRef> {
        self.refs.iter()
    }

    /// The slot numbers of REVOKED capabilities (the tombstone set). The
    /// canonical capability root injects a ZERO/padding leaf at each of these
    /// slots' sorted positions (see [`Self::revoke`] /
    /// [`crate::commitment::compute_canonical_capability_root_felt`]). A slot
    /// that is currently LIVE in `refs` (re-granted after revoke) is shadowed by
    /// its live leaf — the root logic drops the tombstone for any live slot, so
    /// this accessor may report a slot that is also live; callers folding it
    /// into the root must let the live leaf win (the tree builder does).
    pub fn tombstoned_slots(&self) -> impl Iterator<Item = u32> + '_ {
        self.tombstones.iter().copied()
    }

    /// Mutably iterate over capability refs. Used by the executor's
    /// rollback path to restore in-place narrowings; not for general use
    /// (apps should go through `attenuate_in_place` / `grant`).
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut CapabilityRef> {
        // CONSERVATIVELY INVALIDATE the cached cap-root: this hands out
        // `&mut CapabilityRef`, so the caller (the executor's rollback path)
        // may mutate any cap field. We cannot observe the write, so we must
        // assume the c-list changed. This closes the only mutation path that
        // bypasses a dedicated mutator (the staleness leak the design audit
        // names) — a fresh `&mut` borrow always re-derives the root next read.
        self.invalidate_cap_root_cache();
        self.refs.iter_mut()
    }

    /// Get all capabilities targeting a specific cell.
    pub fn capabilities_for(&self, target: &CellId) -> Vec<&CapabilityRef> {
        self.refs.iter().filter(|r| &r.target == target).collect()
    }

    /// Look up the first capability referencing the given target.
    /// Returns None if no capability to that target is held.
    pub fn lookup_by_target(&self, target: &CellId) -> Option<&CapabilityRef> {
        self.refs.iter().find(|r| &r.target == target)
    }
}

impl Default for CapabilitySet {
    fn default() -> Self {
        Self::new()
    }
}

/// Returns true if `granted` permissions are equal to or stricter than `held` permissions.
///
/// This enforces the attenuation-only rule: you can only grant permissions that are
/// as restrictive or more restrictive than what you hold. Never amplification.
pub fn is_attenuation(held: &AuthRequired, granted: &AuthRequired) -> bool {
    granted.is_narrower_or_equal(held)
}

#[cfg(test)]
mod attenuate_in_place_tests {
    //! Adversarial tests for `CapabilitySet::attenuate_in_place`.
    //!
    //! Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §6.3` — narrowing must be
    //! strict subset-refinement only. These tests prove that violating
    //! the invariant gets rejected (no widening, no expiry-extension,
    //! no effect-mask widening).
    use super::*;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    #[test]
    fn happy_path_narrows_permissions_and_returns_commitment() {
        let mut caps = CapabilitySet::new();
        let slot = caps.grant(cid(1), AuthRequired::Either).unwrap();
        let h = caps
            .attenuate_in_place(slot, AuthRequired::Signature, None, None)
            .expect("narrowing Either -> Signature must succeed");
        assert_eq!(
            caps.lookup(slot).unwrap().permissions,
            AuthRequired::Signature
        );
        // Slot identity unchanged.
        assert_eq!(caps.lookup(slot).unwrap().slot, slot);
        assert_ne!(h, [0u8; 32], "commitment must be non-zero");
    }

    #[test]
    fn rejects_widening_permissions() {
        let mut caps = CapabilitySet::new();
        let slot = caps.grant(cid(1), AuthRequired::Signature).unwrap();
        // Either is *broader* than Signature.
        let result = caps.attenuate_in_place(slot, AuthRequired::Either, None, None);
        assert!(result.is_none(), "must reject widening Signature -> Either");
        // Cap state must be unchanged on rejection.
        assert_eq!(
            caps.lookup(slot).unwrap().permissions,
            AuthRequired::Signature
        );
    }

    #[test]
    fn rejects_unknown_slot() {
        let mut caps = CapabilitySet::new();
        let result = caps.attenuate_in_place(99, AuthRequired::Signature, None, None);
        assert!(result.is_none());
    }

    #[test]
    fn rejects_effect_mask_widening() {
        let mut caps = CapabilitySet::new();
        // Start with a faceted cap allowing only TRANSFER.
        let slot = caps
            .grant_faceted(
                cid(1),
                AuthRequired::Signature,
                crate::facet::EFFECT_TRANSFER,
            )
            .unwrap();
        // Try to widen to TRANSFER | SET_FIELD.
        let result = caps.attenuate_in_place(
            slot,
            AuthRequired::Signature,
            Some(crate::facet::EFFECT_TRANSFER | crate::facet::EFFECT_SET_FIELD),
            None,
        );
        assert!(result.is_none(), "must reject mask widening");
        assert_eq!(
            caps.lookup(slot).unwrap().allowed_effects,
            Some(crate::facet::EFFECT_TRANSFER)
        );
    }

    #[test]
    fn rejects_expiry_extension() {
        let mut caps = CapabilitySet::new();
        let slot = caps
            .grant_with_expiry(cid(1), AuthRequired::Signature, 100)
            .unwrap();
        let result = caps.attenuate_in_place(slot, AuthRequired::Signature, None, Some(200));
        assert!(
            result.is_none(),
            "must reject expiry extension (100 -> 200)"
        );
        assert_eq!(caps.lookup(slot).unwrap().expires_at, Some(100));
    }

    #[test]
    fn allows_expiry_shrinking() {
        let mut caps = CapabilitySet::new();
        let slot = caps
            .grant_with_expiry(cid(1), AuthRequired::Signature, 100)
            .unwrap();
        let h = caps
            .attenuate_in_place(slot, AuthRequired::Signature, None, Some(50))
            .expect("expiry shrink 100 -> 50 must succeed");
        assert_eq!(caps.lookup(slot).unwrap().expires_at, Some(50));
        assert_ne!(h, [0u8; 32]);
    }

    #[test]
    fn allows_unbounded_to_bounded_expiry() {
        let mut caps = CapabilitySet::new();
        let slot = caps.grant(cid(1), AuthRequired::Signature).unwrap();
        assert_eq!(caps.lookup(slot).unwrap().expires_at, None);
        let _ = caps
            .attenuate_in_place(slot, AuthRequired::Signature, None, Some(1000))
            .expect("None -> Some(1000) is narrowing");
        assert_eq!(caps.lookup(slot).unwrap().expires_at, Some(1000));
    }

    #[test]
    fn allows_effect_mask_narrowing() {
        let mut caps = CapabilitySet::new();
        let slot = caps
            .grant_faceted(
                cid(1),
                AuthRequired::Signature,
                crate::facet::EFFECT_TRANSFER | crate::facet::EFFECT_SET_FIELD,
            )
            .unwrap();
        let _ = caps
            .attenuate_in_place(
                slot,
                AuthRequired::Signature,
                Some(crate::facet::EFFECT_TRANSFER),
                None,
            )
            .expect("mask narrowing to TRANSFER alone must succeed");
        assert_eq!(
            caps.lookup(slot).unwrap().allowed_effects,
            Some(crate::facet::EFFECT_TRANSFER)
        );
    }

    /// Slot identity must be preserved across attenuation — this is
    /// the structural difference between in-place attenuation and the
    /// revoke-and-reissue workaround.
    #[test]
    fn slot_and_target_preserved_across_narrowing() {
        let mut caps = CapabilitySet::new();
        let target = cid(42);
        let slot = caps.grant(target, AuthRequired::Either).unwrap();
        let before_slot = caps.lookup(slot).unwrap().slot;
        let before_target = caps.lookup(slot).unwrap().target;
        let _ = caps
            .attenuate_in_place(slot, AuthRequired::Signature, None, None)
            .unwrap();
        assert_eq!(caps.lookup(slot).unwrap().slot, before_slot);
        assert_eq!(caps.lookup(slot).unwrap().target, before_target);
    }

    /// Commitment must change when the narrowed cap differs from the
    /// original — this is what makes c-list audit indices updatable
    /// in a single deterministic step.
    #[test]
    fn commitment_changes_when_cap_narrows() {
        let mut caps = CapabilitySet::new();
        let slot = caps.grant(cid(1), AuthRequired::Either).unwrap();
        // First narrowing.
        let h1 = caps
            .attenuate_in_place(slot, AuthRequired::Signature, None, None)
            .unwrap();
        // Second narrowing to identical state — commitment must match.
        let h2 = caps
            .attenuate_in_place(slot, AuthRequired::Signature, None, None)
            .unwrap();
        assert_eq!(
            h1, h2,
            "identical narrowed state must produce equal commitments"
        );

        // Further narrowing to Impossible — commitment must differ.
        let h3 = caps
            .attenuate_in_place(slot, AuthRequired::Impossible, None, None)
            .unwrap();
        assert_ne!(
            h1, h3,
            "different narrowed state must produce different commitments"
        );
    }
}

#[cfg(test)]
mod revoke_tombstone_tests {
    //! The cap-crown REVOKE tombstone semantics: `revoke` drops the cap from the
    //! LOGICAL c-list AND records a tombstone (so the openable cap-root folds
    //! ZERO at the revoked slot's position, matching the in-circuit sel-24 gate).
    //! `restore` (rollback) clears the tombstone, returning the c-list — and thus
    //! the root — exactly to its pre-revoke value. (The cell↔circuit root
    //! byte-identity itself is pinned by the circuit-crate differential
    //! `cap_root_cell_circuit_differential::a2_revoke_*`, which can reach
    //! `dregg_circuit`.)
    use super::*;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    #[test]
    fn revoke_removes_from_logical_clist() {
        let mut caps = CapabilitySet::new();
        let s1 = caps.grant(cid(1), AuthRequired::Signature).unwrap();
        let s2 = caps.grant(cid(2), AuthRequired::Proof).unwrap();

        assert!(caps.revoke(s1), "revoke finds and removes s1");
        // Logical c-list: s1 gone, s2 present.
        assert!(
            caps.lookup(s1).is_none(),
            "revoked slot is logically absent"
        );
        assert!(caps.lookup(s2).is_some(), "other slot survives");
        assert!(
            !caps.has_access(&cid(1)),
            "revoked target no longer accessible"
        );
        assert!(caps.has_access(&cid(2)), "other target still accessible");
        // The slot is tombstoned.
        assert_eq!(
            caps.tombstoned_slots().collect::<Vec<_>>(),
            vec![s1],
            "the revoked slot is recorded as a tombstone"
        );
    }

    #[test]
    fn double_revoke_does_not_duplicate_tombstone() {
        let mut caps = CapabilitySet::new();
        let s = caps.grant(cid(1), AuthRequired::Signature).unwrap();
        assert!(caps.revoke(s));
        assert!(!caps.revoke(s), "second revoke finds nothing to remove");
        assert_eq!(
            caps.tombstoned_slots().collect::<Vec<_>>(),
            vec![s],
            "a tombstone is recorded exactly once"
        );
    }

    #[test]
    fn restore_clears_the_tombstone() {
        let mut caps = CapabilitySet::new();
        let s = caps.grant(cid(1), AuthRequired::Signature).unwrap();
        let cap = caps.lookup(s).cloned().unwrap();
        assert!(caps.revoke(s));
        assert_eq!(caps.tombstoned_slots().count(), 1);

        // Rollback re-inserts the cap; the tombstone must clear so the root
        // returns EXACTLY to the pre-revoke value.
        caps.restore(cap);
        assert!(
            caps.lookup(s).is_some(),
            "restored cap is back in the c-list"
        );
        assert_eq!(
            caps.tombstoned_slots().count(),
            0,
            "restore clears the tombstone (rollback is a true inverse of revoke)"
        );
    }

    #[test]
    fn capabilities_round_trip_through_postcard() {
        // The durable image (commit log / checkpoint / `canonical_ledger_root`) uses
        // the non-self-describing `postcard` codec, so a cap-carrying cell must
        // round-trip through it (SESSION RESUME needs a logged-in session's cap-tree
        // to survive a reopen). This is the regression pin for dropping
        // `skip_serializing_if` on `allowed_effects` (a skipped field desyncs
        // postcard's sequential decode).
        let mut caps = CapabilitySet::new();
        let _ = caps.grant(cid(3), AuthRequired::None).unwrap(); // allowed_effects: None
        let s = caps.grant(cid(4), AuthRequired::Signature).unwrap();
        assert!(caps.revoke(s)); // exercise a tombstone too
        let bytes = postcard::to_allocvec(&caps).expect("postcard serialize");
        let back: CapabilitySet = postcard::from_bytes(&bytes).expect("postcard round-trip");
        assert_eq!(
            back, caps,
            "a cap-carrying c-list round-trips through postcard"
        );
    }

    #[test]
    fn tombstone_survives_serde_round_trip() {
        // The `#[serde(default)]` on `tombstones` decodes legacy (no-`tombstones`)
        // JSON as an empty set, and a post-revoke set carries its tombstones.
        let mut caps = CapabilitySet::new();
        let s1 = caps.grant(cid(1), AuthRequired::Signature).unwrap();
        let _s2 = caps.grant(cid(2), AuthRequired::Proof).unwrap();
        assert!(caps.revoke(s1));

        let json = serde_json::to_string(&caps).expect("serialize");
        let back: CapabilitySet = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(
            back.tombstoned_slots().collect::<Vec<_>>(),
            vec![s1],
            "the tombstone set must round-trip (so the post-revoke root is stable across persistence)"
        );
        assert_eq!(back, caps, "the whole c-list round-trips");

        // Legacy compatibility: JSON WITHOUT a `tombstones` field decodes as an
        // empty tombstone set (so a never-revoked legacy cell's root is unchanged).
        let legacy_json = r#"{"refs":[],"next_slot":0}"#;
        let legacy: CapabilitySet = serde_json::from_str(legacy_json).expect("legacy decode");
        assert_eq!(
            legacy.tombstoned_slots().count(),
            0,
            "legacy c-list (no tombstones field) decodes with an empty tombstone set"
        );
    }
}
