//! Snapshot+refresh delegation model for capability inheritance.
//!
//! In E-style delegation, a child cell inherits its parent's capabilities as a
//! SNAPSHOT. The child can act offline using the snapshot, and periodically
//! refreshes to pick up new capabilities. Revocation is eventual, bounded by
//! `max_staleness` — acceptors may reject stale snapshots at verification time.
//!
//! # Commitment Binding
//!
//! To prevent a malicious parent from constructing a `DelegatedRef` containing
//! fabricated capabilities, the struct includes a `clist_commitment` field: a
//! BLAKE3 hash of the parent's serialized c-list at snapshot time. Verifiers can
//! cross-check this commitment against the parent's known state on the ledger.
//!
//! # ⚠ No parent signs, and no verifier checks — measured 2026-08-06
//!
//! This header read *"the parent signs over `(clist_commitment,
//! delegation_epoch, child_cell_id)` so that a verifier can cryptographically
//! confirm the delegation is authentic"*, in the present tense. Neither half
//! happens. All three production minters (`apply_spawn_with_delegation`,
//! `apply_refresh_delegation`, and `execute_tree`'s
//! `DelegationMode::SnapshotRefresh` auto-install) write `[0u8; 64]` into
//! [`DelegatedRef::parent_signature`], and the verifier that would have read it
//! (`dregg_cell_crypto::delegation::verify_parent_signature`) had zero callers
//! and was deleted on 2026-08-06.
//!
//! The authenticity the deleted sentence promised comes from somewhere else and
//! always did: a snapshot is minted only while applying a turn the parent's own
//! key signed. `exec_lean::lean_shadow`'s snapshot-authority fence records the
//! decision that a snapshot is an ATTESTATION, not an authority edge — the
//! verified kernel carries `delegations` / `delegationEpoch` as REGISTRY state
//! and `authorizedB` reads only the live c-list. What is genuinely checked here
//! is [`DelegatedRef::clist_commitment`], and only at INSTALL.

use serde::{Deserialize, Serialize};

use crate::capability::CapabilityRef;
use crate::id::CellId;

/// Serde helper for `[u8; 64]` (Ed25519 signatures in DelegatedRef).
mod delegation_sig_serde {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], ser: S) -> Result<S::Ok, S::Error> {
        bytes.as_slice().serialize(ser)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(de: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Vec::deserialize(de)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes for signature"))
    }
}

/// A delegated capability snapshot from a parent cell.
///
/// This represents the E-style delegation model: the child receives a point-in-time
/// copy of the parent's c-list. The child can act using this snapshot without
/// contacting the parent. Freshness is checked by acceptors (remote verifiers),
/// not by the executor.
///
/// # Security: Commitment Binding
///
/// The `clist_commitment` is a BLAKE3 hash of the parent's full serialized c-list
/// at the time this snapshot was created. This binds the delegated capabilities to
/// the parent's actual state — a malicious parent cannot fabricate capabilities that
/// weren't in their c-list without producing an invalid commitment.
///
/// ⚠ The `parent_signature` field proves NOTHING — see the module header and
/// the field's own doc. It is `[0u8; 64]` at every minter and has had no reader
/// since 2026-08-06.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DelegatedRef {
    /// The parent cell this delegation comes from.
    pub source: CellId,
    /// The child cell this delegation targets.
    pub child: CellId,
    /// Snapshot of capabilities inherited from parent.
    pub snapshot: Vec<CapabilityRef>,
    /// Parent's delegation epoch when this snapshot was taken.
    pub delegation_epoch: u64,
    /// Timestamp when this snapshot was last refreshed.
    pub refreshed_at: u64,
    /// Maximum acceptable staleness (seconds). Acceptors may reject
    /// if `now - refreshed_at > max_staleness`. Zero means "always refresh."
    pub max_staleness: u64,
    /// BLAKE3 hash of the parent's full serialized c-list at snapshot time.
    ///
    /// Verifiers cross-check this against the parent's known ledger state to
    /// confirm the delegated capabilities were actually held by the parent.
    /// If the parent revokes or changes their c-list, this commitment won't match.
    pub clist_commitment: [u8; 32],
    /// ⚑ **AN INERT 64-BYTE FIELD. It is `[0u8; 64]` at every writer and has no
    /// reader.** This said "Proves the parent authorized this delegation.
    /// Verifiable against the parent's public key without contacting the
    /// parent" until 2026-08-06 — it proved nothing then either, and the
    /// verifier that clause pointed at
    /// (`dregg_cell_crypto::delegation::verify_parent_signature`) had zero
    /// callers and is now deleted.
    ///
    /// It is REDUNDANT, not merely unfilled: a snapshot is minted only while
    /// applying a turn the parent's key already signed, which is where the
    /// authorization actually comes from. The right end state is to delete this
    /// field and [`DelegatedRef::signing_message`] with it; that changes the
    /// persisted `Cell` shape, so it is a `CANONICAL_STATE_SCHEMA_EPOCH` bump
    /// plus a re-genesis and belongs to whoever moves the epoch. Until then, do
    /// not build a check on it and do not describe it as one.
    #[serde(with = "delegation_sig_serde")]
    pub parent_signature: [u8; 64],
}

impl DelegatedRef {
    /// Create a new delegated reference with commitment binding.
    ///
    /// The `clist_commitment` should be computed via [`Self::compute_clist_commitment`]
    /// over the parent's full c-list — that one is checked, at install.
    ///
    /// `parent_signature` is inert: every caller in the tree passes `[0u8; 64]`
    /// and nothing reads it. See its field doc before writing anything else there.
    pub fn new(
        source: CellId,
        child: CellId,
        snapshot: Vec<CapabilityRef>,
        delegation_epoch: u64,
        refreshed_at: u64,
        max_staleness: u64,
        clist_commitment: [u8; 32],
        parent_signature: [u8; 64],
    ) -> Self {
        DelegatedRef {
            source,
            child,
            snapshot,
            delegation_epoch,
            refreshed_at,
            max_staleness,
            clist_commitment,
            parent_signature,
        }
    }

    /// Compute the BLAKE3 commitment over a serialized c-list.
    ///
    /// The input should be the postcard-serialized bytes of the parent's full
    /// `CapabilitySet` (or `Vec<CapabilityRef>`) at the time of delegation.
    /// This is domain-separated to prevent cross-protocol confusion.
    pub fn compute_clist_commitment(serialized_clist: &[u8]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-delegation-clist-commitment-v1");
        hasher.update(serialized_clist);
        *hasher.finalize().as_bytes()
    }

    /// The message a parent WOULD sign for this delegation:
    /// `BLAKE3_derive_key("dregg-delegation-sig-v1", clist_commitment || delegation_epoch_le || child_cell_id_bytes)`
    ///
    /// ⚠ Conditional on purpose. No parent signs it, nothing verifies it, and
    /// this function has had no caller since
    /// `dregg_cell_crypto::delegation::verify_parent_signature` was deleted on
    /// 2026-08-06. It survives only as the other half of
    /// [`Self::parent_signature`] and goes when that field does.
    pub fn signing_message(
        clist_commitment: &[u8; 32],
        delegation_epoch: u64,
        child_cell_id: &CellId,
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-delegation-sig-v1");
        hasher.update(clist_commitment);
        hasher.update(&delegation_epoch.to_le_bytes());
        hasher.update(child_cell_id.as_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Check if this delegation is stale relative to the given timestamp.
    ///
    /// A staleness of zero means "always stale" (always refresh before use).
    /// Otherwise, the delegation is stale if `now - refreshed_at > max_staleness`.
    pub fn is_stale(&self, now: u64) -> bool {
        if self.max_staleness == 0 {
            return true; // always stale = always refresh
        }
        now.saturating_sub(self.refreshed_at) > self.max_staleness
    }

    /// Every LIVE ([`CapabilityRef::is_live_at`]) capability in this snapshot
    /// that targets `target`, in snapshot order.
    ///
    /// ⚑ **This takes a height, and the height is not optional.** The predicates
    /// this replaced — `has_capability(target)` and `capabilities_for(target)` —
    /// matched on TARGET EQUALITY ALONE. A snapshot is a verbatim copy of the
    /// parent's c-list entries, `expires_at` and `permissions` included, so a
    /// frozen (`Impossible`) or lapsed capability sat in the snapshot conferring
    /// full cross-cell authority through every check shaped around the c-list —
    /// where the same capability was correctly refused by
    /// [`crate::CapabilitySet::has_access_at`].
    ///
    /// Snapshot staleness (revocation being EVENTUAL, bounded by
    /// `max_staleness`) is a genuine property of this design and is unaffected:
    /// liveness here reads fields the snapshot itself carries, needing no
    /// contact with the parent and no freshness assumption.
    pub fn live_capabilities_at<'a>(
        &'a self,
        target: &CellId,
        current_height: u64,
    ) -> impl Iterator<Item = &'a CapabilityRef> + 'a {
        let target = *target;
        self.snapshot
            .iter()
            .filter(move |cap| cap.target == target && cap.is_live_at(current_height))
    }

    /// Is `target` NAMED anywhere in this snapshot, live or not?
    ///
    /// ⚠ **Presence, not authority.** This is the raw structural query — it is
    /// the right tool for "did the refresh pick the new grant up?" and the wrong
    /// tool for every authorization decision. Authority goes through
    /// [`crate::Cell::resolve_authority_at`].
    pub fn names_target(&self, target: &CellId) -> bool {
        self.snapshot.iter().any(|cap| &cap.target == target)
    }

    /// Number of capabilities in this snapshot.
    pub fn len(&self) -> usize {
        self.snapshot.len()
    }

    /// Whether the snapshot is empty.
    pub fn is_empty(&self) -> bool {
        self.snapshot.is_empty()
    }
}
