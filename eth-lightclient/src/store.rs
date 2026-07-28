//! Weak-subjectivity sync-committee store — the composition boundary that keeps the
//! sound BLS verify-core ([`crate::verify_sync_aggregate`] /
//! [`crate::finality::verify_finalized_update`]) from ever being fed an
//! RPC-supplied committee.
//!
//! ## The hole this closes
//!
//! [`crate::finality::verify_finalized_update`] and [`crate::verify_sync_aggregate`]
//! USED TO take the trusted `committee_pubkeys` and `genesis_validators_root` as BARE
//! CALLER ARGS. The verify-core is sound *given* the right committee — but if an
//! integration feeds it a 512-key committee an untrusted RPC returned, a forged committee
//! "signs" a forged header, the gate accepts (the forged keys really did sign), and the
//! whole 2/3-of-512 BLS floor goes VACUOUS. The BLS math is never the weak point of a
//! light client; *learning the right committee* is.
//!
//! ⚠ **Having the store was not the same as USING it.** The store landed in `27b15fa95`
//! and closed the trust discipline, but `verify_finalized_update` stayed `pub` with its
//! bare-committee signature, so the un-anchored spelling remained the SHORTEST one and
//! looked exactly like the anchored one at the call site. That is the shape this repo
//! files under "gating defaults to silence": the protection existed, was correct, was
//! tested — and nothing made a caller reach for it. `verify_finalized_update` now demands
//! a [`crate::TrustedCommittee`], obtainable from [`WeakSubjectivityStore::trusted_committee`]
//! or from the loud [`crate::TrustedCommittee::new_unchecked`] and nowhere else.
//!
//! `verify_sync_aggregate` deliberately keeps its bare-committee signature: it is a
//! PROJECTION carrier over one header, it mints no [`FinalizedExecution`], and no trust
//! state advances on its result. The unforgeability anchor is the `FinalizedExecution`,
//! and that is what is now gated.
//!
//! ## The store's trust discipline
//!
//! A real light client anchors trust at a **weak-subjectivity checkpoint**: a
//! governance-provided (NOT RPC-provided) constant that pins the chain's identity.
//! From that anchor the current sync committee is only ever advanced by a
//! cryptographic rotation the *currently trusted* committee vouches for. This store
//! enforces exactly that:
//!
//!   * The anchor is pinned by governance — either a trusted beacon **state root**
//!     ([`WeakSubjectivityStore::pin_checkpoint`]) that the genesis committee is
//!     bootstrapped under, or the genesis **committee** itself
//!     ([`WeakSubjectivityStore::pin_genesis_committee`]). The
//!     `genesis_validators_root` is pinned alongside it. None of these are ever taken
//!     from a caller's per-update input.
//!   * The committee advances ONLY through
//!     [`WeakSubjectivityStore::bootstrap_committee`] (prove the first committee under
//!     the pinned checkpoint state root via [`crate::verify_committee_update`]) or
//!     [`WeakSubjectivityStore::advance`] (verify a finalized update signed by the
//!     CURRENT trusted committee, then prove the NEXT committee's
//!     `next_sync_committee` Merkle branch under the state root that update attested).
//!     A committee that is not a valid rotation from the pinned genesis is REFUSED.
//!   * [`WeakSubjectivityStore::verify`] — the entrypoint an integration calls to turn
//!     an update into a [`crate::finality::FinalizedExecution`] — takes the committee
//!     and `genesis_validators_root` FROM THE STORE, never from the caller. Before any
//!     committee is established it fails closed ([`StoreError::NoTrustedCommittee`]).
//!
//! The `genesis_validators_root` stays pinned in the store because it, together with
//! the fork version, fixes the signing domain — a wrong pinned root refuses every real
//! signature (see the store's gvr-mismatch falsifier). The fork version remains a
//! per-slot parameter: it legitimately changes across forks and a wrong one can only
//! make verification FAIL (wrong domain -> `BadSignature`), never forge acceptance.

use crate::finality::{verify_finalized_update, FinalizedExecution, LightClientUpdate};
use crate::{verify_committee_update, Error, SyncCommittee, TrustedCommittee, SYNC_COMMITTEE_SIZE};

/// Fail-closed errors for the store's trust-advance and verify paths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StoreError {
    /// No trusted committee has been established yet: the store was pinned to a
    /// checkpoint state root but the genesis committee has not been bootstrapped from
    /// it. `verify`/`advance` refuse (fail closed) rather than accept anything.
    NoTrustedCommittee,
    /// A pinned committee (or one offered to `bootstrap_committee`/`advance`) is not
    /// exactly [`SYNC_COMMITTEE_SIZE`] pubkeys — it could never verify, so it is
    /// rejected at the boundary.
    WrongCommitteeSize { got: usize },
    /// The committee-rotation Merkle proof did not chain from the trusted state root:
    /// the offered committee is not the `next_sync_committee` the currently trusted
    /// state commits. A committee not descended from the pinned genesis lands here.
    UnchainedCommittee(Error),
    /// The finalized-update verification (sync-committee BLS / finality branch /
    /// execution branch) failed against the store's trusted committee + pinned
    /// `genesis_validators_root`.
    Verify(Error),
    /// The advance is not monotonic: the update's attested slot is not ahead of the
    /// slot the store has already advanced to (an old update cannot rotate the
    /// committee backward).
    NonMonotonic {
        trusted_slot: u64,
        attested_slot: u64,
    },
}

impl core::fmt::Display for StoreError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for StoreError {}

/// A weak-subjectivity sync-committee store: the pinned trust root plus the current
/// trusted committee, advanced only by cryptographic rotation from genesis.
///
/// Construct one with [`WeakSubjectivityStore::pin_checkpoint`] (pin a governance
/// beacon state root, then [`bootstrap_committee`](WeakSubjectivityStore::bootstrap_committee))
/// or [`WeakSubjectivityStore::pin_genesis_committee`] (pin the committee directly).
/// There is no other constructor: you cannot obtain a store without pinning a genesis,
/// so the "no pinned genesis => refuse" property holds by construction.
#[derive(Debug, Clone)]
pub struct WeakSubjectivityStore {
    /// Pinned `genesis_validators_root` — half of the signing domain, a governance
    /// constant. NEVER taken from a caller's per-update input.
    genesis_validators_root: [u8; 32],
    /// The governance-pinned trusted beacon **state root** the genesis committee is
    /// bootstrapped under (via `verify_committee_update`). Updated to the attested
    /// state root on each `advance` so it always names the state whose
    /// `next_sync_committee` the store last proved.
    trusted_state_root: [u8; 32],
    /// The current trusted sync committee. `None` until bootstrapped from the pinned
    /// checkpoint state root — the fail-closed state.
    current_committee: Option<SyncCommittee>,
    /// The sync-committee period the current committee serves (bookkeeping / report).
    current_period: u64,
    /// The highest attested slot the store has advanced to (monotonic guard). `0`
    /// until the first `advance`.
    trusted_slot: u64,
}

impl WeakSubjectivityStore {
    /// Pin a weak-subjectivity checkpoint: a governance-trusted beacon **state root**
    /// plus the `genesis_validators_root`. The genesis committee is NOT yet known —
    /// call [`bootstrap_committee`](Self::bootstrap_committee) to prove it under this
    /// state root. Until then the store is fail-closed ([`StoreError::NoTrustedCommittee`]).
    ///
    /// `trusted_state_root` is the checkpoint's beacon `state_root` (in production, a
    /// FINALIZED header's state root shipped as a governance constant / config). It is
    /// the root of trust, so it must NOT be an RPC value.
    pub fn pin_checkpoint(
        trusted_state_root: [u8; 32],
        genesis_validators_root: [u8; 32],
        checkpoint_period: u64,
    ) -> Self {
        WeakSubjectivityStore {
            genesis_validators_root,
            trusted_state_root,
            current_committee: None,
            current_period: checkpoint_period,
            trusted_slot: 0,
        }
    }

    /// Pin the genesis sync committee directly (a governance constant) alongside the
    /// `genesis_validators_root`. Equivalent trust to [`pin_checkpoint`](Self::pin_checkpoint)
    /// followed by a bootstrap, for deployments that ship the committee itself rather
    /// than a checkpoint state root. Fails closed if the committee is not exactly
    /// [`SYNC_COMMITTEE_SIZE`] pubkeys.
    pub fn pin_genesis_committee(
        genesis_committee: SyncCommittee,
        genesis_validators_root: [u8; 32],
        genesis_period: u64,
    ) -> Result<Self, StoreError> {
        if genesis_committee.pubkeys.len() != SYNC_COMMITTEE_SIZE {
            return Err(StoreError::WrongCommitteeSize {
                got: genesis_committee.pubkeys.len(),
            });
        }
        Ok(WeakSubjectivityStore {
            genesis_validators_root,
            // A directly-pinned committee has no proven anchoring state root yet; the
            // first `advance` establishes one from a signed update.
            trusted_state_root: [0u8; 32],
            current_committee: Some(genesis_committee),
            current_period: genesis_period,
            trusted_slot: 0,
        })
    }

    /// Bootstrap the genesis committee from the pinned checkpoint state root: prove the
    /// offered committee is the `next_sync_committee` committed by the trusted state
    /// (via [`crate::verify_committee_update`]). This is the ONLY way to install the
    /// first committee on a [`pin_checkpoint`](Self::pin_checkpoint) store — a committee
    /// whose rotation branch does not reconstruct the pinned state root is REFUSED, so
    /// no RPC-supplied committee can be installed.
    pub fn bootstrap_committee(
        &mut self,
        committee: SyncCommittee,
        next_sync_committee_branch: &[[u8; 32]],
    ) -> Result<(), StoreError> {
        if committee.pubkeys.len() != SYNC_COMMITTEE_SIZE {
            return Err(StoreError::WrongCommitteeSize {
                got: committee.pubkeys.len(),
            });
        }
        verify_committee_update(
            &committee,
            next_sync_committee_branch,
            &self.trusted_state_root,
        )
        .map_err(StoreError::UnchainedCommittee)?;
        // The committee committed by the checkpoint state (period P) serves period P+1.
        self.current_period = self.current_period.saturating_add(1);
        self.current_committee = Some(committee);
        Ok(())
    }

    /// Advance the trusted committee by one rotation, chained over a finalized update:
    ///
    ///   1. verify the `update` with the CURRENT trusted committee + the pinned
    ///      `genesis_validators_root` ([`verify_finalized_update`]) — the current
    ///      committee must have signed the attested header at >= 2/3 AND the finalized
    ///      header must be proven (reorg-safe: we only advance at a *finalized* header);
    ///   2. require the advance to be monotonic (attested slot ahead of the trusted slot);
    ///   3. prove `next_committee` is the `next_sync_committee` under the state root the
    ///      current committee just attested ([`crate::verify_committee_update`]).
    ///
    /// Only if all three hold is the committee rotated. Any failure leaves the store's
    /// committee UNCHANGED and returns an error (fail closed) — a non-chained committee
    /// can never be installed even after a genuinely-signed update.
    ///
    /// Returns the [`FinalizedExecution`] the verified update advances to (so a caller
    /// can both rotate the committee and consume the finalized execution root in one
    /// authenticated step).
    pub fn advance(
        &mut self,
        update: &LightClientUpdate,
        next_committee: SyncCommittee,
        next_sync_committee_branch: &[[u8; 32]],
        fork_version: [u8; 4],
    ) -> Result<FinalizedExecution, StoreError> {
        if next_committee.pubkeys.len() != SYNC_COMMITTEE_SIZE {
            return Err(StoreError::WrongCommitteeSize {
                got: next_committee.pubkeys.len(),
            });
        }
        let trusted = self.trusted_committee()?;

        // (1) The current trusted committee must have signed a finalized update.
        let finalized =
            verify_finalized_update(update, &trusted, fork_version).map_err(StoreError::Verify)?;

        // (2) Monotonic: an old update cannot rotate the committee backward.
        let attested_slot = update.attested_header.slot;
        if attested_slot <= self.trusted_slot {
            return Err(StoreError::NonMonotonic {
                trusted_slot: self.trusted_slot,
                attested_slot,
            });
        }

        // (3) The next committee is the `next_sync_committee` under the state the
        //     current committee just attested — a real rotation, not a caller claim.
        verify_committee_update(
            &next_committee,
            next_sync_committee_branch,
            &update.attested_header.state_root,
        )
        .map_err(StoreError::UnchainedCommittee)?;

        // Rotate.
        self.trusted_state_root = update.attested_header.state_root;
        self.trusted_slot = attested_slot;
        self.current_period = self.current_period.saturating_add(1);
        self.current_committee = Some(next_committee);
        Ok(finalized)
    }

    /// Verify a finalized update against the STORE's trusted committee and pinned
    /// `genesis_validators_root` — the entrypoint that closes finding #13. The caller
    /// supplies only the (self-authenticating) `update` and the per-slot `fork_version`;
    /// it can NOT inject the committee or the genesis root. Fails closed with
    /// [`StoreError::NoTrustedCommittee`] before any committee is established.
    pub fn verify(
        &self,
        update: &LightClientUpdate,
        fork_version: [u8; 4],
    ) -> Result<FinalizedExecution, StoreError> {
        let trusted = self.trusted_committee()?;
        verify_finalized_update(update, &trusted, fork_version).map_err(StoreError::Verify)
    }

    /// **The trust anchor** — the store's current committee paired with its pinned
    /// `genesis_validators_root`, as the [`TrustedCommittee`] witness
    /// [`crate::finality::verify_finalized_update`] demands.
    ///
    /// This is the ONLY constructor of a `TrustedCommittee` that certifies anything: the pubkeys
    /// were reached by [`bootstrap_committee`](Self::bootstrap_committee) /
    /// [`advance`](Self::advance) from the pinned genesis, and the `genesis_validators_root` is
    /// the governance constant, never a caller argument. Before any committee is established it
    /// is [`StoreError::NoTrustedCommittee`] — a caller cannot get a witness out of an
    /// un-bootstrapped store, so the fail-closed state cannot be spent as an accept.
    ///
    /// Exposed (rather than kept private behind [`verify`](Self::verify)) so an integration that
    /// needs the raw `verify_finalized_update` — a differential run, a caller composing its own
    /// pipeline — can still be ANCHORED. Reaching for
    /// [`TrustedCommittee::new_unchecked`] because the anchored witness was unobtainable would be
    /// the worst of both worlds.
    pub fn trusted_committee(&self) -> Result<TrustedCommittee<'_>, StoreError> {
        let committee = self
            .current_committee
            .as_ref()
            .ok_or(StoreError::NoTrustedCommittee)?;
        Ok(TrustedCommittee::anchored(
            &committee.pubkeys,
            self.genesis_validators_root,
        ))
    }

    /// The pinned `genesis_validators_root` (governance constant).
    pub fn genesis_validators_root(&self) -> [u8; 32] {
        self.genesis_validators_root
    }

    /// The sync-committee period the current trusted committee serves.
    pub fn current_period(&self) -> u64 {
        self.current_period
    }

    /// Whether a trusted committee has been established (`false` = fail-closed).
    pub fn has_trusted_committee(&self) -> bool {
        self.current_committee.is_some()
    }

    /// Read-only view of the current trusted committee (`None` until bootstrapped).
    /// There is deliberately no setter: the committee only changes through the
    /// cryptographic [`bootstrap_committee`](Self::bootstrap_committee) /
    /// [`advance`](Self::advance) paths.
    pub fn current_committee(&self) -> Option<&SyncCommittee> {
        self.current_committee.as_ref()
    }
}
