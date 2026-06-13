//! The ROUTER — the dispatcher that makes the handle backing-agnostic.
//!
//! This is the piece that realizes the fluid reach-out: an app holds a single
//! [`Capability`] and calls [`Router::resolve`] / [`Router::attenuate_and_grant`].
//! The router looks ONLY at the handle's [`Target`] to decide whether to go
//! down the LOCAL kernel path or the DISTRIBUTED executor→net path. **The app
//! code does not branch on backing** — it cannot tell which one it holds; only
//! the [`Bounds`] in the returned [`Resolution`] relax as `n` rises.
//!
//! `FIRMAMENT.md §3`: "The app does not see which backing it holds. It holds a
//! capability; it invokes it; the firmament routes the invocation to the
//! kernel (local) or the executor→net path (distributed)."

use dregg_types::CellId;

use crate::{
    Backing, Capability, DistributedBacking, LocalBacking, Resolution, ResolveError, Rights, Target,
};

/// The router interface an app sees. ONE handle in, a resolution out — the
/// app never names a backing.
pub trait Router {
    /// Invoke the capability. Dispatches to the kernel (local) or a real turn
    /// (distributed) purely by the handle's [`Target`].
    fn resolve(&self, cap: &Capability) -> Result<Resolution, ResolveError>;

    /// Attenuate the handle to `narrower` and DELEGATE it to a recipient,
    /// enforcing `granted ⊆ held` at whichever backing the target lives on
    /// (`seL4_CNode_Mint`-reduced-rights locally; the real `recKDelegateAtten`
    /// turn distributedly). Returns the recipient's new handle.
    ///
    /// `recipient` is the local CNode slot owner (ignored for local — the new
    /// minted slot IS the delegation) or the distributed recipient cell.
    fn attenuate_and_grant(
        &mut self,
        cap: &Capability,
        narrower: Rights,
        recipient: Recipient,
    ) -> Result<Capability, ResolveError>;
}

/// Who a delegation goes to, named uniformly. For a local target the recipient
/// IS the minted child slot (no separate addressee needed); for a distributed
/// target it is the recipient cell.
#[derive(Clone, Debug)]
pub enum Recipient {
    /// Local: the minted child slot is the delegation; no addressee.
    LocalChild,
    /// Distributed: the recipient cell that receives the granted cap.
    DistributedCell(CellId),
}

/// The firmament's router: it owns both backings and dispatches between them.
///
/// This is the firmament's capability fabric (`FIRMAMENT.md §2`, the "cap
/// fabric" row): one router over the seL4 cap graph (local) AND the dregg cap
/// graph (distributed), presenting one interface.
pub struct FirmamentRouter {
    /// The seL4 cap space (the local backing).
    pub local: LocalBacking,
    /// The dregg federation (the distributed backing).
    pub distributed: DistributedBacking,
    /// For a distributed handle, which cell HOLDS the cap being invoked /
    /// delegated. (The app's own cell — the firmament knows it; the app does
    /// not pass it, keeping the handle a pure `(target, rights)`.)
    pub holder_cell: Option<CellId>,
}

impl FirmamentRouter {
    /// A router over the given backings, with no holder cell bound yet.
    pub fn new(local: LocalBacking, distributed: DistributedBacking) -> Self {
        FirmamentRouter { local, distributed, holder_cell: None }
    }

    /// Bind the app's own cell (the holder of distributed caps). The firmament
    /// supplies this; the app's handle stays a pure `(target, rights)`.
    pub fn with_holder(mut self, holder: CellId) -> Self {
        self.holder_cell = Some(holder);
        self
    }
}

impl Router for FirmamentRouter {
    fn resolve(&self, cap: &Capability) -> Result<Resolution, ResolveError> {
        match &cap.target {
            Target::Local { slot } => self.local.invoke(*slot, &cap.rights),
            Target::Distributed { cell } => {
                let holder = self
                    .holder_cell
                    .ok_or_else(|| ResolveError::Unauthorized("no holder cell bound".into()))?;
                self.distributed.invoke(holder, *cell, &cap.rights)
            }
        }
    }

    fn attenuate_and_grant(
        &mut self,
        cap: &Capability,
        narrower: Rights,
        recipient: Recipient,
    ) -> Result<Capability, ResolveError> {
        // The backing-AGNOSTIC pre-check (the same `is_attenuation` for both):
        // a widening is refused before we even touch a backing. This is the
        // unified handle's own attenuate (`Capability::attenuate`).
        let narrowed = cap.attenuate(narrower.clone()).ok_or_else(|| {
            ResolveError::Unauthorized(format!(
                "non-attenuating: {:?} is wider than held {:?}",
                narrower, cap.rights
            ))
        })?;

        match &cap.target {
            Target::Local { slot } => {
                // seL4_CNode_Mint with reduced rights — the backing ENFORCES
                // the narrowing too (defense in depth: the handle pre-checked,
                // the kernel re-checks).
                let child = self.local.mint(*slot, narrowed.rights.clone()).ok_or_else(|| {
                    ResolveError::BackingRejected("seL4_CNode_Mint refused (amplifying)".into())
                })?;
                // The delegated handle points at the new child slot.
                Ok(Capability::local(child, narrowed.rights))
            }
            Target::Distributed { cell } => {
                let holder = self
                    .holder_cell
                    .ok_or_else(|| ResolveError::Unauthorized("no holder cell bound".into()))?;
                let to = match recipient {
                    Recipient::DistributedCell(c) => c,
                    Recipient::LocalChild => {
                        return Err(ResolveError::Unauthorized(
                            "distributed delegate needs a recipient cell".into(),
                        ))
                    }
                };
                // The REAL recKDelegateAtten turn through the executor — it
                // enforces `granted ⊆ held` itself.
                self.distributed
                    .delegate(holder, to, *cell, narrowed.rights.clone())?;
                // The recipient's handle is the same target with narrowed rights.
                Ok(Capability::distributed(*cell, narrowed.rights))
            }
        }
    }
}

impl FirmamentRouter {
    /// Convenience: which backing WOULD resolve this handle — purely for
    /// assertions/logging. (The app never calls this; it cannot tell.)
    pub fn backing_of(cap: &Capability) -> Backing {
        if cap.target.is_local() {
            Backing::LocalKernel
        } else {
            Backing::DistributedTurn
        }
    }
}
