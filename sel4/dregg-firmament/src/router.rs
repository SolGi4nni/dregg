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
    Backing, Capability, DistributedBacking, HostPdBacking, LocalBacking, Resolution, ResolveError,
    Rights, SurfaceBacking, Target,
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
    /// Surface: the recipient cell that receives the granted SURFACE cap (the
    /// app you hand a window to — e.g. sharing a read-only view of a window).
    /// A surface IS a cell, so this addressee is a [`CellId`] exactly like
    /// [`Recipient::DistributedCell`]; it is kept distinct only so the router's
    /// surface arm reads clearly.
    SurfaceCell(CellId),
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
    /// The surface fabric (the SURFACE backing) — the cells the compositor
    /// renders as windows. A surface IS a cell, so this backing is the same
    /// real-executor machinery as [`Self::distributed`], aimed at the glass.
    pub surface: SurfaceBacking,
    /// The host process-PD backing (the SANDBOXED-FIRMAMENT leg) — the registry
    /// of confined forked-child endpoints a [`Target::HostPd`] cap is invoked
    /// against over its firmament Endpoint.
    pub host: HostPdBacking,
    /// For a distributed OR surface handle, which cell HOLDS the cap being
    /// invoked / delegated. (The app's own cell — the firmament knows it; the
    /// app does not pass it, keeping the handle a pure `(target, rights)`.)
    pub holder_cell: Option<CellId>,
}

impl FirmamentRouter {
    /// A router over the given local + distributed backings, with a fresh empty
    /// surface fabric and no holder cell bound yet. Inject a seeded surface
    /// fabric via [`Self::with_surface`] (mirroring [`Self::with_holder`]).
    pub fn new(local: LocalBacking, distributed: DistributedBacking) -> Self {
        FirmamentRouter {
            local,
            distributed,
            surface: SurfaceBacking::new(),
            host: HostPdBacking::new(),
            holder_cell: None,
        }
    }

    /// Install the host process-PD backing (the seeded registry of confined
    /// forked-child endpoints). Mirrors [`Self::with_surface`]: the firmament
    /// supplies the registry; the app names only a `HostPd(id)` target.
    pub fn with_host(mut self, host: HostPdBacking) -> Self {
        self.host = host;
        self
    }

    /// Bind the app's own cell (the holder of distributed / surface caps). The
    /// firmament supplies this; the app's handle stays a pure `(target,
    /// rights)`.
    pub fn with_holder(mut self, holder: CellId) -> Self {
        self.holder_cell = Some(holder);
        self
    }

    /// Install the surface fabric (the seeded [`SurfaceBacking`] whose cells the
    /// compositor renders). Mirrors [`Self::with_holder`]: the firmament
    /// supplies the fabric; the app names only a `Surface(cell)` target.
    pub fn with_surface(mut self, surface: SurfaceBacking) -> Self {
        self.surface = surface;
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
            Target::Surface { cell } => {
                // A window IS a cell — present/draw resolves the surface cap
                // through the SAME real-executor authority check as a
                // distributed cell.
                let holder = self
                    .holder_cell
                    .ok_or_else(|| ResolveError::Unauthorized("no holder cell bound".into()))?;
                self.surface.invoke(holder, *cell, &cap.rights)
            }
            Target::HostPd { pd } => {
                // A confined forked-child PD reached over its firmament Endpoint
                // (the control socket) — a validated round-trip through the SAME
                // `granted ⊆ held` gate the kernel's ValidityTable enforces.
                self.host.invoke(*pd, &cap.rights)
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
                let child = self
                    .local
                    .mint(*slot, narrowed.rights.clone())
                    .ok_or_else(|| {
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
                    Recipient::LocalChild | Recipient::SurfaceCell(_) => {
                        return Err(ResolveError::Unauthorized(
                            "distributed delegate needs a distributed recipient cell".into(),
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
            Target::Surface { cell } => {
                // Handing a window to another app: the SAME real executor turn
                // (`Effect::GrantCapability`) and the SAME `granted ⊆ held`
                // gate as a distributed cell — a surface IS a cell. A widening
                // surface grant is rejected by the executor (DelegationDenied);
                // the backing-agnostic `Capability::attenuate` above already
                // refused it before we got here, and the executor re-checks
                // (defense in depth).
                let holder = self
                    .holder_cell
                    .ok_or_else(|| ResolveError::Unauthorized("no holder cell bound".into()))?;
                let to = match recipient {
                    Recipient::SurfaceCell(c) => c,
                    Recipient::LocalChild | Recipient::DistributedCell(_) => {
                        return Err(ResolveError::Unauthorized(
                            "surface delegate needs a surface recipient cell".into(),
                        ))
                    }
                };
                self.surface
                    .delegate(holder, to, *cell, narrowed.rights.clone())?;
                // The recipient's handle is the same surface with narrowed rights.
                Ok(Capability::surface(*cell, narrowed.rights))
            }
            Target::HostPd { pd } => {
                // Hand a confined host-PD's Endpoint to another holder with
                // NARROWED rights: the backing-agnostic `Capability::attenuate`
                // above already enforced `granted ⊆ held` (the SAME gate the
                // kernel's ValidityTable re-checks at every invocation — defense
                // in depth). Phase 0 reuses that attenuation: the recipient's
                // handle is the same host-PD with the narrowed rights. (A
                // separate-recipient SCM_RIGHTS fd-pass of the Endpoint is the
                // next slice; Phase 0 covers the in-process attenuated grant.)
                let _ = recipient; // Endpoint-only Phase 0 keeps the same addressee.
                Ok(Capability::host_pd(*pd, narrowed.rights))
            }
        }
    }
}

impl FirmamentRouter {
    /// Convenience: which backing WOULD resolve this handle — purely for
    /// assertions/logging. (The app never calls this; it cannot tell.) A local
    /// target resolves via the kernel; a distributed cell AND a surface (which
    /// IS a cell) both resolve via a real executor turn.
    pub fn backing_of(cap: &Capability) -> Backing {
        if cap.target.is_local() {
            Backing::LocalKernel
        } else if cap.target.is_host_pd() {
            // A confined forked-child PD over its firmament Endpoint.
            Backing::HostPdEndpoint
        } else {
            // Distributed cell or Surface — both go through the executor turn.
            Backing::DistributedTurn
        }
    }
}
