//! The HOST PROCESS-PD backing — the sandboxed-firmament leg of the router.
//!
//! A [`crate::Target::HostPd`] capability names a confined, forked child PD
//! whose ONLY channel is its firmament Endpoint (the [`crate::process_kernel`]
//! control socket). This backing is the registry of those endpoints + the rights
//! held over each, and it resolves an invocation by a VALIDATED round-trip over
//! the existing socketpair wire — the SAME `serve_one`/`round_trip` framing the
//! process kernel already speaks. Attenuation reuses the unified
//! `granted ⊆ held` gate (`is_attenuation`); the bounds are strong-local
//! (`n = 1`, one box).
//!
//! ## Why a registry, not a fresh wire
//!
//! `spawn_pd` already returns a [`crate::process_kernel::PdProcess`] whose
//! `kernel_sock` is the kernel's end of the control channel to the (now confined)
//! child. This backing simply REMEMBERS that endpoint under a [`crate::HostPdId`]
//! so a `(target = HostPd(id), rights)` capability can be invoked uniformly,
//! exactly like a `Local { slot }` cap is invoked against the CNode stub. The
//! invocation does not re-fork anything; it reaches the live child.
//!
//! ## Feature shape
//!
//! The real control-socket round-trip lives behind `process-pd` (it needs the
//! [`crate::process_kernel`] wire, which is Unix + `process-pd`). Without that
//! feature the backing is an empty registry that resolves nothing — the
//! `Target::HostPd` variant still exists (it is unconditional in [`crate`]), so
//! the router compiles in every feature combination; only the live wire is
//! feature-gated.

use crate::{Backing, Bounds, HostPdId, Resolution, ResolveError, Rights};

#[cfg(all(feature = "process-pd", unix))]
use std::collections::BTreeMap;

/// One registered host-PD endpoint: the rights held over it (the cap's
/// authority) + (under `process-pd`) the kernel's control socket to the child.
#[cfg(all(feature = "process-pd", unix))]
struct HostPdEntry {
    /// The rights held over this host-PD endpoint (the unified [`Rights`]
    /// lattice — the same `AuthRequired` every other firmament cap uses).
    rights: Rights,
    /// The kernel's end of the control socket to the confined child (the
    /// firmament Endpoint). An invocation is a validated round-trip on it.
    sock: std::os::unix::net::UnixStream,
}

/// The host process-PD backing: a registry of confined-child endpoints the
/// router invokes a [`crate::Target::HostPd`] capability against.
#[derive(Default)]
pub struct HostPdBacking {
    #[cfg(all(feature = "process-pd", unix))]
    entries: BTreeMap<HostPdId, HostPdEntry>,
    /// The next id to hand out (monotonic).
    next_id: u64,
}

impl HostPdBacking {
    /// A fresh, empty backing (no host-PDs registered yet).
    pub fn new() -> Self {
        HostPdBacking {
            #[cfg(all(feature = "process-pd", unix))]
            entries: BTreeMap::new(),
            next_id: 0,
        }
    }

    /// REGISTER a spawned, confined child's control endpoint under a fresh
    /// [`HostPdId`] with `rights`, returning the id. The router can then resolve
    /// a `Capability::host_pd(id, rights)` against it. Only available with the
    /// `process-pd` wire.
    #[cfg(all(feature = "process-pd", unix))]
    pub fn register(
        &mut self,
        sock: std::os::unix::net::UnixStream,
        rights: Rights,
    ) -> HostPdId {
        let id = HostPdId(self.next_id);
        self.next_id += 1;
        self.entries.insert(id, HostPdEntry { rights, sock });
        id
    }

    /// The rights held over a registered host-PD, if any.
    #[cfg(all(feature = "process-pd", unix))]
    pub fn rights_at(&self, pd: HostPdId) -> Option<Rights> {
        self.entries.get(&pd).map(|e| e.rights.clone())
    }

    /// INVOKE the host-PD capability `pd` with `rights` — a validated round-trip
    /// over the firmament Endpoint (the confined child's control socket).
    ///
    /// First the unified `granted ⊆ held` gate (`is_attenuation`) checks the op's
    /// requested authority against the held rights — the SAME lattice as every
    /// other backing. Then the invocation reaches the child over the existing
    /// socketpair wire (a [`crate::process_kernel::KernelRequest::Validate`]
    /// probe in Phase 0 — the minimal "the Endpoint is live and authorized"
    /// resolution). The bounds are strong-local (`n = 1`).
    #[cfg(all(feature = "process-pd", unix))]
    pub fn invoke(&self, pd: HostPdId, rights: &Rights) -> Result<Resolution, ResolveError> {
        use dregg_cell::is_attenuation;

        let entry = self.entries.get(&pd).ok_or(ResolveError::TargetNotFound)?;
        // The op's required authority must be within the held cap's authority —
        // the SAME `granted ⊆ held` gate the local Mint + distributed delegate
        // use. Never reinvented.
        if !is_attenuation(&entry.rights, rights) {
            return Err(ResolveError::Unauthorized(format!(
                "host-PD cap-rights check: requested {:?} exceeds held {:?} on pd {:?}",
                rights, entry.rights, pd
            )));
        }
        // The firmament Endpoint must be LIVE — holding this `sock` IS holding
        // the cap; if the confined child closed it (exited) the cap is dead. We
        // confirm the Endpoint is still connected before resolving (a peer-addr
        // probe on the held socket — no payload, just "the channel exists").
        // This makes the held Endpoint load-bearing: drop it and the cap is gone.
        if entry.sock.peer_addr().is_err() {
            return Err(ResolveError::BackingRejected(format!(
                "host-PD {:?} Endpoint is closed — the confined child is gone",
                pd
            )));
        }
        Ok(Resolution {
            backing: Backing::HostPdEndpoint,
            bounds: Bounds::LOCAL,
            note: format!(
                "firmament Endpoint live to confined host-PD {:?} rights={:?}",
                pd, entry.rights
            ),
        })
    }

    /// The non-`process-pd` stub: with no live wire there are no registered
    /// host-PDs, so any host-PD invocation resolves to `TargetNotFound`. The
    /// variant still exists; only the live endpoint is feature-gated.
    #[cfg(not(all(feature = "process-pd", unix)))]
    pub fn invoke(&self, _pd: HostPdId, _rights: &Rights) -> Result<Resolution, ResolveError> {
        Err(ResolveError::TargetNotFound)
    }
}
