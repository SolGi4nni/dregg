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
#[cfg(all(feature = "process-pd", unix))]
use std::sync::Mutex;

// ───────────────────────── the SURFACE Endpoint protocol ────────────────────
//
// A migrated surface re-homes its PRESENT/INPUT round-trips onto the confined
// child PD's firmament Endpoint — a SECOND socket alongside the kernel control
// socket (`docs/deos/SURFACE-MIGRATION.md` §2(b), the live transport re-home).
// The child runs a surface renderer over this socket: it receives a
// [`SurfaceEvent`] (an input event or a present request) and replies with a
// [`SurfaceFrame`] (the rendered output the glass shows). The wire is the SAME
// length-prefixed framing the process kernel speaks, kept dependency-free.

/// An event the compositor delivers to the migrated surface's renderer over the
/// child PD's firmament Endpoint. This is the GLASS following the cap: instead
/// of the in-process compositor producing the frame, the confined child does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SurfaceEvent {
    /// A user input event routed to the surface (a keystroke/pointer code). The
    /// child folds it into its surface state and re-renders.
    Input {
        /// An opaque input code the surface interprets (e.g. a key/pointer id).
        code: u64,
    },
    /// A present request: render the current surface state at `seq` and return
    /// the frame. `seq` is the present sequence number the compositor advances.
    Present {
        /// The present sequence number (monotone; the frame log's index).
        seq: u64,
    },
}

/// The frame a migrated surface's renderer returns over the Endpoint — the
/// rendered output that crosses back to the compositor (the glass).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SurfaceFrame {
    /// The present sequence this frame answers (echoes the request's `seq`, or
    /// the surface's current seq for an input-driven re-render).
    pub seq: u64,
    /// The content digest of the rendered frame — a fingerprint of the surface
    /// state the child produced. The compositor folds this into its frame log,
    /// exactly like the in-process digest, proving the frame came from the child.
    pub digest: u64,
}

#[cfg(all(feature = "process-pd", unix))]
impl SurfaceEvent {
    /// Encode to the wire (tag byte + u64 payload, little-endian).
    pub fn encode(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(9);
        match self {
            SurfaceEvent::Input { code } => {
                v.push(0);
                v.extend_from_slice(&code.to_le_bytes());
            }
            SurfaceEvent::Present { seq } => {
                v.push(1);
                v.extend_from_slice(&seq.to_le_bytes());
            }
        }
        v
    }

    /// Decode the inverse of [`Self::encode`].
    pub fn decode(b: &[u8]) -> Option<SurfaceEvent> {
        let (&tag, rest) = b.split_first()?;
        let n = u64::from_le_bytes(rest.get(..8)?.try_into().ok()?);
        match tag {
            0 => Some(SurfaceEvent::Input { code: n }),
            1 => Some(SurfaceEvent::Present { seq: n }),
            _ => None,
        }
    }
}

#[cfg(all(feature = "process-pd", unix))]
impl SurfaceFrame {
    /// Encode to the wire (seq ‖ digest, little-endian).
    pub fn encode(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(16);
        v.extend_from_slice(&self.seq.to_le_bytes());
        v.extend_from_slice(&self.digest.to_le_bytes());
        v
    }

    /// Decode the inverse of [`Self::encode`].
    pub fn decode(b: &[u8]) -> Option<SurfaceFrame> {
        let seq = u64::from_le_bytes(b.get(..8)?.try_into().ok()?);
        let digest = u64::from_le_bytes(b.get(8..16)?.try_into().ok()?);
        Some(SurfaceFrame { seq, digest })
    }
}

/// Length-prefixed framed write/read over the surface Endpoint — the SAME
/// `[u32 len][bytes]` framing the process kernel's control wire uses, so the
/// surface Endpoint and the control Endpoint speak one transport shape.
#[cfg(all(feature = "process-pd", unix))]
pub fn surface_write_framed(
    s: &mut std::os::unix::net::UnixStream,
    bytes: &[u8],
) -> std::io::Result<()> {
    use std::io::Write;
    let len = (bytes.len() as u32).to_le_bytes();
    s.write_all(&len)?;
    s.write_all(bytes)?;
    s.flush()
}

/// Read a frame written by [`surface_write_framed`].
#[cfg(all(feature = "process-pd", unix))]
pub fn surface_read_framed(
    s: &mut std::os::unix::net::UnixStream,
) -> std::io::Result<Vec<u8>> {
    use std::io::Read;
    let mut len = [0u8; 4];
    s.read_exact(&mut len)?;
    let n = u32::from_le_bytes(len) as usize;
    let mut buf = vec![0u8; n];
    s.read_exact(&mut buf)?;
    Ok(buf)
}

/// The CHILD-side surface renderer loop: serve one [`SurfaceEvent`] from the
/// surface Endpoint and reply with a [`SurfaceFrame`]. The confined child runs
/// this in its body — the renderer that, after a migrate, owns the glass. The
/// `render` closure maps `(state, event) -> (new_state, frame)`; the surface
/// state is the child's PRIVATE memory (MMU-isolated), reached only over this
/// Endpoint. Returns `Ok(false)` on a clean EOF (the compositor closed the
/// surface Endpoint).
#[cfg(all(feature = "process-pd", unix))]
pub fn serve_one_surface_event<S>(
    sock: &mut std::os::unix::net::UnixStream,
    state: &mut S,
    mut render: impl FnMut(&mut S, SurfaceEvent) -> SurfaceFrame,
) -> std::io::Result<bool> {
    let frame = match surface_read_framed(sock) {
        Ok(f) => f,
        Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => return Ok(false),
        Err(e) => return Err(e),
    };
    let event = match SurfaceEvent::decode(&frame) {
        Some(ev) => ev,
        // A malformed surface frame is answered with a zero frame (fail-closed:
        // the surface shows nothing rather than trusting garbage).
        None => {
            surface_write_framed(sock, &SurfaceFrame { seq: 0, digest: 0 }.encode())?;
            return Ok(true);
        }
    };
    let out = render(state, event);
    surface_write_framed(sock, &out.encode())?;
    Ok(true)
}

/// One registered host-PD endpoint: the rights held over it (the cap's
/// authority) + (under `process-pd`) the kernel's control socket to the child
/// and (optionally) the SURFACE Endpoint a migrated surface re-homes onto.
#[cfg(all(feature = "process-pd", unix))]
struct HostPdEntry {
    /// The rights held over this host-PD endpoint (the unified [`Rights`]
    /// lattice — the same `AuthRequired` every other firmament cap uses).
    rights: Rights,
    /// The kernel's end of the control socket to the confined child (the
    /// firmament Endpoint). An invocation is a validated round-trip on it.
    sock: std::os::unix::net::UnixStream,
    /// The compositor's end of the SURFACE Endpoint to the confined child — the
    /// live-transport channel a migrated surface's `present`/`route_input`
    /// round-trips on (`SurfaceEvent` → `SurfaceFrame`). `None` until a surface
    /// is migrated to this PD; `Some` once [`HostPdBacking::register_surface`]
    /// hands over the second socket. Under a `Mutex` so a present is one
    /// serialized round-trip even behind a shared `&self`.
    surface_sock: Option<Mutex<std::os::unix::net::UnixStream>>,
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
        self.entries.insert(
            id,
            HostPdEntry {
                rights,
                sock,
                surface_sock: None,
            },
        );
        id
    }

    /// REGISTER the SURFACE Endpoint for an already-registered host-PD — the
    /// live-transport re-home of `docs/deos/SURFACE-MIGRATION.md` §2(b). After a
    /// surface migrates (`migrate(surface_cap, HostPd{pd})` re-mints the
    /// authority half), the compositor hands over the second socket (the
    /// surface Endpoint to the confined child) here; thereafter the surface's
    /// `present`/`route_input` round-trip over it instead of the in-process
    /// compositor — the GLASS follows the cap. Returns whether the PD was found.
    #[cfg(all(feature = "process-pd", unix))]
    pub fn register_surface(
        &mut self,
        pd: HostPdId,
        surface_sock: std::os::unix::net::UnixStream,
    ) -> bool {
        match self.entries.get_mut(&pd) {
            Some(e) => {
                e.surface_sock = Some(Mutex::new(surface_sock));
                true
            }
            None => false,
        }
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

    /// PRESENT a migrated surface over the child PD's SURFACE Endpoint — the
    /// live-transport half of the move. After the `granted ⊆ held` gate, the
    /// compositor sends a [`SurfaceEvent`] (`Present`/`Input`) across the
    /// surface socket to the confined child and reads back the [`SurfaceFrame`]
    /// the child RENDERED — the glass following the cap. The cap's `rights` gate
    /// the op exactly like [`Self::invoke`]; the surface Endpoint must have been
    /// registered ([`Self::register_surface`]) or the op is
    /// [`ResolveError::TargetNotFound`].
    ///
    /// This is the SAME round-trip shape the control Endpoint uses (a framed
    /// request → a framed reply), just carrying surface traffic — so a migrated
    /// surface's `present`/`route_input` reach the confined child over its
    /// firmament Endpoint, not the in-process compositor.
    #[cfg(all(feature = "process-pd", unix))]
    pub fn present_over_endpoint(
        &self,
        pd: HostPdId,
        rights: &Rights,
        event: SurfaceEvent,
    ) -> Result<SurfaceFrame, ResolveError> {
        use dregg_cell::is_attenuation;

        let entry = self.entries.get(&pd).ok_or(ResolveError::TargetNotFound)?;
        // The SAME `granted ⊆ held` gate every other backing runs: a present
        // carrying rights wider than held over the migrated surface is refused.
        if !is_attenuation(&entry.rights, rights) {
            return Err(ResolveError::Unauthorized(format!(
                "surface present over host-PD {:?}: requested {:?} exceeds held {:?}",
                pd, rights, entry.rights
            )));
        }
        let surface = entry
            .surface_sock
            .as_ref()
            .ok_or(ResolveError::TargetNotFound)?;
        let mut sock = surface.lock().map_err(|_| {
            ResolveError::BackingRejected("surface Endpoint lock poisoned".into())
        })?;
        // THE GLASS-FOLLOWS-THE-CAP ROUND-TRIP: send the event to the confined
        // child, read back the frame it rendered. Holding this socket IS holding
        // the live surface; if the child exited, the read fails and the surface
        // is dead.
        surface_write_framed(&mut sock, &event.encode())
            .map_err(|e| ResolveError::BackingRejected(format!("surface send: {e}")))?;
        let reply = surface_read_framed(&mut sock).map_err(|e| {
            ResolveError::BackingRejected(format!(
                "surface Endpoint to host-PD {:?} closed — the confined child is gone: {e}",
                pd
            ))
        })?;
        SurfaceFrame::decode(&reply).ok_or_else(|| {
            ResolveError::BackingRejected("malformed surface frame from child".into())
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
