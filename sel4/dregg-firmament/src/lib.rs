//! # dregg-firmament — the cap-gradation bridge (the fluid reach-out, in code)
//!
//! `docs/FIRMAMENT.md §3` makes the firmament's central claim: **an seL4
//! capability and a dregg capability are the same abstraction at different
//! points on a distance parameter.** Both are unforgeable, attenuable,
//! delegable references to a resource; they differ only in *how far away* the
//! resource is and *what bounds hold on operations against it*.
//!
//! This crate turns that design into CODE. The app holds ONE
//! [`Capability`] handle — a `(target, rights)` pair — and invokes /
//! attenuates / delegates it with the SAME verbs regardless of whether the
//! target is:
//!
//! - **local** — an seL4 kernel object (a CNode slot / endpoint). The
//!   invocation is a kernel syscall; attenuation is `seL4_CNode_Mint` with
//!   reduced rights; revocation is `seL4_CNode_Revoke` (synchronous, immediate).
//!   Modeled by [`local::LocalBacking`] (a faithful host stub of the syscall
//!   boundary; on a real PD the same shape calls the Microkit IPC primitives).
//!
//! - **distributed** — a dregg cell on a (possibly remote) federation. The
//!   invocation is a real turn through the executor; attenuation is the real
//!   `recKDelegateAtten` gate (`granted ⊆ held`); revocation is the group-key
//!   epoch lift. Modeled by [`distributed::DistributedBacking`], which runs a
//!   GENUINE [`dregg_turn::TurnExecutor`] turn against a real
//!   [`dregg_cell::Ledger`].
//!
//! **The app does not see which backing it holds.** It holds a [`Capability`];
//! it invokes it; the [`Router`] resolves it to the kernel (local) or the
//! executor→net path (distributed). **Adoption is attenuation** at both ends,
//! and the rights lattice is the SAME [`dregg_cell::AuthRequired`] — the local
//! Mint and the distributed delegate BOTH gate on the real
//! [`dregg_cell::is_attenuation`] (`granted ⊆ held`). We never reinvent the
//! attenuation check.
//!
//! ## The `n = 1` collapse
//!
//! The distance parameter `n` is the number of machines the target is spread
//! across. On the firmament `n = 1` (everything is on one seL4 box), so the
//! distributed bounds collapse to strong local properties (§3 table):
//! revocation is *immediate*, commit is *synchronous*, checkpoint is
//! *consistent*. This crate exposes that as [`Bounds`]: a [`Resolution`]
//! carries the bounds that held for the op, so the SAME handle resolving
//! local-vs-distributed differs ONLY in the relaxed bounds, never in the verbs.
//!
//! That is the fluid reach-out: first-class locally (the strong `n = 1`
//! properties), seamless to the wire (the bounds simply relax as `n` rises).
//!
//! ## The semihost ([`EmulatedKernel`] + the [`microkit_facade`])
//!
//! `docs/DREGG-DESKTOP-OS.md §3` (the semihosted-seL4 KEYSTONE) makes the local
//! leg *runnable on your mac/linux today*: the [`EmulatedKernel`] PROMOTES
//! [`LocalBacking`]'s CNode slot-table with the three seL4 IPC primitives (a
//! synchronous Endpoint, a badge-OR Notification, Untyped+Retype), and the
//! [`microkit_facade`] ships the `sel4-microkit`-shaped API (a
//! `#[protection_domain]`-style entry, [`Handler`], [`Channel`], [`MessageInfo`],
//! [`memory_region_symbol!`]) the dregg PDs code against — std-backed (semihost)
//! now, real seL4 later, **the same PD source on both**. It is a faithful
//! `n = 1` firmament (a host thread's revoke IS synchronous; the cap checks are
//! the genuine [`is_attenuation`]).
//!
//! ### Two backings, cfg-selected (the v0 isolation gap is CLOSED)
//!
//! The semihost has TWO cfg-selected backings under ONE facade:
//!
//! - **v0 — thread-backed** ([`EmulatedKernel`], the default): PDs are host
//!   threads in one address space. Fast (no `fork`), ideal for `cargo test`. It
//!   carries ONE honestly-labeled non-fidelity: "no ambient authority" is
//!   by-construction-in-the-API, NOT MMU-enforced (a malicious thread could read
//!   another PD's memory; raw RAM has no tag bits to stop cap forgery). See
//!   [`EmulatedKernel::ISOLATION_FIDELITY`].
//! - **v1 — process-backed** ([`process_kernel::ProcessKernel`], `--features
//!   process-pd`, Unix): PDs are forked PROCESSES, so the host **MMU enforces**
//!   address-space separation — a PD physically cannot read another PD's private
//!   memory. Shared regions are `shm_open`/`mmap` segments granted by name; and
//!   an epoch-tagged cap-handle **validity table** (the kernel's, the
//!   cross-process CNode-unforgeability analogue) refuses a cap forged from raw
//!   bytes. This **closes** the v0 gap; what remains trusted is stated honestly
//!   (the table is the kernel's TCB; the MMU is the host OS's). See
//!   [`process_kernel::ProcessKernel::ISOLATION_FIDELITY`].
//!
//! **The PD source is UNCHANGED across both** — only the backing moves
//! thread→process. The boot test (m0-hello + the 2-PD notify slice) runs on
//! both, and the v1 path adds the isolation tooth v0 lacked (a PD CANNOT read
//! another PD's memory NOR forge a cap by writing raw bytes, while IPC still
//! works). `docs/DREGG-DESKTOP-OS.md §3`.

use std::string::String;

pub mod distributed;
pub mod emulated_kernel;
pub mod host_pd;
pub mod local;
pub mod microkit_facade;
pub mod router;
pub mod surface;

// The HOUYHNHNM RECOVERY MONITOR — an external, simple-but-complete watcher that
// reads the LIVE ARTIFACT (a host-PD's Endpoint round-trip, never a self-reported
// "OK"), detects claimed-vs-actual divergence (`RecoveryNotHolding` — the council's
// exact signal), guards the restart loop with an attempt counter (escalates rather
// than looping forever), and can stop/inspect/restart a wedged subsystem
// fail-closed. Recursive: a monitor is itself a `Subsystem`, so monitors watch
// monitors (`docs/deos/HOUYHNHNM-CONVERGENCE.md`, fare's Houyhnhnm ch3/ch6). It
// depends only on the public host-PD/Endpoint probe surface; the mock-driven tests
// run in the default feature set (no `process-pd`), and the real `HostPdSubsystem`
// adapter (the genuine live-Endpoint probe) is gated on `process-pd`.
pub mod recovery_monitor;

// The COMPOSITOR-PD — the minimal framebuffer/input multiplexer on the
// EmulatedKernel (`docs/DREGG-DESKTOP-OS.md §2 L5` + `§6 R3 Stage D`, native-now
// on the semihost). It is the SOLE holder of the framebuffer region, models its
// scene as a dregg cell, and enforces the verified scene (T1 non-overlap / T2
// label-binding / T3 focus-exclusivity — the anti-ghost teeth PROVEN in the Lean
// `Dregg2.Apps.Compositor` AppSpec) AS THE GATE on every `present()` an app-PD
// submits over an Endpoint. The ONLY new TCB; NO app logic, NO widget toolkit,
// NO placement policy. std-backed (semihost); the scene authority is the genuine
// `is_attenuation` (`granted ⊆ held`) lattice, never reinvented.
pub mod compositor_pd;

// The EXECUTOR-PD — the firmament HEART on the semihost (`docs/FIRMAMENT.md §2`
// L3, `docs/DREGG-DESKTOP-OS.md §3` the KEYSTONE payoff: "the verified
// executor-PD hosts on the host's ordinary Lean runtime NOW"). It is the
// Endpoint SERVER for staged turns: an app-PD stages a turn into `turn_in`,
// signals the executor over its PP channel, and the executor runs it through a
// `TurnRunner` (on the semihost the cockpit's REAL `dregg_sdk::embed::DreggEngine`
// — the verified `TurnExecutor` over a `dregg_cell::Ledger`), writes the receipt
// into `commit_out`, and replies. It holds NO device cap — pure compute over
// bytes (the executor's exact `§2` cap partition: turn_in R, commit_out RW). It
// rides the EXISTING `EmulatedKernel` IPC (Endpoint recv/reply + regions), the
// SAME primitives the compositor-PD uses; NO executor logic of its own. This is
// the executor-stub seat's verified-turn path RUNNING (the real-seL4 PD idles it
// until the Lean ELF runtime links — WALL step 4, NOT a blocker on the semihost).
pub mod executor_pd;

// The v1 PROCESS-backed PD substrate (the MMU-enforced isolation upgrade). It
// is Unix-only and behind the `process-pd` feature: PDs become forked host
// PROCESSES so the host MMU enforces address-space separation, shared regions
// become `shm_open`/`mmap`, and a kernel-side epoch-tagged validity table
// refuses raw-bytes cap forgery. This CLOSES the one honestly-labeled v0
// non-fidelity ([`EmulatedKernel::ISOLATION_FIDELITY`]). It EXTENDS the
// emulator with a cfg-selected backing — the v0 thread kernel stays the default
// for fast `cargo test`; see `docs/DREGG-DESKTOP-OS.md §3`.
#[cfg(all(feature = "process-pd", unix))]
pub mod process_kernel;

// The OS-SANDBOX confinement (Phase-0 of the cross-platform sandboxed
// firmament). It closes the ambient-authority gap the process backing's MMU
// isolation leaves open: a forked child PD, right after `fork()` and before its
// body runs, closes every non-granted fd and drops ambient OS authority (macOS
// Seatbelt / Linux namespaces+seccomp+Landlock), so its ONLY channel is the
// firmament Endpoint. Unix-only, behind `process-pd-sandbox` (implies
// `process-pd`); see `docs/DREGG-DESKTOP-OS.md §3`.
#[cfg(all(feature = "process-pd-sandbox", unix))]
pub mod sandbox;

pub use compositor_pd::{
    cell_seed, decode_present, encode_present, label_of, CompositorPd, FrameCommit, Present,
    Refusal, RegionId, Scene, Surface, FRAMEBUFFER_TILES, LABEL_PRESENT, LABEL_PRESENT_OK,
    LABEL_PRESENT_REFUSED,
};
pub use distributed::DistributedBacking;
pub use host_pd::{HostPdBacking, SurfaceEvent, SurfaceFrame};
#[cfg(all(feature = "process-pd", unix))]
pub use host_pd::{serve_one_surface_event, surface_read_framed, surface_write_framed};
pub use emulated_kernel::{
    EmulatedKernel, IpcError, Message, NotifyCap, ObjectId, ObjectType, ReplyToken, RetypeError,
};
pub use executor_pd::{
    stage_turn_into, ExecutorPd, ServedTurn, TurnRunner, LABEL_RUN_TURN, LABEL_TURN_COMMITTED,
    LABEL_TURN_REJECTED,
};
pub use local::LocalBacking;
pub use recovery_monitor::{
    ActualState, Claim, Divergence, Escalation, MonitorPolicy, MonitorSubsystem, RecoveryMonitor,
    Subsystem, Verdict,
};
#[cfg(all(feature = "process-pd", unix))]
pub use recovery_monitor::HostPdSubsystem;
pub use microkit_facade::{
    Channel, ChannelSet, ChannelTable, ChannelWiring, EventLoop, Handler, MessageInfo, NullHandler,
    ProtectionDomain, Region,
};
pub use router::{FirmamentRouter, Router};
pub use surface::SurfaceBacking;

// The v1 process-backed substrate's public surface (Unix + `process-pd` only):
// the forking kernel, the unforgeable cap-handle + its validity table, the
// `shm_open`/`mmap` region, and the PD-side client.
#[cfg(all(feature = "process-pd", unix))]
pub use process_kernel::{
    CapError, CapHandle, CapObject, ForgeReason, KernelClient, KernelReply, KernelRequest,
    ObjectKind, PdProcess, ProcessKernel, ShmRegion, SpawnError, ValidityTable,
};

// The Phase-0 sandbox confinement surface (Unix + `process-pd-sandbox`).
#[cfg(all(feature = "process-pd-sandbox", unix))]
pub use sandbox::{confine_child, ConfineError, Confinement};
#[cfg(all(feature = "process-pd-sandbox", unix))]
pub use process_kernel::CONFINE_FAILED_EXIT;

// Re-export the REAL dregg rights lattice and id so app code names the genuine
// types, not a parallel model.
pub use dregg_cell::{is_attenuation, AuthRequired};
pub use dregg_types::CellId;

/// The rights carried by a firmament capability.
///
/// This is the REAL dregg [`AuthRequired`] lattice — not a parallel model. A
/// local seL4 cap and a distributed dregg cap attenuate against the SAME
/// order (`is_attenuation` / `AuthRequired::is_narrower_or_equal`), which is
/// the whole point: one rights model, two backings.
pub type Rights = AuthRequired;

/// The identity of a host PROCESS-backed PD (a confined forked child) — the
/// addressee of a [`Target::HostPd`] capability.
///
/// On the v1 process backing a PD is a forked, OS-sandboxed child whose only
/// channel is its control [`process_kernel`] socket. A host-PD cap names which
/// such PD it reaches; the router resolves it by invoking that PD over the
/// existing socketpair wire. The id is opaque (a kernel-assigned index), exactly
/// like a [`Target::Local`] slot but for a process-PD rather than a CNode slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HostPdId(pub u64);

/// What a capability points at — the *target*, which determines the distance
/// `n` and therefore the backing the router dispatches to.
///
/// This is the `target` half of the `(target, rights)` handle in
/// `FIRMAMENT.md §3`. The app names a target; it does NOT name a backing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Target {
    /// A LOCAL seL4 kernel object: a slot in a CNode (`n = 1`). The
    /// invocation is a syscall; revocation is synchronous; commit is local.
    Local {
        /// The CNode slot index of the kernel object. On a real PD this is a
        /// `seL4_CPtr`; on the host stub it indexes [`local::LocalBacking`]'s
        /// slot table.
        slot: u32,
    },
    /// A DISTRIBUTED dregg cell on a federation (`n ≥ 1`). The invocation is a
    /// turn through the executor; revocation is the epoch lift; commit is
    /// quorum-gated when `n > 1` (and synchronous when `n = 1`).
    Distributed {
        /// The cell this capability points at — the REAL dregg [`CellId`].
        cell: CellId,
    },
    /// A SURFACE: a dregg cell whose state is rendered as a window — **the
    /// firmament made visual** (`docs/DREGG-DESKTOP-OS.md`). A window IS a
    /// capability over a cell; holding/attenuating/delegating/revoking the
    /// window is exactly holding/attenuating/delegating/revoking that cap,
    /// through the SAME `granted ⊆ held` gate and the SAME real executor as a
    /// [`Target::Distributed`] cell. The invocation is a turn (present/draw);
    /// at `n = 1` (compositor + apps on one box) the bounds collapse to
    /// strong-local — a surface revoke darkens the glass the instant it returns.
    Surface {
        /// The cell that backs this surface — the REAL dregg [`CellId`] whose
        /// state the compositor renders.
        cell: CellId,
    },
    /// A HOST PROCESS-backed PD — a forked, OS-sandboxed child whose ONLY
    /// channel is the firmament Endpoint (the [`process_kernel`] control
    /// socket). This is the SANDBOXED FIRMAMENT target: an invocation is a
    /// validated round-trip over that socket; the child cannot open files /
    /// reach the network / exec, so the Endpoint is the sole authority surface.
    /// Attenuation reuses the same `granted ⊆ held` gate (the kernel's
    /// `ValidityTable`); the bounds are strong-local (`n = 1`, one box). Only a
    /// `HostPdId`, exactly like a [`Target::Local`] slot but for a process-PD.
    HostPd {
        /// Which host process-PD this capability reaches.
        pd: HostPdId,
    },
}

impl Target {
    /// A LOCAL kernel-object target at the given CNode slot.
    pub fn local(slot: u32) -> Self {
        Target::Local { slot }
    }

    /// A DISTRIBUTED dregg-cell target.
    pub fn distributed(cell: CellId) -> Self {
        Target::Distributed { cell }
    }

    /// A SURFACE target — a dregg cell rendered as a window.
    pub fn surface(cell: CellId) -> Self {
        Target::Surface { cell }
    }

    /// A HOST PROCESS-PD target — a confined forked child reached over its
    /// firmament Endpoint (the sandboxed-firmament target).
    pub fn host_pd(pd: HostPdId) -> Self {
        Target::HostPd { pd }
    }

    /// Is this target local (resolves via the kernel/stub path)?
    pub fn is_local(&self) -> bool {
        matches!(self, Target::Local { .. })
    }

    /// Is this target a host process-PD (resolves via the firmament Endpoint /
    /// control-socket path)?
    pub fn is_host_pd(&self) -> bool {
        matches!(self, Target::HostPd { .. })
    }

    /// Is this target a surface (a window — resolves via the executor turn
    /// path, the same as a distributed cell, since a surface IS a cell)?
    pub fn is_surface(&self) -> bool {
        matches!(self, Target::Surface { .. })
    }
}

/// A firmament capability: the unified `(target, rights)` handle.
///
/// This is the ONE handle in `FIRMAMENT.md §3`. An app holds it, invokes it,
/// attenuates it (`rights' ⊆ rights`), or delegates it — with the SAME verbs
/// whether the target is local or distributed. The [`Router`] is what knows
/// which backing to dispatch to; the handle itself is backing-agnostic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Capability {
    /// Which resource this references, and how far away it is.
    pub target: Target,
    /// The rights held over the target — the REAL dregg [`AuthRequired`].
    pub rights: Rights,
}

impl Capability {
    /// Mint a handle to a LOCAL kernel object (a CNode slot) with `rights`.
    pub fn local(slot: u32, rights: Rights) -> Self {
        Capability {
            target: Target::local(slot),
            rights,
        }
    }

    /// Mint a handle to a DISTRIBUTED dregg cell with `rights`.
    pub fn distributed(cell: CellId, rights: Rights) -> Self {
        Capability {
            target: Target::distributed(cell),
            rights,
        }
    }

    /// Mint a handle to a SURFACE (a window backed by a dregg cell) with
    /// `rights`. This is "a window = a `Capability{ target: Surface(cell),
    /// rights }`" made concrete — it attenuates / delegates through the SAME
    /// [`Capability::attenuate`] and router gates as every other handle, with
    /// no special-casing (the surface target rides the generic backing-agnostic
    /// machinery).
    pub fn surface(cell: CellId, rights: Rights) -> Self {
        Capability {
            target: Target::surface(cell),
            rights,
        }
    }

    /// Mint a handle to a HOST PROCESS-PD (a confined forked child reached only
    /// over its firmament Endpoint) with `rights`. Attenuates / delegates
    /// through the SAME [`Capability::attenuate`] and router gates as every
    /// other handle — the sandboxed-firmament target rides the generic
    /// backing-agnostic machinery.
    pub fn host_pd(pd: HostPdId, rights: Rights) -> Self {
        Capability {
            target: Target::host_pd(pd),
            rights,
        }
    }

    /// Attenuate this handle's rights to `narrower` — backing-agnostic.
    ///
    /// **This is the heart of "adoption is attenuation".** It gates on the
    /// REAL [`is_attenuation`] (`granted ⊆ held`) regardless of backing, so a
    /// widening is rejected identically whether the cap is local or
    /// distributed. The router then *enforces* the narrowing at the backing:
    /// `seL4_CNode_Mint`-with-reduced-rights locally, `recKDelegateAtten`
    /// distributedly. Returns `None` if `narrower` is not `⊆` the held rights.
    pub fn attenuate(&self, narrower: Rights) -> Option<Capability> {
        // The SAME check the executor's GrantCapability path runs and the
        // SAME check `seL4_CNode_Mint`'s reduced-rights derivation models:
        // `granted ⊆ held`. Never reinvented.
        if !is_attenuation(&self.rights, &narrower) {
            return None;
        }
        Some(Capability {
            target: self.target.clone(),
            rights: narrower,
        })
    }
}

/// The honest bounds that held for an operation — the `n`-parametrized
/// distance bounds of `FIRMAMENT.md §3`. The SAME handle resolving
/// local-vs-distributed differs ONLY in these bounds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bounds {
    /// `seL4_CNode_Revoke` is synchronous (the cap is dead the instant the
    /// syscall returns) iff this is true. `n = 1` ⇒ immediate; `n > 1` ⇒
    /// eventual (the epoch lift must propagate).
    pub revocation_immediate: bool,
    /// The commit is final the moment the op returns (one local transaction)
    /// iff this is true. `n = 1` ⇒ synchronous; `n > 1` ⇒ quorum-gated.
    pub commit_synchronous: bool,
    /// The distance parameter: the number of machines the target is spread
    /// across. `1` = the firmament's collapsed limit.
    pub n: u32,
}

impl Bounds {
    /// The strong `n = 1` bounds: immediate revocation, synchronous commit —
    /// the firmament's headline guarantees for a local deployment.
    pub const LOCAL: Bounds = Bounds {
        revocation_immediate: true,
        commit_synchronous: true,
        n: 1,
    };

    /// The relaxed `n > 1` bounds: eventual revocation, quorum commit — what a
    /// distributed target over the net-PD edge gets once it reaches the wire.
    pub fn distributed(n: u32) -> Bounds {
        if n <= 1 {
            // A distributed target that happens to be on THIS machine collapses
            // to the strong local bounds — the `n = 1` collapse, exactly.
            Bounds::LOCAL
        } else {
            Bounds {
                revocation_immediate: false,
                commit_synchronous: false,
                n,
            }
        }
    }
}

/// The result of resolving (invoking) a capability through the router.
///
/// It carries both the backing that resolved it and the [`Bounds`] that held —
/// so a test can prove that ONE handle resolved local AND distributed, with
/// the bounds being the only difference.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Resolution {
    /// Which backing resolved the invocation.
    pub backing: Backing,
    /// The bounds that held for the op (the `n`-parametrized distance bounds).
    pub bounds: Bounds,
    /// A short human-readable note about what the backing did (e.g. the
    /// kernel object touched, or the receipt the turn produced).
    pub note: String,
}

/// Which backing resolved an invocation — purely informational (the app does
/// NOT branch on this; the whole point is it cannot tell).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Backing {
    /// Resolved via the seL4 kernel path (CNode/endpoint syscall).
    LocalKernel,
    /// Resolved via the executor→net path (a real dregg turn).
    DistributedTurn,
    /// Resolved via a HOST PROCESS-PD's firmament Endpoint (the sandboxed-
    /// firmament control socket — a validated round-trip to a confined child).
    HostPdEndpoint,
}

/// Errors a router can return when resolving a capability.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolveError {
    /// The target slot/cell was not found in the backing.
    TargetNotFound,
    /// The held rights did not authorize the requested operation (the backing
    /// rejected — `seL4` cap-rights check, or the executor's auth/attenuation
    /// gate). Carries a short reason for the boot/serial log.
    Unauthorized(String),
    /// The backing failed for a backing-specific reason (e.g. the executor
    /// rejected the turn). Carries the backing's own reason string.
    BackingRejected(String),
}

#[cfg(test)]
mod handle_tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    #[test]
    fn attenuate_is_backing_agnostic_and_uses_real_check() {
        // Local and distributed handles attenuate through the SAME real check.
        let loc = Capability::local(3, AuthRequired::Either);
        let dist = Capability::distributed(cid(7), AuthRequired::Either);

        // Either -> Signature is a genuine narrowing (real lattice).
        assert!(loc.attenuate(AuthRequired::Signature).is_some());
        assert!(dist.attenuate(AuthRequired::Signature).is_some());

        // Signature -> Either is a WIDENING; rejected at BOTH backings by the
        // SAME `is_attenuation` gate.
        let loc_s = Capability::local(3, AuthRequired::Signature);
        let dist_s = Capability::distributed(cid(7), AuthRequired::Signature);
        assert!(loc_s.attenuate(AuthRequired::Either).is_none());
        assert!(dist_s.attenuate(AuthRequired::Either).is_none());

        // And the narrowed handle keeps the SAME target — only rights moved.
        let n = loc.attenuate(AuthRequired::Signature).unwrap();
        assert_eq!(n.target, loc.target);
        assert_eq!(n.rights, AuthRequired::Signature);
    }

    #[test]
    fn n_equals_one_collapse() {
        // A distributed target on THIS machine collapses to the strong local
        // bounds — the `n = 1` collapse made concrete.
        assert_eq!(Bounds::distributed(1), Bounds::LOCAL);
        assert!(Bounds::distributed(1).revocation_immediate);
        assert!(Bounds::distributed(1).commit_synchronous);

        // n > 1 relaxes the bounds — but the VERBS are unchanged.
        let far = Bounds::distributed(5);
        assert!(!far.revocation_immediate);
        assert!(!far.commit_synchronous);
        assert_eq!(far.n, 5);
    }
}
