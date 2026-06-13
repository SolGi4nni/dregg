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

use std::string::String;

pub mod local;
pub mod distributed;
pub mod router;

pub use local::LocalBacking;
pub use distributed::DistributedBacking;
pub use router::{FirmamentRouter, Router};

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

    /// Is this target local (resolves via the kernel/stub path)?
    pub fn is_local(&self) -> bool {
        matches!(self, Target::Local { .. })
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
        Capability { target: Target::local(slot), rights }
    }

    /// Mint a handle to a DISTRIBUTED dregg cell with `rights`.
    pub fn distributed(cell: CellId, rights: Rights) -> Self {
        Capability { target: Target::distributed(cell), rights }
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
        Some(Capability { target: self.target.clone(), rights: narrower })
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
    pub const LOCAL: Bounds = Bounds { revocation_immediate: true, commit_synchronous: true, n: 1 };

    /// The relaxed `n > 1` bounds: eventual revocation, quorum commit — what a
    /// distributed target over the net-PD edge gets once it reaches the wire.
    pub fn distributed(n: u32) -> Bounds {
        if n <= 1 {
            // A distributed target that happens to be on THIS machine collapses
            // to the strong local bounds — the `n = 1` collapse, exactly.
            Bounds::LOCAL
        } else {
            Bounds { revocation_immediate: false, commit_synchronous: false, n }
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
