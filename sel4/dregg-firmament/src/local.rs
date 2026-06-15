//! The LOCAL backing — an seL4 kernel object resolved by a syscall.
//!
//! In `FIRMAMENT.md §3` the local end of the gradation is an seL4 kernel
//! object (a CNode slot / endpoint / frame). The invocation is a kernel
//! syscall; attenuation is `seL4_CNode_Mint` with reduced rights; revocation
//! is `seL4_CNode_Revoke` (synchronous — the cap is dead the instant the
//! syscall returns). These are the strong `n = 1` bounds.
//!
//! This module models the seL4 **syscall boundary** faithfully:
//!
//! - On a real PD, [`LocalBacking::invoke`] is a `seL4_Call` on the slot's
//!   `seL4_CPtr`, [`LocalBacking::mint`] is `seL4_CNode_Mint`, and
//!   [`LocalBacking::revoke`] is `seL4_CNode_Revoke`. The cap-rights check is
//!   the kernel's.
//! - On the HOST (where this test runs), the backing is a faithful stub: a
//!   slot table standing in for the CNode, where `mint` derives a reduced-
//!   rights child slot and `revoke` synchronously removes the slot + its
//!   derivations. The rights are the REAL dregg [`AuthRequired`], and the
//!   `mint` reduced-rights derivation gates on the REAL [`is_attenuation`] —
//!   so the local Mint and the distributed delegate enforce the IDENTICAL
//!   `granted ⊆ held` law.
//!
//! The shape (slot table, mint-with-attenuation, synchronous revoke) is what a
//! real PD's CNode operations have; only the syscall-vs-table mechanism
//! differs, and the app never sees it.

use std::collections::BTreeMap;
use std::string::String;

use dregg_cell::is_attenuation;

use crate::{Backing, Bounds, Resolution, ResolveError, Rights};

/// One slot in the (modeled) CNode — a kernel object the PD holds a cap to.
#[derive(Clone, Debug)]
struct Slot {
    /// The rights the holder has over this object (the seL4 cap rights,
    /// modeled as the REAL dregg [`AuthRequired`] so local and distributed
    /// share one lattice).
    rights: Rights,
    /// A label for the underlying kernel object (an endpoint name, a frame
    /// paddr, …) — what the syscall would actually touch.
    object: String,
    /// The parent slot this was minted from (`seL4_CNode_Mint` records the
    /// derivation tree). `None` = an original cap. A `revoke` of the parent
    /// removes all descendants — synchronous, immediate.
    minted_from: Option<u32>,
}

/// The local backing: a CNode slot table standing in for the seL4 kernel's
/// cap space, with `mint` / `revoke` / `invoke` modeling the syscall boundary.
#[derive(Clone, Debug, Default)]
pub struct LocalBacking {
    slots: BTreeMap<u32, Slot>,
    next_slot: u32,
}

impl LocalBacking {
    /// A fresh, empty CNode.
    pub fn new() -> Self {
        LocalBacking {
            slots: BTreeMap::new(),
            next_slot: 0,
        }
    }

    /// Install an ORIGINAL capability over a kernel object at the next free
    /// slot, returning the slot index. On a real PD this is the cap the
    /// firmament minted into the app-PD's CNode at boot (CapDL init).
    pub fn install(&mut self, object: impl Into<String>, rights: Rights) -> u32 {
        let slot = self.next_slot;
        self.next_slot += 1;
        self.slots.insert(
            slot,
            Slot {
                rights,
                object: object.into(),
                minted_from: None,
            },
        );
        slot
    }

    /// Resolve (invoke) the capability at `slot` with `rights`.
    ///
    /// Models `seL4_Call` on the slot's `seL4_CPtr`: the kernel checks the
    /// invocation against the cap's rights, then performs the operation. Here
    /// we check the requested `rights` against the held rights via the REAL
    /// [`is_attenuation`] (the requested op must be `⊆` the held authority —
    /// the same direction the kernel's rights check enforces), then "perform"
    /// it by returning a [`Resolution`] with the strong `n = 1` bounds.
    pub fn invoke(&self, slot: u32, rights: &Rights) -> Result<Resolution, ResolveError> {
        let s = self.slots.get(&slot).ok_or(ResolveError::TargetNotFound)?;
        // The op's required authority must be within the held cap's authority.
        if !is_attenuation(&s.rights, rights) {
            return Err(ResolveError::Unauthorized(format!(
                "seL4 cap-rights check: requested {:?} exceeds held {:?} on slot {}",
                rights, s.rights, slot
            )));
        }
        Ok(Resolution {
            backing: Backing::LocalKernel,
            bounds: Bounds::LOCAL,
            note: format!(
                "seL4_Call slot={} object={} rights={:?}",
                slot, s.object, s.rights
            ),
        })
    }

    /// `seL4_CNode_Mint` with reduced rights — the LOCAL attenuation primitive.
    ///
    /// Derives a CHILD cap at a new slot pointing at the SAME object with
    /// `narrower` rights. The kernel enforces that a mint cannot amplify; here
    /// we enforce the IDENTICAL law via the REAL [`is_attenuation`]
    /// (`narrower ⊆ held`). Returns the new child slot, or `None` if the mint
    /// would widen (rejected exactly as `seL4_CNode_Mint` rejects an
    /// over-broad rights mask).
    pub fn mint(&mut self, parent: u32, narrower: Rights) -> Option<u32> {
        let p = self.slots.get(&parent)?;
        if !is_attenuation(&p.rights, &narrower) {
            return None; // amplifying mint — refused, the `granted ⊆ held` law
        }
        let object = p.object.clone();
        let slot = self.next_slot;
        self.next_slot += 1;
        self.slots.insert(
            slot,
            Slot {
                rights: narrower,
                object,
                minted_from: Some(parent),
            },
        );
        Some(slot)
    }

    /// `seL4_CNode_Revoke` — synchronous, immediate revocation (`n = 1`).
    ///
    /// Removes the slot AND every cap minted (transitively) from it — the
    /// kernel's derivation-tree revoke. The cap is dead the instant this
    /// returns: there is no in-flight window, no epoch to propagate. Returns
    /// the number of slots removed.
    pub fn revoke(&mut self, slot: u32) -> usize {
        // Collect the slot + its transitive mint-descendants.
        let mut doomed = vec![slot];
        let mut i = 0;
        while i < doomed.len() {
            let parent = doomed[i];
            for (&s, sl) in self.slots.iter() {
                if sl.minted_from == Some(parent) && !doomed.contains(&s) {
                    doomed.push(s);
                }
            }
            i += 1;
        }
        let mut removed = 0;
        for s in doomed {
            if self.slots.remove(&s).is_some() {
                removed += 1;
            }
        }
        removed
    }

    /// Does a live cap exist at `slot`? (Post-revoke, this is `false`
    /// immediately — the `n = 1` immediacy.)
    pub fn is_live(&self, slot: u32) -> bool {
        self.slots.contains_key(&slot)
    }

    /// The rights held at `slot`, if any.
    pub fn rights_at(&self, slot: u32) -> Option<Rights> {
        self.slots.get(&slot).map(|s| s.rights.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::AuthRequired;

    #[test]
    fn mint_attenuates_and_refuses_amplification() {
        let mut cnode = LocalBacking::new();
        let root = cnode.install("endpoint:ctrl", AuthRequired::Either);

        // Mint a narrower child — succeeds (Either -> Signature).
        let child = cnode
            .mint(root, AuthRequired::Signature)
            .expect("narrowing mint");
        assert_eq!(cnode.rights_at(child), Some(AuthRequired::Signature));

        // Mint a WIDER child off the narrowed one — refused (the `granted ⊆
        // held` law, enforced by the SAME `is_attenuation`).
        assert!(cnode.mint(child, AuthRequired::Either).is_none());
    }

    #[test]
    fn revoke_is_synchronous_and_transitive() {
        let mut cnode = LocalBacking::new();
        let root = cnode.install("endpoint:ctrl", AuthRequired::Either);
        let child = cnode.mint(root, AuthRequired::Signature).unwrap();
        let grandchild = cnode.mint(child, AuthRequired::Signature).unwrap();

        // Revoking the root kills the whole derivation subtree, immediately.
        let removed = cnode.revoke(root);
        assert_eq!(removed, 3);
        assert!(!cnode.is_live(root));
        assert!(!cnode.is_live(child));
        assert!(!cnode.is_live(grandchild));
        // n = 1: no in-flight window — the cap is dead the instant revoke returns.
    }

    #[test]
    fn invoke_checks_rights() {
        let mut cnode = LocalBacking::new();
        let slot = cnode.install("frame:0x4000", AuthRequired::Either);
        // Invoking with the SAME authority you hold succeeds.
        assert!(cnode.invoke(slot, &AuthRequired::Either).is_ok());
        // Invoking requiring only a NARROWER authority (Signature ⊆ Either) is
        // within the held cap — succeeds.
        assert!(cnode.invoke(slot, &AuthRequired::Signature).is_ok());
        // Requiring a BROADER authority than held is refused: hold Signature,
        // require None (None is the top of the lattice — the broadest).
        let narrow = cnode.install("frame:narrow", AuthRequired::Signature);
        assert!(cnode.invoke(narrow, &AuthRequired::None).is_err());
        // A requirement the held cap cannot meet: hold Impossible, require Signature.
        let locked = cnode.install("frame:locked", AuthRequired::Impossible);
        assert!(cnode.invoke(locked, &AuthRequired::Signature).is_err());
    }
}
