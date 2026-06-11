//! Capability-attenuated agent mandates — the Rust mirror of the verified Lean
//! `Dregg2.Agent.Mandate` (`metatheory/Dregg2/Agent/Mandate.lean`).
//!
//! # What this is
//!
//! A principal (human or agent) grants an **agent** a *mandate*: a capability with attenuation — a
//! `target` it may act on, a rights bound (`keep`), a spend `budget`, and a caveat window — that the
//! agent may SUB-DELEGATE to sub-agents only by STRICT ATTENUATION. The agent fabric is a
//! [`DelegTree`]: a mandate plus its sub-mandate children, each itself a tree.
//!
//! This module is the IN-BAND replacement for the out-of-band sub-agent capability check the SDK's
//! `SubAgent::execute` path (`sdk/src/runtime.rs`) was performing informally. The three tree-level
//! invariants the agent runtime must maintain are now TYPED, CHECKED predicates, byte-for-byte
//! mirroring the Lean theorems they correspond to:
//!
//!   * **No sub-agent amplifies authority** ([`DelegTree::no_amplify`]) ⟷ Lean
//!     `subtree_rights_le_root`. Every descendant mandate's conferred rights ⊆ the root's,
//!     transitively over the genuine permission lattice.
//!
//!   * **Budget is conserved across the tree** ([`DelegTree::budget_bounded`] +
//!     [`DelegTree::budget_partitioned`]) ⟷ Lean `subtree_budget_le_root` +
//!     `children_no_oversubscribe`. Two distinct facets: no descendant out-spends the root (bound),
//!     and no node over-subscribes its budget to its children (conservation — Σ children ≤ parent,
//!     the Stingray slice law).
//!
//!   * **Revocation propagates** ([`materialize_revoke`]) ⟷ Lean `revoke_kills_subtree`. Revoking
//!     the (single, shared) root target severs connectivity for the ENTIRE subtree.
//!
//! # Routing through the verified executor
//!
//! A mandate MATERIALIZES into real executor effects: [`Mandate::materialize_grant`] emits the
//! [`Effect::GrantCapability`] the verified executor runs to install the attenuated cap, and
//! [`materialize_revoke`] emits the [`Effect::RevokeDelegation`] that tears the subtree down. The
//! Lean side proves `materialize = recKDelegateAtten`, which `authorityattenuation.lean` proves IS
//! `execFullA`'s delegate-atten arm — so a granted mandate is a committed kernel delegation checked
//! INLINE, not a side-table. This module produces the EXACT effects that path consumes; the Lean
//! `Mandate.materialize_non_amplifying` / `materialize_grants` theorems are the soundness this
//! mirror inherits.
//!
//! The differential test `tests/agent_mandate_lean_differential.rs` exercises the SAME fixtures the
//! Lean `demoTree_*` non-vacuity theorems use and asserts the Rust predicates agree with the Lean
//! verdicts (`well_attenuated`, `budget_partitioned`, `no_amplify`, `budget_bounded`, the teeth).

use std::collections::BTreeSet;

use dregg_cell::facet::{
    EFFECT_GRANT_CAPABILITY, EFFECT_REVOKE_CAPABILITY, EFFECT_SET_FIELD, EFFECT_TRANSFER,
    EffectMask,
};
use dregg_cell::{AuthRequired, CapabilityRef, CellId};
use dregg_turn::action::Effect;

/// The permission rights an agent may exercise on its target — the Rust mirror of the Lean
/// `Auth` lattice (`Dregg2.Authority.Positional.Auth`). Ordered by SUBSET on the held set
/// (`is_attenuation := granted ⊆ held`); a sub-delegation can only DROP rights.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Auth {
    Read,
    Write,
    Grant,
    Call,
    Reply,
    Reset,
    Control,
}

/// A rights bound: the set of [`Auth`] a mandate confers. `⊆` is the attenuation order
/// (Lean `confRights`/`ExecAuth = Finset Auth`).
pub type Rights = BTreeSet<Auth>;

impl Auth {
    /// The executor facet bit this right corresponds to (`dregg_cell::facet`). The materialized
    /// cap's `allowed_effects` mask is the OR of its rights' bits — so a read-only mandate exposes
    /// only `SetField`, never `Transfer`/`Grant`. Attenuation (`keep' ⊆ keep`) is therefore a
    /// genuine facet-mask narrowing on the wire, the executor's own faceting discipline.
    fn facet_bit(self) -> EffectMask {
        match self {
            Auth::Read => EFFECT_SET_FIELD,
            Auth::Write => EFFECT_TRANSFER,
            Auth::Grant => EFFECT_GRANT_CAPABILITY,
            Auth::Reset => EFFECT_REVOKE_CAPABILITY,
            // call/reply/control are routing/meta rights with no single facet bit; they ride the
            // base SetField facet (the conservative, non-amplifying choice).
            Auth::Call | Auth::Reply | Auth::Control => EFFECT_SET_FIELD,
        }
    }
}

/// The `allowed_effects` facet mask a rights set materializes to: the OR of each right's facet bit.
/// `keep' ⊆ keep ⟹ facet_mask(keep') ⊆ facet_mask(keep)` (bitwise), so the wire mask is
/// non-amplifying exactly when the rights set is.
fn facet_mask(rights: &Rights) -> EffectMask {
    rights.iter().fold(0u32, |acc, r| acc | r.facet_bit())
}

/// A caveat: a runtime restriction the executor evaluates against each action the agent takes.
/// Mirrors Lean `Caveat` — a predicate on the action's method-code, conjoined on sub-delegation
/// (a child is bound by its own AND every ancestor's caveat).
#[derive(Clone)]
pub struct Caveat {
    /// Admit an action whose method-code is `m`?  Boxed so caveats compose by conjunction.
    admits: std::rc::Rc<dyn Fn(u64) -> bool>,
}

impl Caveat {
    /// The always-permissive caveat (Lean `Caveat.any`).
    pub fn any() -> Self {
        Caveat {
            admits: std::rc::Rc::new(|_| true),
        }
    }

    /// A caveat admitting exactly the method-codes in `allowed` (a concrete restriction with teeth).
    pub fn only(allowed: &[u64]) -> Self {
        let set: BTreeSet<u64> = allowed.iter().copied().collect();
        Caveat {
            admits: std::rc::Rc::new(move |m| set.contains(&m)),
        }
    }

    /// Does this caveat admit method-code `m`?
    pub fn admits(&self, m: u64) -> bool {
        (self.admits)(m)
    }

    /// Conjoin two caveats: admit iff BOTH admit (Lean `Caveat.and`). Sub-delegation narrows the
    /// window — the child is the stronger restriction.
    pub fn and(&self, other: &Caveat) -> Caveat {
        let a = self.admits.clone();
        let b = other.admits.clone();
        Caveat {
            admits: std::rc::Rc::new(move |m| a(m) && b(m)),
        }
    }
}

impl std::fmt::Debug for Caveat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Caveat(<fn>)")
    }
}

/// A **mandate**: the agent's attenuated capability bundle (Lean `Mandate`). `holder` may act on
/// `target` with at most the rights in `keep`, spend at most `budget`, and only on actions its
/// `caveat` admits.
#[derive(Clone, Debug)]
pub struct Mandate {
    /// Who granted it (the principal or a parent agent).
    pub grantor: CellId,
    /// The agent that holds it.
    pub holder: CellId,
    /// The resource the mandate confers an edge to.
    pub target: CellId,
    /// The rights bound (`recKDelegateAtten`'s `keep`).
    pub keep: Rights,
    /// The spend ceiling.
    pub budget: u64,
    /// The runtime caveat window.
    pub caveat: Caveat,
}

impl Mandate {
    /// Construct a root mandate granted by a principal.
    pub fn root(
        grantor: CellId,
        holder: CellId,
        target: CellId,
        keep: Rights,
        budget: u64,
        caveat: Caveat,
    ) -> Self {
        Mandate {
            grantor,
            holder,
            target,
            keep,
            budget,
            caveat,
        }
    }

    /// **Strict sub-delegation** (Lean `Mandate.subDelegate`) — the ONLY way to make a child
    /// mandate. The child's `grantor` is THIS mandate's holder; its rights are `self.keep ∩ req`
    /// (so ⊆ `self.keep`); its budget is `min(self.budget, b)` (so ≤ `self.budget`); its caveat is
    /// `self.caveat ∧ cv`. No face is ever widened — a sub-delegation can only attenuate.
    pub fn sub_delegate(&self, child: CellId, req: &Rights, b: u64, cv: &Caveat) -> Mandate {
        Mandate {
            grantor: self.holder,
            holder: child,
            target: self.target,
            keep: self.keep.intersection(req).copied().collect(),
            budget: self.budget.min(b),
            caveat: self.caveat.and(cv),
        }
    }

    /// The mandate's rights bound (Lean `Mandate.rights`).
    pub fn rights(&self) -> &Rights {
        &self.keep
    }

    /// **Materialize the GRANT** onto the verified executor (Lean `Mandate.materialize` =
    /// `recKDelegateAtten`). Emits the [`Effect::GrantCapability`] the executor runs to install the
    /// attenuated cap from `grantor` to `holder`. The conferred cap carries exactly `keep` — the
    /// non-amplification the Lean `materialize_non_amplifying` proves at the wire.
    pub fn materialize_grant(&self) -> Effect {
        Effect::GrantCapability {
            from: self.grantor,
            to: self.holder,
            cap: CapabilityRef {
                target: self.target,
                // The executor rewrites the slot on grant; the value here is irrelevant.
                slot: 0,
                permissions: AuthRequired::Signature,
                breadstuff: None,
                expires_at: None,
                // The attenuated facet mask — only the kept rights' effect bits are exposed.
                allowed_effects: Some(facet_mask(&self.keep)),
                stored_epoch: None,
            },
        }
    }
}

/// A node of the delegation tree (Lean `DelegTree`): a mandate plus its children (sub-mandates).
#[derive(Clone, Debug)]
pub struct DelegTree {
    /// The mandate at this node.
    pub mandate: Mandate,
    /// The children subtrees (each born by `sub_delegate` of `mandate`).
    pub children: Vec<DelegTree>,
}

impl DelegTree {
    /// A leaf (no sub-delegations).
    pub fn leaf(mandate: Mandate) -> Self {
        DelegTree {
            mandate,
            children: Vec::new(),
        }
    }

    /// Attach a sub-delegation as a child, returning the updated tree.
    pub fn with_child(mut self, child: DelegTree) -> Self {
        self.children.push(child);
        self
    }

    /// **`well_attenuated`** (Lean `DelegTree.WellAttenuated`) — every parent→child edge is a
    /// genuine strict attenuation: child rights ⊆ parent's, budget ≤ parent's, caveat ⇒ parent's
    /// (checked on a method-code probe set), target SHARED, and grantor = parent holder. The
    /// structural invariant the agent runtime MUST maintain (its only tree-builder is
    /// `sub_delegate`, which satisfies every clause).
    pub fn well_attenuated(&self, caveat_probes: &[u64]) -> bool {
        self.children.iter().all(|c| {
            c.mandate.keep.is_subset(&self.mandate.keep)
                && c.mandate.budget <= self.mandate.budget
                && caveat_probes
                    .iter()
                    .all(|&m| !c.mandate.caveat.admits(m) || self.mandate.caveat.admits(m))
                && c.mandate.target == self.mandate.target
                && c.mandate.grantor == self.mandate.holder
        }) && self
            .children
            .iter()
            .all(|c| c.well_attenuated(caveat_probes))
    }

    /// **`no_amplify`** (Lean `subtree_rights_le_root`) — NO sub-agent out-authorizes the root:
    /// every mandate's rights in the subtree ⊆ the root's. Holds for any well-attenuated tree (the
    /// transitive chaining of `keep ⊆`); checked here directly over every descendant.
    pub fn no_amplify(&self) -> bool {
        let root = &self.mandate.keep;
        self.mandate_iter().all(|m| m.keep.is_subset(root))
    }

    /// **`budget_bounded`** (Lean `subtree_budget_le_root`) — NO descendant out-spends the root:
    /// every mandate's budget ≤ the root's.
    pub fn budget_bounded(&self) -> bool {
        let root = self.mandate.budget;
        self.mandate_iter().all(|m| m.budget <= root)
    }

    /// **`budget_partitioned`** (Lean `DelegTree.BudgetPartitioned` /
    /// `children_no_oversubscribe`) — at EVERY node the immediate children's budgets sum to ≤ the
    /// node's budget (no over-subscription: the slices fit inside the parent). The conservation
    /// facet, distinct from `budget_bounded`: the latter alone permits 10 children each carrying the
    /// FULL parent budget; this forbids it.
    pub fn budget_partitioned(&self) -> bool {
        let children_sum: u64 = self.children.iter().map(|c| c.mandate.budget).sum();
        children_sum <= self.mandate.budget && self.children.iter().all(|c| c.budget_partitioned())
    }

    /// Iterate every mandate in the subtree (root first, pre-order) — Lean `mandateList`.
    pub fn mandate_iter(&self) -> Box<dyn Iterator<Item = &Mandate> + '_> {
        Box::new(
            std::iter::once(&self.mandate)
                .chain(self.children.iter().flat_map(|c| c.mandate_iter())),
        )
    }

    /// Every mandate in a well-attenuated tree shares the root target (Lean `mandateList_target`):
    /// the holder set a single root-target revocation reaches.
    pub fn shares_root_target(&self) -> bool {
        let root_target = self.mandate.target;
        self.mandate_iter().all(|m| m.target == root_target)
    }

    /// The grant effects materializing this whole tree onto the verified executor (one
    /// `GrantCapability` per edge, pre-order). Feeding these to the executor installs the entire
    /// attenuated delegation cone.
    pub fn materialize_grants(&self) -> Vec<Effect> {
        self.mandate_iter().map(|m| m.materialize_grant()).collect()
    }
}

/// **Materialize the REVOCATION** (Lean `revoke_kills_subtree`) — emit the
/// [`Effect::RevokeDelegation`] that, run by the verified executor, severs connectivity to the
/// (single, shared) root target for the named child holder. Because every node in a well-attenuated
/// tree shares the root target ([`DelegTree::shares_root_target`]), revoking it at each holder tears
/// down the ENTIRE delegation cone — single-machine immediate revocation.
pub fn materialize_revoke(child: CellId) -> Effect {
    Effect::RevokeDelegation { child }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rights(items: &[Auth]) -> Rights {
        items.iter().copied().collect()
    }

    /// A CellId from a single byte (test fixture ids).
    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    /// The demo tree of the Lean `demoTree`: principal 0 → agent 1 (budget 100, {read,write}) →
    /// sub-agent 2 (budget 40, {read}) → sub-sub-agent 3 (budget 10, {read}).
    fn demo_tree() -> DelegTree {
        let root = Mandate::root(
            cid(0),
            cid(1),
            cid(7),
            rights(&[Auth::Read, Auth::Write]),
            100,
            Caveat::any(),
        );
        let child = root.sub_delegate(cid(2), &rights(&[Auth::Read]), 40, &Caveat::any());
        let grand = child.sub_delegate(cid(3), &rights(&[Auth::Read]), 10, &Caveat::any());
        DelegTree::leaf(root).with_child(DelegTree::leaf(child).with_child(DelegTree::leaf(grand)))
    }

    #[test]
    fn demo_tree_well_attenuated() {
        // Lean `demoTree_wellAttenuated`.
        assert!(demo_tree().well_attenuated(&[0, 1, 2, 99]));
    }

    #[test]
    fn demo_tree_budget_partitioned() {
        // Lean `demoTree_budgetPartitioned`: 40 ≤ 100, 10 ≤ 40, leaves trivial.
        assert!(demo_tree().budget_partitioned());
    }

    #[test]
    fn demo_no_amplify() {
        // Lean `demo_no_amplify`: every mandate's rights ⊆ root {read,write}.
        assert!(demo_tree().no_amplify());
    }

    #[test]
    fn demo_budget_bounded() {
        // Lean `demo_budget_bounded`: every budget ≤ 100.
        assert!(demo_tree().budget_bounded());
    }

    #[test]
    fn overbudget_is_clamped() {
        // Lean `demo_overbudget_clamped`: asking 999 against a parent of 100 yields 100, never 999.
        let root = Mandate::root(
            cid(0),
            cid(1),
            cid(7),
            rights(&[Auth::Read]),
            100,
            Caveat::any(),
        );
        let child = root.sub_delegate(cid(2), &rights(&[Auth::Read]), 999, &Caveat::any());
        assert_eq!(child.budget, 100);
    }

    #[test]
    fn rights_genuinely_narrow() {
        // Lean `demo_rights_narrow`: a read-only sub-delegation drops write.
        let root = Mandate::root(
            cid(0),
            cid(1),
            cid(7),
            rights(&[Auth::Read, Auth::Write]),
            100,
            Caveat::any(),
        );
        let child = root.sub_delegate(cid(2), &rights(&[Auth::Read]), 40, &Caveat::any());
        assert_eq!(child.keep, rights(&[Auth::Read]));
        assert!(!child.keep.contains(&Auth::Write));
    }

    #[test]
    fn caveat_window_narrows() {
        // Lean `subDelegate_caveat_narrows`: if the child admits a method, so does the parent.
        let root = Mandate::root(
            cid(0),
            cid(1),
            cid(7),
            rights(&[Auth::Read]),
            100,
            Caveat::only(&[1, 2, 3]),
        );
        let child = root.sub_delegate(cid(2), &rights(&[Auth::Read]), 40, &Caveat::only(&[2]));
        // child admits only 2 (intersection of {1,2,3} and {2}); parent admits it too.
        assert!(child.caveat.admits(2));
        assert!(root.caveat.admits(2));
        // child does NOT admit 1 (narrowed away), and never admits something outside the parent.
        assert!(!child.caveat.admits(1));
        for m in 0..10u64 {
            assert!(!child.caveat.admits(m) || root.caveat.admits(m));
        }
    }

    #[test]
    fn oversubscription_is_caught() {
        // TEETH for budget_partitioned: two children each carrying the full parent budget
        // over-subscribes — the predicate REFUSES it (the conservation facet has teeth).
        let root = Mandate::root(
            cid(0),
            cid(1),
            cid(7),
            rights(&[Auth::Read]),
            100,
            Caveat::any(),
        );
        // Bypass `sub_delegate`'s clamp to forge an over-subscribing tree (an adversarial runtime).
        let mut c1 = root.sub_delegate(cid(2), &rights(&[Auth::Read]), 100, &Caveat::any());
        let mut c2 = root.sub_delegate(cid(3), &rights(&[Auth::Read]), 100, &Caveat::any());
        c1.budget = 100;
        c2.budget = 100;
        let bad = DelegTree::leaf(root)
            .with_child(DelegTree::leaf(c1))
            .with_child(DelegTree::leaf(c2));
        // 100 + 100 = 200 > 100 — over-subscribed.
        assert!(!bad.budget_partitioned());
        // ...but `budget_bounded` (the weaker facet) still passes — the two facets are DISTINCT.
        assert!(bad.budget_bounded());
    }

    #[test]
    fn amplification_is_caught() {
        // TEETH for no_amplify: a forged child claiming MORE rights than its parent is refused.
        let root = Mandate::root(
            cid(0),
            cid(1),
            cid(7),
            rights(&[Auth::Read]),
            100,
            Caveat::any(),
        );
        let mut rogue = root.sub_delegate(cid(2), &rights(&[Auth::Read]), 40, &Caveat::any());
        rogue.keep = rights(&[Auth::Read, Auth::Write, Auth::Control]); // forged amplification
        let bad = DelegTree::leaf(root).with_child(DelegTree::leaf(rogue));
        assert!(!bad.no_amplify());
        assert!(!bad.well_attenuated(&[]));
    }

    #[test]
    fn shares_root_target_holds() {
        // Lean `mandateList_target`: every node shares the root target (revocation reaches all).
        assert!(demo_tree().shares_root_target());
    }

    #[test]
    fn materialize_emits_real_effects() {
        // The grant effects are real executor effects (GrantCapability), one per tree edge.
        let tree = demo_tree();
        let effects = tree.materialize_grants();
        assert_eq!(effects.len(), 3); // root + child + grandchild
        match &effects[0] {
            Effect::GrantCapability { from, to, cap } => {
                assert_eq!(*from, cid(0));
                assert_eq!(*to, cid(1));
                assert_eq!(cap.target, cid(7));
            }
            other => panic!("expected GrantCapability, got {other:?}"),
        }
        // Revocation is a real RevokeDelegation effect.
        match materialize_revoke(cid(2)) {
            Effect::RevokeDelegation { child } => assert_eq!(child, cid(2)),
            other => panic!("expected RevokeDelegation, got {other:?}"),
        }
    }
}
