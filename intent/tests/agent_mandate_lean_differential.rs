//! Agent-mandate differential: PIN the Rust `agent_mandate` algebra against the VERIFIED Lean
//! `Dregg2.Agent.Mandate` theorems (`metatheory/Dregg2/Agent/Mandate.lean`).
//!
//! # Why this test exists (the coherence move)
//!
//! The SDK's sub-agent path (`sdk/src/runtime.rs`, `SubAgent::execute`) historically checked a
//! spawned worker's capabilities OUT-OF-BAND. The agent layer makes those checks IN-BAND, typed,
//! over a delegation TREE — and the THREE tree-level invariants are PROVED in Lean:
//!
//!   * `subtree_rights_le_root`     — no sub-agent amplifies authority.
//!   * `subtree_budget_le_root` +
//!     `children_no_oversubscribe`  — budget is conserved across the tree (bound + conservation).
//!   * `revoke_kills_subtree`       — revocation propagates to the whole subtree.
//!
//! plus the non-vacuity fixtures `demoTree_wellAttenuated` / `demoTree_budgetPartitioned` /
//! `demo_no_amplify` / `demo_budget_bounded` and the teeth (`demo_overbudget_clamped`,
//! `demo_rights_narrow`).
//!
//! This test reconstructs the EXACT Lean `demoTree` (principal 0 → agent 1 budget 100 {read,write}
//! → sub-agent 2 budget 40 {read} → sub-sub-agent 3 budget 10 {read}) in the Rust mirror and asserts
//! the Rust predicates return the SAME verdicts the Lean theorems prove — and that the teeth
//! (over-subscription, amplification) are genuinely REFUSED. A drift between the two surfaces fails
//! the build, so the running agent layer cannot silently diverge from the verified statement.
//!
//! Materialization is checked structurally: the grant effects the mirror emits are the real
//! `Effect::GrantCapability` moves the verified executor's delegate-atten arm consumes (Lean
//! `Mandate.materialize = recKDelegateAtten`, which `authorityattenuation.lean` proves IS
//! `execFullA`'s arm), with the attenuated facet mask narrowing exactly as `keep` narrows.

use std::collections::BTreeSet;

use dregg_cell::facet::{EFFECT_GRANT_CAPABILITY, EFFECT_SET_FIELD, EFFECT_TRANSFER};
use dregg_cell::CellId;
use dregg_intent::agent_mandate::{
    materialize_revoke, Auth, Caveat, DelegTree, Mandate, Rights,
};
use dregg_turn::action::Effect;

fn rights(items: &[Auth]) -> Rights {
    items.iter().copied().collect::<BTreeSet<_>>()
}

fn cid(b: u8) -> CellId {
    CellId::from_bytes([b; 32])
}

/// The EXACT Lean `demoTree` (Mandate.lean §9): principal 0 → agent 1 (100, {read,write}) →
/// sub-agent 2 (40, {read}) → sub-sub-agent 3 (10, {read}).
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
fn rust_agrees_with_lean_demo_well_attenuated() {
    // Lean `demoTree_wellAttenuated`.
    assert!(demo_tree().well_attenuated(&[0, 1, 2, 99]));
}

#[test]
fn rust_agrees_with_lean_demo_budget_partitioned() {
    // Lean `demoTree_budgetPartitioned`: 40 ≤ 100, 10 ≤ 40.
    assert!(demo_tree().budget_partitioned());
}

#[test]
fn rust_agrees_with_lean_subtree_rights_le_root() {
    // Lean `subtree_rights_le_root` / `demo_no_amplify`.
    assert!(demo_tree().no_amplify());
}

#[test]
fn rust_agrees_with_lean_subtree_budget_le_root() {
    // Lean `subtree_budget_le_root` / `demo_budget_bounded`.
    assert!(demo_tree().budget_bounded());
}

#[test]
fn rust_agrees_with_lean_mandate_list_target() {
    // Lean `mandateList_target`: every node shares the root target (revocation reaches all).
    assert!(demo_tree().shares_root_target());
}

#[test]
fn teeth_overbudget_clamped() {
    // Lean `demo_overbudget_clamped`: min(parent, 999) = parent, never 999.
    let root = Mandate::root(cid(0), cid(1), cid(7), rights(&[Auth::Read]), 100, Caveat::any());
    let child = root.sub_delegate(cid(2), &rights(&[Auth::Read]), 999, &Caveat::any());
    assert_eq!(child.budget, 100);
}

#[test]
fn teeth_rights_narrow() {
    // Lean `demo_rights_narrow`: read-only sub-delegation drops write.
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
}

#[test]
fn teeth_oversubscription_refused() {
    // The conservation facet (Lean `children_no_oversubscribe`) has teeth: an adversarial runtime
    // that forges two children each with the full parent budget over-subscribes — REFUSED.
    let root = Mandate::root(cid(0), cid(1), cid(7), rights(&[Auth::Read]), 100, Caveat::any());
    let mut c1 = root.sub_delegate(cid(2), &rights(&[Auth::Read]), 100, &Caveat::any());
    let mut c2 = root.sub_delegate(cid(3), &rights(&[Auth::Read]), 100, &Caveat::any());
    c1.budget = 100;
    c2.budget = 100;
    let bad = DelegTree::leaf(root)
        .with_child(DelegTree::leaf(c1))
        .with_child(DelegTree::leaf(c2));
    assert!(!bad.budget_partitioned()); // 200 > 100 — refused
    assert!(bad.budget_bounded()); // the weaker facet still passes — the two are DISTINCT
}

#[test]
fn teeth_amplification_refused() {
    // Lean `subtree_rights_le_root` teeth: a forged child claiming MORE rights is refused.
    let root = Mandate::root(cid(0), cid(1), cid(7), rights(&[Auth::Read]), 100, Caveat::any());
    let mut rogue = root.sub_delegate(cid(2), &rights(&[Auth::Read]), 40, &Caveat::any());
    rogue.keep = rights(&[Auth::Read, Auth::Write, Auth::Control]);
    let bad = DelegTree::leaf(root).with_child(DelegTree::leaf(rogue));
    assert!(!bad.no_amplify());
    assert!(!bad.well_attenuated(&[]));
}

#[test]
fn materialization_emits_executor_effects_with_narrowing_facets() {
    // Materialize the whole tree: one real `Effect::GrantCapability` per edge (Lean
    // `materialize_grants`), with the facet mask narrowing exactly as `keep` narrows.
    let tree = demo_tree();
    let effects = tree.materialize_grants();
    assert_eq!(effects.len(), 3); // root + child + grandchild

    // Root (agent 1) carries {read,write} ⟹ facet has BOTH SetField and Transfer.
    match &effects[0] {
        Effect::GrantCapability { from, to, cap } => {
            assert_eq!(*from, cid(0));
            assert_eq!(*to, cid(1));
            assert_eq!(cap.target, cid(7));
            let mask = cap.allowed_effects.expect("facet mask present");
            assert!(mask & EFFECT_SET_FIELD != 0);
            assert!(mask & EFFECT_TRANSFER != 0); // write right ⟹ transfer facet
        }
        other => panic!("expected GrantCapability, got {other:?}"),
    }

    // Child (sub-agent 2) is read-only ⟹ facet has SetField but NOT Transfer (write dropped).
    match &effects[1] {
        Effect::GrantCapability { to, cap, .. } => {
            assert_eq!(*to, cid(2));
            let mask = cap.allowed_effects.expect("facet mask present");
            assert!(mask & EFFECT_SET_FIELD != 0);
            assert_eq!(mask & EFFECT_TRANSFER, 0); // write was attenuated away
            assert_eq!(mask & EFFECT_GRANT_CAPABILITY, 0); // no grant right either
        }
        other => panic!("expected GrantCapability, got {other:?}"),
    }

    // Revocation is a real `Effect::RevokeDelegation` (Lean `revoke_kills_subtree`).
    match materialize_revoke(cid(2)) {
        Effect::RevokeDelegation { child } => assert_eq!(child, cid(2)),
        other => panic!("expected RevokeDelegation, got {other:?}"),
    }
}
