//! # THE MEMBERSHIP-BINDING FOLD-MECHANISM TOOTH.
//!
//! The membership analog of the in-lib custom fold-wire teeth: it
//! exercises the membership-binding MECHANISM end-to-end over REAL recursion leaves, WITHOUT the
//! deployed `SenderAuthorized` leg's tuple-emit (the named big-bang piece). Two
//! `prove_membership_leaf_with_claim` leaves — each a genuine membership leaf re-exposing its bound
//! 2-slot `(sender_leaf, authorized_root)` tuple as an `expose_claim` — are folded through
//! `prove_membership_binding_node`, which `connect`s the two tuples lane-by-lane.
//!
//! * HONEST (in-set) — both leaves bind the SAME `(sender_leaf, authorized_root)`: the per-lane
//!   `connect` is consistent, the node folds, the bound tuple is re-exposed. A pure light client
//!   folding it now WITNESSES the sender's set-membership tuple.
//! * FORGED (out-of-set) — the "leg" leaf claims a DIFFERENT `(sender_leaf, authorized_root)` than
//!   the bound membership leaf: the per-lane `connect` is a conflict ⇒ the aggregation is UNSAT ⇒ no
//!   node proof. This is the bite that makes the membership REAL for a pure light client: a leg
//!   cannot claim a membership tuple no verifying membership leaf backs.
//!
//! The deployed wiring (a DUAL-EXPOSE `SenderAuthorized` leg leaf, segment ++ the `(leaf, root)`
//! tuple at fixed PI slots, folded via `prove_membership_binding_node_segmented`) is READY but gated
//! on the `SenderAuthorized` descriptor EMITTING the tuple PIs (today the effect-vm "membership"
//! column is the unrelated `cap_root`); that descriptor-emit rides the big-bang VK regen. This tooth
//! proves the fold MECHANISM + the membership leaf are correct today.
//!
//! Real recursion (minutes), so both poles are `#[ignore]`. Run with:
//!   cargo test -p dregg-circuit-prove --test membership_binding_mechanism -- --ignored --nocapture

use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::must_refuse;
use dregg_circuit_prove::binding_tooth::assert_node_refused_by_binding_connect;
use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;
use dregg_circuit_prove::membership_leaf_adapter::MEMBERSHIP_BINDING_NODE_ARM;

/// ⚑ TRACKED child-VK pins for a 2-to-1 fold (`dregg_circuit_prove::fold_vk_pin`) — every fold in
/// the crate now takes them, because `into_recursion_input` left each child's preprocessed
/// commitment an unconstrained runtime public input.
fn pins(
    l: &p3_recursion::RecursionOutput<
        dregg_circuit_prove::plonky3_recursion_impl::recursive::DreggRecursionConfig,
    >,
    r: &p3_recursion::RecursionOutput<
        dregg_circuit_prove::plonky3_recursion_impl::recursive::DreggRecursionConfig,
    >,
) -> dregg_circuit_prove::fold_vk_pin::FoldVkPins {
    dregg_circuit_prove::fold_vk_pin::FoldVkPins::tracked(l, r)
        .expect("both fold children carry a preprocessed commitment")
}
use dregg_circuit_prove::membership_leaf_adapter::{
    SenderMembershipWitness, prove_membership_binding_node, prove_membership_leaf_with_claim,
};

fn witness(sender_leaf: u32) -> SenderMembershipWitness {
    SenderMembershipWitness {
        sender_leaf: BabyBear::new(sender_leaf),
        authorized_root: BabyBear::new(7777777),
    }
}

/// POSITIVE POLE — the leg leaf and the membership leaf bind the SAME `(sender_leaf, authorized_root)`
/// tuple (the sender is genuinely in the authorized set): the binding node folds and re-exposes the
/// bound tuple.
#[test]
#[ignore = "SLOW: real membership-binding recursion fold (~minutes); run with --ignored"]
fn membership_binding_honest_folds() {
    let config = ir2_leaf_wrap_config();
    let w = witness(42424242);
    let pis = w.public_inputs();

    let leg = prove_membership_leaf_with_claim(&w, &pis, &config)
        .expect("membership leg claim leaf mints");
    let ms = prove_membership_leaf_with_claim(&w, &pis, &config).expect("membership leaf mints");

    prove_membership_binding_node(&leg, &ms, &pins(&leg, &ms), &config)
        .expect("the honest membership-binding node folds (tuples agree)");
    eprintln!("MEMBERSHIP binding: honest in-set tuple FOLDED + bound in the recursion tree.");
}

/// THE TOOTH — the leg leaf claims a DIFFERENT `(sender_leaf, authorized_root)` (an out-of-set
/// sender) than the bound membership leaf: the in-circuit `connect` is a conflict ⇒ UNSAT ⇒ no node
/// proof.
#[test]
#[ignore = "SLOW: real membership-binding recursion fold (~minutes); run with --ignored"]
fn membership_binding_forged_rejected() {
    let config = ir2_leaf_wrap_config();
    let leg_w = witness(99999999); // the leg claims a DIFFERENT (out-of-set) sender leaf
    let ms_w = witness(42424242); // the bound membership leaf binds the honest in-set one
    let leg_pis = leg_w.public_inputs();
    let ms_pis = ms_w.public_inputs();
    assert_ne!(leg_pis, ms_pis);

    let leg = prove_membership_leaf_with_claim(&leg_w, &leg_pis, &config)
        .expect("the forged leg is itself a valid (but DIFFERENT) membership leaf");
    let ms = prove_membership_leaf_with_claim(&ms_w, &ms_pis, &config)
        .expect("the honest membership leaf mints");

    let what = "a leg claiming a membership tuple NO bound membership leaf backs folded into a verifying \
         node";
    let err = must_refuse(what, || {
        prove_membership_binding_node(&leg, &ms, &pins(&leg, &ms), &config)
    });
    // ⚑ ASSERT THE REASON. Bare `must_refuse` here accepted ANY `Err` — an OOM, an FRI fault, or
    // the node's own "leg leaf carries no expose_claim" pre-flight — all of which would have kept
    // this tooth green with the per-lane `connect` never built.
    assert_node_refused_by_binding_connect(what, &err, MEMBERSHIP_BINDING_NODE_ARM);
    eprintln!(
        "MEMBERSHIP binding: out-of-set tuple REJECTED by the fold (connect conflict ⇒ no root)."
    );
}
