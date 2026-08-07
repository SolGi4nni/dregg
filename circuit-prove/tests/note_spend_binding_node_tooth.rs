//! THE NOTE-SPEND BINDING-NODE MECHANISM TOOTH (bridge carrier, G2 backing half).
//!
//! [`note_spend_leaf_adapter`] re-proves the REAL foreign note-spend STARK
//! (`dregg-note-spending-dsl-v3` — the circuit `apply_bridge_mint` verifies off-AIR
//! via `verify_note_spend_dsl_full`) as a recursion-foldable IR-v2 leaf whose
//! `expose_claim` is the 7-slot tuple `[nullifier, merkle_root, value_lo,
//! asset_type, destination_federation, value_hi, mint_hash]`, with lane 6 the
//! in-AIR-recomputed felt-domain mint identity.
//!
//! This test exercises the BINDING NODE over real leaves:
//!
//!   * POSITIVE: folding a leg whose claimed tuple IS backed by the note-spend
//!     sub-proof succeeds, and the node re-exposes the bound tuple.
//!   * NEGATIVE (the fold tooth at node level): a leg claiming a DIFFERENT tuple
//!     (another spend's nullifier/mint_hash) has no satisfying assembly — the
//!     per-lane `connect` is a conflict, so NO root exists and a pure light client
//!     never receives a verifying artifact for the forged backing.
//!
//! ⚑ The DEPLOYED leg (the `mintV3` felt-domain mint_hash PI-emit + dual-expose)
//! is the named VK-gated big-bang piece — see the adapter's module docs. Until the
//! regen lands this is the MECHANISM tooth; `Dregg2.Circuit.BridgeBackingAttack`
//! STANDS.
//!
//! ANSWERS:         do two distinct real note-spend witnesses prove as claim leaves, does folding leaf A against ITSELF through prove_note_spend_binding_node succeed and re-expose exactly the tuple A claims, and does folding leaf A against leaf B return SOME Err?
//! DOES NOT ANSWER: whether the refusal is the BINDING that fired. This file calls bare must_refuse, not assert_refused_by_binding_node, so any Err satisfies the negative pole — an OOM, an FRI fault or a trace-shape error all read as the forgery being rejected. It also reaches no deployed leg: the positive pole folds one leaf against itself, so no leg-versus-sub-proof distinction is exercised anywhere here.

use dregg_circuit::field::BabyBear;
use dregg_circuit::note_spending_witness::{NoteSpendingWitness, test_spending_key};
use dregg_circuit::poseidon2::hash_many;
use dregg_circuit::refusal::must_refuse;
use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

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
use dregg_circuit_prove::note_spend_leaf_adapter::{
    note_spend_leaf_public_inputs, prove_note_spend_binding_node, prove_note_spend_leaf_with_claim,
    read_exposed_note_spend_claim,
};

/// SCOPE — printed by every test in this file. The module doc above and these two
/// strings are two copies of one statement and MUST stay BYTE-IDENTICAL: Rust has no
/// cheap single-source-of-truth for a doc line that is also runtime output.
fn scope() {
    println!(
        "ANSWERS:         do two distinct real note-spend witnesses prove as claim leaves, does folding leaf A against ITSELF through prove_note_spend_binding_node succeed and re-expose exactly the tuple A claims, and does folding leaf A against leaf B return SOME Err?"
    );
    println!(
        "DOES NOT ANSWER: whether the refusal is the BINDING that fired. This file calls bare must_refuse, not assert_refused_by_binding_node, so any Err satisfies the negative pole — an OOM, an FRI fault or a trace-shape error all read as the forgery being rejected. It also reaches no deployed leg: the positive pole folds one leaf against itself, so no leg-versus-sub-proof distinction is exercised anywhere here."
    );
}

/// A REAL full-width witness (raw 32-byte fields, > 2^30 value so the high limb is
/// live), depth 2 (the one-padding-row discipline the deployed DSL circuit uses).
fn make_witness(tag: u8) -> NoteSpendingWitness {
    let owner = [tag; 32];
    let nonce = [tag ^ 0x5A; 32];
    let rand = [tag ^ 0xA5; 32];
    let key = test_spending_key(tag as u32 + 0x77);
    let depth = 2;
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    for i in 0..depth {
        siblings.push([
            hash_many(&[BabyBear::new((i * 3 + 1) as u32), BabyBear::new(tag as u32)]),
            hash_many(&[BabyBear::new((i * 3 + 2) as u32), BabyBear::new(tag as u32)]),
            hash_many(&[BabyBear::new((i * 3 + 3) as u32), BabyBear::new(tag as u32)]),
        ]);
        positions.push((i % 4) as u8);
    }
    NoteSpendingWitness::from_note_limbs(
        &owner,
        0xDEAD_BEEF_CAFE,
        3,
        &nonce,
        &rand,
        key,
        siblings,
        positions,
    )
}

#[test]
fn note_spend_binding_node_bites() {
    scope();
    let config = ir2_leaf_wrap_config();

    // Two DISTINCT real spends → two distinct claim tuples.
    let w_a = make_witness(0x44);
    let w_b = make_witness(0x55);
    let pis_a = note_spend_leaf_public_inputs(&w_a);
    let pis_b = note_spend_leaf_public_inputs(&w_b);
    assert_ne!(pis_a, pis_b, "distinct spends must claim distinct tuples");

    let leaf_a = prove_note_spend_leaf_with_claim(&w_a, &pis_a, &config)
        .expect("honest note-spend A folds as a claim leaf");
    let leaf_b = prove_note_spend_leaf_with_claim(&w_b, &pis_b, &config)
        .expect("honest note-spend B folds as a claim leaf");

    // POSITIVE POLE: a leg claiming the tuple the sub-proof genuinely backs folds,
    // and the node re-exposes the bound tuple.
    let node = prove_note_spend_binding_node(&leaf_a, &leaf_a, &pins(&leaf_a, &leaf_a), &config)
        .expect("a backed claim must fold through the binding node");
    let bound = read_exposed_note_spend_claim(&node).expect("the node re-exposes the bound tuple");
    assert_eq!(
        bound.as_slice(),
        pis_a.as_slice(),
        "the node's bound tuple is the backed claim"
    );

    // NEGATIVE POLE (THE TOOTH): a leg claiming tuple A folded against a sub-proof
    // backing tuple B is a per-lane `connect` conflict — UNSAT, no root.
    must_refuse(
        "a claim with NO backing note-spend folded through the node",
        || prove_note_spend_binding_node(&leaf_a, &leaf_b, &pins(&leaf_a, &leaf_b), &config),
    );
}
