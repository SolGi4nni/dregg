//! Deployed light-client tooth for the Lean-authored private graph-rewrite cell.
//!
//! This is deliberately heavier than the module's fast verifier tests.  It puts
//! the exact direct-IR2 witness bundle on a genuine rotated `Effect::Custom` leg,
//! folds that leg through `prove_turn_chain_recursive`, and verifies the resulting
//! whole-chain artifact as a light client.  Consequently the recursive artifact
//! binds all four joins at once:
//!
//! * the custom program's canonical VK8;
//! * the cell's real old/new commitment8 anchors;
//! * the private graph proof's whole public-input commitment8; and
//! * the proved graph-new-root8 to committed post-state fields `0..8`.
//!
//! Honest scope: the current `Effect::Custom` face is a nonce-tick with frozen
//! fields.  This test therefore models the proof turn as an attestation of a
//! candidate graph root staged in the cell by an earlier ordinary field-write
//! turn; it does not pretend the custom turn itself writes that root.  Making
//! staging+attestation atomic requires a dedicated custom-app-write face (or a
//! proven multi-effect composition) and remains a named protocol seam.
//!
//! The test is ignored in the everyday profile because it mints real recursion
//! proofs.  Run it in release mode on the build node.

use dregg_cell::{Cell, Ledger, field_from_u64};
use dregg_circuit::descriptor_ir2::{
    UMemBoundaryWitness, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest,
    generate_rotated_effect_vm_descriptor_and_trace_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive, verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{
    CarrierWitness, DescriptorParticipant, RotatedParticipantLeg,
};
use dregg_circuit_prove::private_graph_rewrite::{
    BoundedContext, BoundedGraph, BoundedPattern, BoundedRule, HostEdgeSlot,
    PrivateGraphRewriteWitness, RuleEdgeSlot,
};
use dregg_circuit_prove::{private_graph_rewrite, private_graph_rewrite_cell};
use dregg_turn::rotation_witness as rw;

const BALANCE: i64 = 1_000;
const DOMAIN: u32 = 11;
const SESSION: u32 = 77;
const STEP_INDEX: u32 = 9;

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn cell(nonce: u64, graph_root: [u32; 8]) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], BALANCE);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    for (slot, lane) in graph_root.into_iter().enumerate() {
        assert!(cell.state.set_field(slot, field_from_u64(lane as u64)));
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

fn pattern(slots: [RuleEdgeSlot; 2]) -> BoundedPattern {
    BoundedPattern { slots }
}

fn graph_witness() -> PrivateGraphRewriteWitness {
    let context = BoundedContext {
        slots: [HostEdgeSlot::edge(4, 7, 8), HostEdgeSlot::edge(5, 8, 9)],
    };
    let rule0 = BoundedRule {
        lhs: pattern([RuleEdgeSlot::edge(1, 0, 1), RuleEdgeSlot::padding()]),
        rhs: pattern([RuleEdgeSlot::edge(2, 0, 1), RuleEdgeSlot::edge(3, 1, 2)]),
    };
    let rule1 = BoundedRule {
        lhs: pattern([RuleEdgeSlot::edge(6, 2, 3), RuleEdgeSlot::padding()]),
        rhs: pattern([RuleEdgeSlot::edge(7, 3, 2), RuleEdgeSlot::padding()]),
    };
    PrivateGraphRewriteWitness {
        old_graph: BoundedGraph {
            slots: [
                HostEdgeSlot::edge(1, 4, 5),
                HostEdgeSlot::edge(4, 7, 8),
                HostEdgeSlot::padding(),
                HostEdgeSlot::edge(5, 8, 9),
            ],
        },
        new_graph: BoundedGraph {
            slots: [
                HostEdgeSlot::edge(4, 7, 8),
                HostEdgeSlot::edge(5, 8, 9),
                HostEdgeSlot::edge(2, 4, 5),
                HostEdgeSlot::edge(3, 5, 6),
            ],
        },
        rules: [rule0, rule1],
        sigma: [4, 5, 6, 7],
        context,
        old_blind: [101, 102, 103, 104],
        new_blind: [201, 202, 203, 204],
        rule_blinds: [[301, 302, 303, 304], [401, 402, 403, 404]],
        rule_slot: false,
    }
}

fn mint_custom_leg(
    nonce: u64,
    before_graph_root: [u32; 8],
    after_graph_root: [u32; 8],
    proof_commitment: [BabyBear; 8],
    program_vk_hash: [BabyBear; 8],
    carrier_witness: Option<CarrierWitness>,
) -> RotatedParticipantLeg {
    assert_eq!(
        before_graph_root, after_graph_root,
        "the deployed Custom face freezes fields; stage the candidate root before attesting it"
    );
    let before_cell = cell(nonce, before_graph_root);
    let after_cell = cell(nonce + 1, after_graph_root);
    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).expect("ledger seed");
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log = vec![[3u8; 32]];
    let before_w = bridge(&rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &rw::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    ));
    let after_w = bridge(&rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &rw::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    ));
    let mut state = CellState::new(BALANCE as u64, nonce as u32);
    state.fields = before_graph_root.map(BabyBear::new);
    state.refresh_commitment();
    let effects = vec![Effect::Custom {
        program_vk_hash,
        proof_commitment,
    }];
    let (descriptor, trace, public_inputs, map_heaps, memory) =
        generate_rotated_effect_vm_descriptor_and_trace_wide(
            &state,
            &effects,
            &before_w,
            &after_w,
            &empty_caveat_manifest(),
            None,
            None,
            None,
            None,
        )
        .expect("custom wide dispatch");

    let octet_lo = public_inputs
        .len()
        .checked_sub(24)
        .expect("field octet plus two wide anchors");
    assert_eq!(
        &public_inputs[octet_lo..octet_lo + 8],
        &after_graph_root.map(BabyBear::new),
        "the deployed custom leg must publish committed fields[0..8]"
    );

    let config = ir2_leaf_wrap_config();
    let proof = prove_vm_descriptor2_for_config(
        &descriptor,
        &trace,
        &public_inputs,
        &memory,
        &map_heaps,
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("custom wide leg proves");
    verify_vm_descriptor2_with_config(&descriptor, &proof, &public_inputs, &config)
        .expect("fresh custom wide proof self-verifies under the leaf-wrap config");
    RotatedParticipantLeg {
        proof,
        descriptor,
        public_inputs,
        carrier_witness,
    }
}

fn graph_roots() -> ([u32; 8], [u32; 8]) {
    let statement = private_graph_rewrite::statement(DOMAIN, SESSION, STEP_INDEX, &graph_witness())
        .expect("valid private graph statement");
    (statement.old_root, statement.new_root)
}

fn honest_chain() -> Vec<FinalizedTurn> {
    let (graph_old, graph_new) = graph_roots();
    let vk8 = private_graph_rewrite_cell::vk_recipe().canonical_vk_felts();

    // Probe the real rotated roots first.  They depend on the two cell images,
    // not on the custom proof commitment, so the graph proof can then name the
    // exact state transition the deployed leg will carry.
    let probe = mint_custom_leg(0, graph_new, graph_new, [BabyBear::ZERO; 8], vk8, None);
    let old8 = probe.wide_old_root8().expect("wide old root");
    let new8 = probe.wide_new_root8().expect("wide new root");
    let old_u32 = old8.map(|felt| felt.as_u32());
    let new_u32 = new8.map(|felt| felt.as_u32());

    let (_zk, public, bundle) = private_graph_rewrite_cell::prove_zk(
        DOMAIN,
        SESSION,
        STEP_INDEX,
        &graph_witness(),
        old_u32,
        new_u32,
    )
    .expect("private graph cell proof");
    assert_eq!(public.rewrite.old_root, graph_old);
    assert_eq!(public.rewrite.new_root, graph_new);
    assert_eq!(bundle.vk_recipe.canonical_vk_felts(), vk8);

    let commitment = custom_proof_pi_commitment(&bundle.public_inputs);
    let first_leg = mint_custom_leg(
        0,
        graph_new,
        graph_new,
        commitment,
        vk8,
        Some(CarrierWitness::CustomIr2(bundle)),
    );
    assert_eq!(first_leg.wide_old_root8(), Some(old8));
    assert_eq!(first_leg.wide_new_root8(), Some(new8));

    // A plain second turn gives the recursion tree a sibling and preserves the
    // graph root.  Its lack of a carrier witness is the ordinary re-execution
    // rung and does not weaken turn zero's direct-IR2 binding node.
    let second_leg = mint_custom_leg(
        1,
        graph_new,
        graph_new,
        core::array::from_fn(|lane| BabyBear::new(700 + lane as u32)),
        vk8,
        None,
    );
    let first = FinalizedTurn::new(DescriptorParticipant::rotated(first_leg));
    let second = FinalizedTurn::new(DescriptorParticipant::rotated(second_leg));
    assert_eq!(first.new_root(), second.old_root());
    vec![first, second]
}

#[test]
#[ignore = "heavy: real private graph HidingFri + deployed direct-IR2 whole-chain recursion"]
fn deployed_private_graph_rewrite_attests_a_precommitted_cell_root_to_a_light_client() {
    let turns = honest_chain();
    let whole = prove_turn_chain_recursive(&turns)
        .expect("the honest graph-rewrite carrier must fold through the deployed chain prover");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the light client must accept the graph/state/VK/app-root-bound artifact");
}
