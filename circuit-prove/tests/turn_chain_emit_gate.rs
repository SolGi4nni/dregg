//! Byte-pin and real-prover gate for the Lean-emitted whole-history turn-chain binding.
//!
//! Constraint authorship lives only in
//! `metatheory/Dregg2/Circuit/Emit/EffectVmEmitTurnChainBinding.lean`. This test pins Lean's exact
//! bytes, parses and dispatches that artifact, proves the production chip-lane witness, verifies it,
//! and drives forged continuity/index/count/public fixtures to rejection.

use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit::refusal::{Outcome, classify};
use dregg_circuit::turn_chain_witness::{
    ACC_IN, ACC_OUT, IDX, IS_REAL, OLD_ROOT, PI_CHAIN_DIGEST, PI_FINAL_ROOT, PI_NUM_TURNS,
    REAL_COUNT, TURN_CHAIN_BINDING_NAME, TURN_CHAIN_BINDING_PI_COUNT, TURN_CHAIN_BINDING_WIDTH,
    turn_chain_binding_witness,
};

/// Exact `DescriptorIR2.emitVmJson2 turnChainBindingDescriptor` bytes, pinned by Lean's
/// `TURN_CHAIN_BINDING_GOLDEN` equality guard.
const GOLDEN_JSON: &str = r#"{"name":"dregg-turn-chain-binding-v2","ir":2,"trace_width":7,"public_input_count":4,"tables":[],"constraints":[{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"loc","c":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"nxt","c":0}}}},{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"last","col":1,"pi_index":1},{"t":"boundary","row":"first","body":{"t":"var","v":2}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"loc","c":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"nxt","c":2}}}},{"t":"pi_binding","row":"last","col":3,"pi_index":3},{"t":"lookup","table":8,"tuple":[{"t":"const","v":4},{"t":"var","v":2},{"t":"var","v":0},{"t":"var","v":1},{"t":"var","v":4},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":3}]},{"t":"boundary","row":"first","body":{"t":"var","v":4}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":4},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":4}},"r":{"t":"const","v":-1}}}},{"t":"window_gate","on_transition":false,"body":{"t":"mul","l":{"t":"loc","c":5},"r":{"t":"add","l":{"t":"loc","c":5},"r":{"t":"const","v":-1}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"nxt","c":5},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":5}}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":5}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":6},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":6}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"nxt","c":5}}}}},{"t":"pi_binding","row":"last","col":6,"pi_index":2}],"hash_sites":[],"ranges":[]}"#;

fn honest_fixture() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    turn_chain_binding_witness(&[
        (BabyBear::new(11), BabyBear::new(22)),
        (BabyBear::new(22), BabyBear::new(33)),
        (BabyBear::new(33), BabyBear::new(44)),
    ])
    .expect("continuous three-turn witness builds")
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("turn-chain emit gate rejection", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        Outcome::UnsatPanic(_) | Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

#[test]
fn lean_bytes_parse_dispatch_and_shape() {
    let checked_in = include_str!("../../circuit/descriptors/by-name/turn-chain-binding.json");
    assert_eq!(
        GOLDEN_JSON,
        checked_in
            .strip_suffix('\n')
            .expect("the checked-in JSON is one newline-terminated emitted record"),
        "checked-in JSON payload must equal Lean's pinned emission"
    );
    let parsed = parse_vm_descriptor2(GOLDEN_JSON).expect("Lean bytes parse as IR-v2");
    let dispatched = descriptor_by_name(TURN_CHAIN_BINDING_NAME)
        .expect("the production descriptor registry dispatches the turn-chain artifact");
    assert_eq!(
        parsed, dispatched,
        "dispatch must serve the byte-pinned artifact"
    );
    assert_eq!(parsed.trace_width, TURN_CHAIN_BINDING_WIDTH);
    assert_eq!(parsed.public_input_count, TURN_CHAIN_BINDING_PI_COUNT);
    assert_eq!(parsed.constraints.len(), 14);
    assert_eq!(
        parsed
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count(),
        6
    );
    assert_eq!(
        parsed
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(_)))
            .count(),
        1
    );
    assert_eq!(
        parsed
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count(),
        4
    );
    assert_eq!(
        parsed
            .constraints
            .iter()
            .filter(|c| matches!(
                c,
                VmConstraint2::Base(VmConstraint::Boundary {
                    row: VmRow::First,
                    ..
                })
            ))
            .count(),
        3
    );
}

#[test]
fn production_witness_padding_proves_and_verifies() {
    let desc = descriptor_by_name(TURN_CHAIN_BINDING_NAME).expect("dispatch");
    let (trace, pis) = honest_fixture();
    assert_eq!(trace.len(), 4, "three turns pad to four rows");
    assert!(
        trace
            .iter()
            .all(|row| row.len() == TURN_CHAIN_BINDING_WIDTH)
    );
    let pad = &trace[3];
    assert_eq!(pad[OLD_ROOT], pis[PI_FINAL_ROOT]);
    assert_eq!(
        pad[dregg_circuit::turn_chain_witness::NEW_ROOT],
        pis[PI_FINAL_ROOT]
    );
    assert_eq!(pad[IDX], BabyBear::new(3));
    assert_eq!(pad[IS_REAL], BabyBear::ZERO);
    assert_eq!(pad[REAL_COUNT], BabyBear::new(3));
    assert_eq!(pad[ACC_IN], trace[2][ACC_OUT]);
    assert_eq!(pad[ACC_OUT], pis[PI_CHAIN_DIGEST]);

    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the production witness proves through the Lean-emitted descriptor");
    verify_vm_descriptor2(&desc, &proof, &pis).expect("the production witness proof re-verifies");
}

#[test]
fn forged_history_fixtures_are_rejected() {
    let desc = descriptor_by_name(TURN_CHAIN_BINDING_NAME).expect("dispatch");
    let (trace, pis) = honest_fixture();
    assert!(!rejects(&desc, &trace, &pis), "honest control must accept");

    let mut broken_continuity = trace.clone();
    broken_continuity[1][OLD_ROOT] += BabyBear::ONE;
    assert!(
        rejects(&desc, &broken_continuity, &pis),
        "a broken old/new-root seam must be REJECTED"
    );

    let mut bad_idx = trace.clone();
    bad_idx[2][IDX] += BabyBear::ONE;
    assert!(
        rejects(&desc, &bad_idx, &pis),
        "a broken positional index step must be REJECTED"
    );

    let mut bad_count = pis.clone();
    bad_count[PI_NUM_TURNS] += BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &bad_count),
        "a forged num_turns must be REJECTED"
    );

    let mut bad_final = pis.clone();
    bad_final[PI_FINAL_ROOT] += BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &bad_final),
        "a forged final root must be REJECTED"
    );

    let mut bad_digest = pis.clone();
    bad_digest[PI_CHAIN_DIGEST] += BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &bad_digest),
        "a forged sequential chain digest must be REJECTED"
    );
}
