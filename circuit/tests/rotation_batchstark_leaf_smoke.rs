//! # C3 THREAD-1 SMOKE FOLD — does a rotated `Ir2BatchProof` wrap as a BatchStark leaf?
//!
//! The C3 cutover ("delete v1") drives OPTION (a): make the recursion/aggregation layer
//! ingest the rotated multi-table `Ir2BatchProof` instead of the v1 186-col uni-STARK
//! (`EffectVmDescriptorAir`) leaf. The scope verdict demands ONE smoke fold FIRST: feed a
//! single real rotated 9-table descriptor leaf (chip degree-7 S-box + LogUp buses) through
//! `build_and_prove_next_layer` as a `RecursionInput::BatchStark` leaf and observe whether
//! the recursion circuit's table-packing/constraint-profile absorbs it.
//!
//! This test produces a real `transferVmDescriptor2R24` `Ir2BatchProof` (the SAME fixture as
//! `effect_vm_rotation_flip.rs`) and hands it to
//! `dregg_circuit::ivc_turn_chain::prove_descriptor_leaf_rotated` (THREAD 1's BatchStark
//! leaf-wrap). If it folds, OPTION (a) is confirmed bounded end-to-end; if it does not, the
//! exact failure is the re-estimate signal.
//!
//! Gated on `recursion`. SLOW; run with
//! `cargo test -p dregg-circuit --features recursion batchstark_leaf_smoke -- --nocapture`.

#![cfg(feature = "prover")]

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, UMemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::effect_vm::trace_rotated::{
    ROT_WIDTH, RotatedBlockWitness, generate_rotated_effect_vm_trace, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::ivc_turn_chain::ir2_leaf_wrap_config;
use dregg_circuit::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, verify_recursive_batch_proof_with_config,
};
use dregg_turn::rotation_witness as rw;

fn rotated_transfer_json() -> &'static str {
    for line in V3_STAGED_REGISTRY_TSV.lines() {
        let mut it = line.splitn(3, '\t');
        if it.next() == Some("transferVmDescriptor2R24") {
            let _name = it.next();
            return it.next().expect("json column");
        }
    }
    panic!("transferVmDescriptor2R24 not in V3_STAGED_REGISTRY_TSV");
}

fn open_permissions() -> Permissions {
    Permissions {
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

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// THE SMOKE FOLD: a real rotated transfer leaf wrapped as a NativeBatchStark recursion leaf.
///
/// GREEN (2026-06-13): a real rotated 3-instance multi-table LogUp descriptor leaf (main w=331 /
/// 38 PV / 50 global lookups · chip w=364 / 2 global · byte w=2 / 1 global) now folds as a
/// `RecursionInput::NativeBatchStark` leaf AND the wrapped root self-verifies in-circuit. All
/// three walls of the C3 leaf-wrap are crossed: (1) the proof-type wall (bare
/// `p3_batch_stark::BatchProof` + caller `&[Ir2Air]` ride the native-batch entry), (2) the
/// config wall (inner proof + verifier + output at ONE FRI engine, FRI MMCS verifies
/// in-circuit), and (3) the foreign-multi-table-LogUp-leaf `WitnessChecks` accounting wall —
/// the recursion verifier circuit's own LogUp bus was unbalanced (net +779 on the all-zero
/// tuple) because a descriptor public input asserted equal to the zero constant gave
/// `WitnessId(0)` TWO bus creators (the zero `Const` AND a `Public` op). The fork now demotes
/// such a duplicate `Public` to a bus READER (see `PreprocessedColumns::dup_public_outputs`),
/// restoring the one-creator-per-witness invariant.
#[test]
fn rotated_transfer_leaf_folds_as_batchstark() {
    let desc =
        parse_vm_descriptor2(rotated_transfer_json()).expect("rotated transfer descriptor parses");
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 311");
    assert_eq!(desc.public_input_count, 38, "34 v1 PIs + 4 appended");

    // -- a real transfer-out (the validated v1 reference witness). --
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    let bridge = |w: &rw::RotationWitness| -> RotatedBlockWitness {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
    };
    let caveat = transfer_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("rotated transfer trace generates");

    // -- THE SIDESTEP: mint the rotated batch under the leaf-wrap config (a
    //    `DreggRecursionConfig` whose FRI engine = `ir2_config`'s knobs: log_blowup 6,
    //    max_log_arity 3, 19 queries, 16 query-PoW). The proof is a
    //    `BatchProof<DreggRecursionConfig>` the in-circuit verifier consumes with no
    //    cross-config type mismatch, and minted at the SAME FRI engine the verifier circuit
    //    interprets. Self-verifies natively under the same config. --
    let wrap_config = ir2_leaf_wrap_config();
    let mem_boundary = MemBoundaryWitness::default();
    let umem_boundary = UMemBoundaryWitness::default();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &dpis,
        &mem_boundary,
        &[],
        &umem_boundary,
        &wrap_config,
    )
    .expect("rotated transfer Ir2BatchProof proves under the leaf-wrap config");
    verify_vm_descriptor2_with_config(&desc, &proof, &dpis, &wrap_config)
        .expect("rotated transfer proof verifies natively under the leaf-wrap config");

    // -- THE SMOKE FOLD: wrap the multi-table native batch proof as a NativeBatchStark leaf. --
    //
    // GREEN (2026-06-13): all three walls are crossed —
    //   1. proof-type: the bare `p3_batch_stark::BatchProof` + caller `&[Ir2Air]` ride the
    //      `RecursionInput::NativeBatchStark` variant (allocating verifier inputs straight from
    //      the bare batch via `BatchStarkVerifierInputsBuilder::allocate`, running the generic
    //      `verify_batch_circuit`) — NOT the `CircuitTablesAir` reconstruction;
    //   2. config: inner proof + in-circuit verifier + output all run at ONE FRI engine (the
    //      leaf-wrap config), so the FRI Merkle path lengths match and FRI MMCS verification
    //      PASSES in-circuit;
    //   3. WitnessChecks accounting: the recursion verifier circuit's own LogUp bus now balances
    //      for a FOREIGN multi-table LogUp leaf. The earlier net-+779 imbalance on the all-zero
    //      tuple was a descriptor public input asserted equal to the zero constant, which gave
    //      `WitnessId(0)` two bus creators (the zero `Const` + a `Public`). The fork now demotes
    //      the duplicate `Public` to a bus reader (`PreprocessedColumns::dup_public_outputs`),
    //      restoring one-creator-per-witness; upstream's debug `check_lookups` passes.
    let wrapped = dregg_circuit::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config(
        &desc,
        &proof,
        &dpis,
        &wrap_config,
    )
    .expect("the rotated multi-table LogUp leaf folds as a NativeBatchStark recursion leaf");
    verify_recursive_batch_proof_with_config(&wrapped.0, &wrap_config)
        .expect("the wrapped native-batch leaf root proof verifies in-circuit");
}

/// C4 GATE PROBE — can two rotated leaves AGGREGATE at the leaf-wrap config?
///
/// The C3 smoke (above) wraps ONE rotated leaf and self-verifies it. C4's recursion rewire
/// (`prove_chain_core` / `prove_joint_core`) must AGGREGATE the rotated leaves up a binary tree
/// to one root. The rotated leaf-wrap OUTPUT is minted at `ir2_leaf_wrap_config` (log_blowup 6,
/// 19 queries — the self-consistent FRI engine the inner `Ir2BatchProof` rides), NOT the chain's
/// standard `create_recursion_config` (log_blowup 3, 38 queries). So a rotated leaf CANNOT be
/// aggregated under the standard config (the in-circuit FRI verifier params would mismatch the
/// child's FRI engine). THE QUESTION this probe settles: does `build_and_prove_aggregation_layer`
/// fold two rotated-leaf outputs when run at `ir2_leaf_wrap_config` itself? If GREEN, C4's
/// recursion leg is mechanical (run the whole chain — binding leaf + aggregation — at the wrap
/// config). If it fails, the wall is real and needs a config-lift re-wrap or a fork change.
#[test]
fn two_rotated_leaves_aggregate_at_wrap_config() {
    use dregg_circuit::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_recursion::{BatchOnly, ProveNextLayerParams, build_and_prove_aggregation_layer};

    let desc =
        parse_vm_descriptor2(rotated_transfer_json()).expect("rotated transfer descriptor parses");
    let wrap_config = ir2_leaf_wrap_config();

    // Mint two rotated transfer leaves (distinct amounts so the proofs differ).
    let mint_leaf = |amount: u64| {
        let before_balance: i64 = 100_000;
        let st = CellState::new(before_balance as u64, 0);
        let effects = vec![Effect::Transfer {
            amount,
            direction: 1,
        }];
        let mut ledger = Ledger::new();
        let before_cell = producer_cell(before_balance, 0);
        let after_cell = producer_cell(before_balance - amount as i64, 0);
        ledger.insert_cell(after_cell.clone()).unwrap();
        let nullifier_root = [0u8; 32];
        let commitments_root = [0u8; 32];
        let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
        let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
        let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
        let bridge = |w: &rw::RotationWitness| -> RotatedBlockWitness {
            RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
        };
        let caveat = transfer_caveat_manifest();
        let (trace, dpis) = generate_rotated_effect_vm_trace(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &caveat,
        )
        .expect("rotated transfer trace generates");
        let mem_boundary = MemBoundaryWitness::default();
        let umem_boundary = UMemBoundaryWitness::default();
        let proof = prove_vm_descriptor2_for_config(
            &desc,
            &trace,
            &dpis,
            &mem_boundary,
            &[],
            &umem_boundary,
            &wrap_config,
        )
        .expect("rotated transfer proves under wrap config");
        dregg_circuit::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config(
            &desc,
            &proof,
            &dpis,
            &wrap_config,
        )
        .expect("rotated leaf folds")
    };

    let left_out = mint_leaf(50);
    let right_out = mint_leaf(70);

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();
    let left = left_out.into_recursion_input::<BatchOnly>();
    let right = right_out.into_recursion_input::<BatchOnly>();

    let agg =
        build_and_prove_aggregation_layer::<DreggRecursionConfig, BatchOnly, BatchOnly, _, 4>(
            &left,
            &right,
            &wrap_config,
            &backend,
            &params,
            None,
        )
        .expect("two rotated leaves aggregate at the wrap config");
    verify_recursive_batch_proof_with_config(&agg.0, &wrap_config)
        .expect("the aggregated root verifies in-circuit at the wrap config");
}
