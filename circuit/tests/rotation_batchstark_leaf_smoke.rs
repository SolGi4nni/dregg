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

#![cfg(feature = "recursion")]

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, UMemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::ivc_turn_chain::ir2_leaf_wrap_config;
use dregg_circuit::plonky3_recursion_impl::recursive::verify_recursive_batch_proof_with_config;
use dregg_circuit::effect_vm::trace_rotated::{
    ROT_WIDTH, RotatedBlockWitness, generate_rotated_effect_vm_trace, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
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
/// `#[ignore]`: the two TYPE walls of the prior pass are crossed (the native-batch leaf-wrap
/// compiles, runs, builds the in-circuit verifier, and PASSES FRI MMCS verification), but a
/// REMAINING SEMANTIC wall panics inside `prove_all_tables` — the recursion verifier circuit's
/// own `WitnessChecks` LogUp bus is unbalanced (net +779, config/arity-INDEPENDENT) when the
/// wrapped leaf is a multi-table native batch carrying BOTH per-instance public values AND
/// cross-table global LogUp lookups. Ignored (not deleted) so it stays compiled as the exact
/// reproduction; run with `--ignored` to reproduce the wall. Remove `#[ignore]` + assert green
/// when the fork closes the foreign-multi-table-LogUp-leaf accounting.
#[test]
#[ignore = "C3 native-batch leaf-wrap: in-circuit WitnessChecks imbalance (+779) for a \
            multi-table global-LogUp leaf; type walls crossed, FRI verifies; see fn doc"]
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
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &receipt_log);

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
    // PROGRESS (2026-06-13): the prior pass's TWO walls are CROSSED —
    //   1. proof-type: the bare `p3_batch_stark::BatchProof` + caller `&[Ir2Air]` ride the NEW
    //      `RecursionInput::NativeBatchStark` variant (allocating verifier inputs straight from
    //      the bare batch via `BatchStarkVerifierInputsBuilder::allocate`, running the generic
    //      `verify_batch_circuit`) — NOT the `CircuitTablesAir` reconstruction;
    //   2. config: inner proof + in-circuit verifier + output all run at ONE FRI engine (the
    //      leaf-wrap config), so the FRI Merkle path lengths match (the "siblings vs op_ids"
    //      wall is gone, and FRI MMCS verification PASSES in-circuit).
    //
    // REMAINING WALL (precise, config/arity-INDEPENDENT — identical net +779 under FRI arity 1
    // and 3): the recursion verifier circuit's own `WitnessChecks` LogUp bus is UNBALANCED
    // (net +779 on the all-zero tuple) when the wrapped leaf is a multi-table native batch with
    // BOTH per-instance public values AND cross-table global LogUp lookups (transfer = 3
    // instances: main w=331/38 PV/50 global lookups, chip w=364/2 global, byte w=2/1 global).
    // This is the blanket `RecursiveAir::eval_folded_circuit` + `verify_batch_circuit` path
    // applied to a FOREIGN multi-table LogUp STARK as a recursion leaf — validated in the fork
    // only for recursion-circuit-shaped AIRs (Const/Public/Alu), not yet for this. The panic is
    // `p3_lookup::debug_util::check_lookups` inside `prove_all_tables` (the verifier circuit's
    // OWN witness graph), reached from `build_and_prove_next_layer`.
    //
    // When the fork closes the global-lookup-leaf accounting, flip this to assert the leaf
    // folds + the wrapped root self-verifies (the two commented lines below are the green form).
    let folded = dregg_circuit::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config(
        &desc, &proof, &dpis, &wrap_config,
    );
    match folded {
        Ok(wrapped) => {
            verify_recursive_batch_proof_with_config(&wrapped.0, &wrap_config)
                .expect("the wrapped native-batch leaf root proof verifies in-circuit");
            // GREEN: the global-lookup-leaf wall lifted. (If this branch runs, update the doc
            // on `prove_descriptor_leaf_rotated` + delete the panic arms below.)
        }
        Err(e) => panic!("native-batch leaf-wrap returned Err (expected the in-circuit \
                          WitnessChecks panic, not a clean Err): {e}"),
    }
}
