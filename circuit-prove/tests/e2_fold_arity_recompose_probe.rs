//! # E2 FOLD-ARITY RECOMPOSE PROBE — go/no-go for the per-turn double-prove deletion
//!
//! **THE QUESTION** (EFFICIENCY-BACKLOG E2, rank 2): every IVC-bound turn is proven TWICE —
//! the production artifact mints under `ir2_config` (log_blowup 6, 19 queries, fold-by-8:
//! `IR2_FRI_MAX_LOG_ARITY = 3`), then `turn/src/rotation_witness.rs:749-762` re-proves the
//! IDENTICAL descriptor/trace/PI vector under `ir2_leaf_wrap_config()` (fold-by-2:
//! `INNER_FRI_MAX_LOG_ARITY = 1`). The ONLY knob separating the two engines is the fold
//! arity, and the arity-2 choice is a still-unresolved DIAGNOSTIC PROBE
//! (`plonky3_recursion_impl.rs:401-411` — "isolate whether higher-arity folding is the
//! obstruction"). The in-circuit verifier reads count/arity from the proof structure, so
//! direct consumption of the arity-8 proof is PLAUSIBLE but was UNEXERCISED: every existing
//! recursion test folds at arity 2.
//!
//! **THE PROBE**: mint one real rotated 3-instance multi-table LogUp transfer leaf
//! (`transferVmDescriptor2R24`, the same fixture as `rotation_batchstark_leaf_smoke.rs`)
//! under a `DreggRecursionConfig` at the FULL production `ir2_config` knobs — including
//! `max_log_arity = 3` — and feed it to the SAME leaf-wrap
//! (`prove_descriptor_leaf_rotated_with_config`). Green ⟹ the recompose path
//! (`p3-recursion::pcs/fri/verifier.rs::reconstruct_evals` + `one_hot_from_bits`, which
//! carry explicit arity-4/8 arms) absorbs a real arity-8 dregg leaf, the fold-by-2 choice
//! was only a diagnostic, and the per-turn re-mint is DELETABLE (the cutover itself is
//! semantic-change and is NOT performed here). Red ⟹ the wall is real; the exact failure is
//! the re-estimate signal.
//!
//! **NON-VACUITY TOOTH**: a tiny trace could go green without ever folding by more than 2.
//! The probe asserts the minted proof's commit-phase schedule actually CONTAINS a step with
//! `log_arity ≥ 2` (the proof carries `log_arity` per `CommitPhaseProofStep`), so the
//! in-circuit verifier demonstrably walked the >2-arity reconstruct path.
//!
//! **BYTE-SAFE**: this file only EXERCISES the mechanism on a throwaway config object. It
//! deletes nothing, re-pins nothing, and touches no deployed descriptor bytes or VK. The
//! soundness half of the E2 decision is ALREADY Lean-proven and is NOT re-derived here:
//! `Dregg2.Circuit.FriLedgerSound.arity8_costs_seven_times_arity2_at_logBlowup6`
//! (#assert_axioms clean) — arity 8 at log_blowup 6 costs EXACTLY 3 per-fold bits
//! (112 → 109, goodCount ×7). The cutover decision goes through `dregg_fri_ledger`, not a
//! comment.
//!
//! **RESULT (2026-07-19): GO — both probes GREEN on first run.** Measured on the real
//! transfer leaf: inner mint arity-2 402,539 B / 8 commit phases (schedule all-[1]) vs
//! arity-8 373,951 B / 4 commit phases (schedule [2,2,3,1] — log_arity 3 present, so the
//! in-circuit arity-8 reconstruct arm demonstrably ran); wrap of the arity-8 leaf GREEN
//! (~50 s, wrapped root 229,594 B, self-verifies in-circuit); aggregation of two arity-8
//! leaves at the probe config GREEN (~52 s, root verifies in-circuit). The fold-by-2 choice
//! was ONLY a diagnostic: nothing in the recompose path rejects the production arity. The
//! per-turn re-mint (`rotation_witness.rs` re-prove) is mechanically deletable — the cutover
//! (flip `INNER_FRI_MAX_LOG_ARITY` 1→3, delete the re-mint, collapse the config-type split,
//! gnark arity-8 `fold_row`) is semantic-change and STAGED, not fired here.
//!
//! Run with:
//! `cargo test -p dregg-circuit-prove --test e2_fold_arity_recompose_probe -- --nocapture`

use std::time::Instant;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    IR2_FRI_LOG_BLOWUP, IR2_FRI_LOG_FINAL_POLY_LEN, IR2_FRI_MAX_LOG_ARITY, IR2_FRI_NUM_QUERIES,
    IR2_FRI_QUERY_POW_BITS, MemBoundaryWitness, UMemBoundaryWitness, parse_vm_descriptor2,
    prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, avail_pad_for_descriptor_name, generate_rotated_effect_vm_trace_avail,
    transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_config_with_fri,
    verify_recursive_batch_proof_with_config,
};
use dregg_turn::rotation_witness as rw;

/// The production `ir2_config` mints with NO commit-phase proof-of-work (the leaf-wrap's
/// `IR2_INNER_COMMIT_POW_BITS` pins the same 0 — `ivc_turn_chain.rs:880`).
const IR2_COMMIT_POW_BITS: usize = 0;

/// **THE PROBE CONFIG** — a `DreggRecursionConfig` whose FRI engine (StarkConfig PCS *and*
/// in-circuit `FriVerifierParams`) sits at the FULL production `ir2_config` knobs, fold
/// arity INCLUDED. This is byte-for-byte `ir2_leaf_wrap_config()` except `max_log_arity`:
/// 3 (fold up to 8/step, the production engine) instead of 1 (fold by 2, the diagnostic).
/// If the E2 cutover happens, THIS is the config the whole rotated chain would run at.
fn arity8_probe_config() -> DreggRecursionConfig {
    assert_eq!(
        IR2_FRI_MAX_LOG_ARITY, 3,
        "the production ir2_config fold arity moved; re-aim the probe"
    );
    create_recursion_config_with_fri(
        IR2_FRI_LOG_BLOWUP,
        IR2_FRI_LOG_FINAL_POLY_LEN,
        IR2_FRI_MAX_LOG_ARITY,
        IR2_FRI_NUM_QUERIES,
        IR2_COMMIT_POW_BITS,
        IR2_FRI_QUERY_POW_BITS,
    )
}

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

/// The rotated transfer fixture: descriptor + (trace, descriptor PIs) — identical to
/// `rotation_batchstark_leaf_smoke.rs` (a real transfer-out over the validated v1
/// reference witness), amount-parameterized so distinct leaves differ.
fn rotated_transfer_fixture(
    amount: u64,
) -> (
    dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
) {
    let desc =
        parse_vm_descriptor2(rotated_transfer_json()).expect("rotated transfer descriptor parses");
    // The deployed transfer member is AVAILABILITY-HARDENED (`…-v1-avail`, pad 10) and
    // gentian-refuse-welded; the generator takes the pad and the prover graduates the base
    // trace (chip lanes + refuse aux) up to `desc.trace_width` internally
    // (`trace_with_chip_lanes`) — no geometry pin here, the prover fails closed on mismatch.
    let pad = avail_pad_for_descriptor_name(&desc.name);

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
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let mk_witness = |cell: &Cell| {
        rw::produce(
            cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        )
    };
    let before_w = mk_witness(&before_cell);
    let after_w = mk_witness(&after_cell);

    let bridge = |w: &rw::RotationWitness| -> RotatedBlockWitness {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
    };
    let caveat = transfer_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace_avail(
        pad,
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("rotated transfer trace generates");
    assert_eq!(
        dpis.len(),
        desc.public_input_count,
        "generator PI count drifted from the committed descriptor"
    );
    (desc, trace, dpis)
}

/// The per-query commit-phase fold schedule (`log_arity` per step) read off the proof, plus
/// the commit-phase commitment count. Every query walks the same schedule (one commitment
/// per phase), so query 0 is representative; asserted below anyway. Concrete over
/// `DreggRecursionConfig`, whose `Pcs::Proof` normalizes to the public-field `FriProof`.
fn fold_schedule(proof: &p3_batch_stark::BatchProof<DreggRecursionConfig>) -> (usize, Vec<u8>) {
    let fri = &proof.opening_proof;
    let schedule: Vec<u8> = fri.query_proofs[0]
        .commit_phase_openings
        .iter()
        .map(|s| s.log_arity)
        .collect();
    for (qi, q) in fri.query_proofs.iter().enumerate() {
        let qs: Vec<u8> = q
            .commit_phase_openings
            .iter()
            .map(|s| s.log_arity)
            .collect();
        assert_eq!(
            qs, schedule,
            "query {qi} walks a different fold schedule than query 0"
        );
    }
    (fri.commit_phase_commits.len(), schedule)
}

/// **THE GO/NO-GO**: does the in-circuit recompose path absorb a REAL arity-8 dregg leaf?
///
/// Mints the rotated transfer `Ir2BatchProof` at the FULL production `ir2_config` knobs
/// (fold-by-8), asserts the proof genuinely folds by >2 (non-vacuity), then wraps it with
/// the UNCHANGED leaf-wrap (`prove_descriptor_leaf_rotated_with_config`) at the probe
/// config and self-verifies the wrapped root in-circuit. Also mints the SAME trace at the
/// current arity-2 wrap config for the size/schedule comparison (the arity-2 WRAP itself is
/// already exercised by `rotation_batchstark_leaf_smoke.rs` — not repeated here).
#[test]
fn rotated_leaf_wraps_at_full_ir2_arity8_knobs() {
    let (desc, trace, dpis) = rotated_transfer_fixture(50);
    let mem_boundary = MemBoundaryWitness::default();
    let umem_boundary = UMemBoundaryWitness::default();

    // -- Mint at the CURRENT wrap config (arity 2) for the comparison row. --
    let arity2_config = ir2_leaf_wrap_config();
    let t0 = Instant::now();
    let arity2_proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &dpis,
        &mem_boundary,
        &[],
        &umem_boundary,
        &arity2_config,
    )
    .expect("rotated transfer proves at the current arity-2 wrap config");
    let arity2_mint = t0.elapsed();
    let (arity2_phases, arity2_schedule) = fold_schedule(&arity2_proof);
    let arity2_bytes = postcard::to_allocvec(&arity2_proof)
        .expect("arity-2 proof serializes")
        .len();

    // -- Mint at the PROBE config (the full production ir2_config knobs, fold-by-8). --
    let probe_config = arity8_probe_config();
    let t0 = Instant::now();
    let probe_proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &dpis,
        &mem_boundary,
        &[],
        &umem_boundary,
        &probe_config,
    )
    .expect("rotated transfer proves at the arity-8 probe config");
    let probe_mint = t0.elapsed();
    let (probe_phases, probe_schedule) = fold_schedule(&probe_proof);
    let probe_bytes = postcard::to_allocvec(&probe_proof)
        .expect("probe proof serializes")
        .len();

    println!(
        "E2 PROBE inner mint: arity-2 {arity2_mint:?} / {arity2_bytes} B / {arity2_phases} commit \
         phases (schedule {arity2_schedule:?}) vs arity-8 {probe_mint:?} / {probe_bytes} B / \
         {probe_phases} commit phases (schedule {probe_schedule:?})"
    );

    // NON-VACUITY: the probe proof must actually fold by more than 2 somewhere, or the wrap
    // below would exercise nothing the existing smoke test does not.
    assert!(
        probe_schedule.iter().any(|&a| a >= 2),
        "probe proof never folds by >2 (schedule {probe_schedule:?}) — the trace is too small \
         to exercise the recompose path at arity >2; the probe is VACUOUS, not green"
    );
    assert!(
        probe_phases < arity2_phases,
        "arity-8 minting did not shorten the commit phase ({probe_phases} vs {arity2_phases}) — \
         the config knob did not take"
    );

    verify_vm_descriptor2_with_config(&desc, &probe_proof, &dpis, &probe_config)
        .expect("probe proof verifies natively at the probe config");

    // -- THE PROBE ITSELF: the unchanged leaf-wrap over the arity-8 proof. --
    let t0 = Instant::now();
    let wrapped = dregg_circuit_prove::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config(
        &desc,
        &probe_proof,
        &dpis,
        &probe_config,
    )
    .expect(
        "E2 GO/NO-GO = NO-GO: the rotated arity-8 (production ir2_config knobs) leaf does NOT \
         wrap — the in-circuit recompose path rejects fold arity >2; the failure text above is \
         the re-estimate signal",
    );
    let wrap_time = t0.elapsed();
    let wrapped_bytes = postcard::to_allocvec(&wrapped.0)
        .expect("wrapped root serializes")
        .len();
    println!(
        "E2 PROBE wrap: arity-8 leaf wrapped in {wrap_time:?}, wrapped root {wrapped_bytes} B"
    );

    verify_recursive_batch_proof_with_config(&wrapped.0, &probe_config)
        .expect("the wrapped arity-8 leaf root verifies in-circuit at the probe config");
}

/// **THE ESCALATION HALF**: two arity-8 leaves AGGREGATE at the probe config (the C4-probe
/// shape, `rotation_batchstark_leaf_smoke.rs::two_rotated_leaves_aggregate_at_wrap_config`,
/// re-run at fold-by-8). The E2 cutover runs the WHOLE rotated chain — binding leaf +
/// aggregation tree — at one config, so the go needs the aggregation layer to fold
/// arity-8 children too, not just the leaf wrap.
#[test]
fn two_arity8_leaves_aggregate_at_probe_config() {
    use dregg_circuit_prove::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_recursion::{BatchOnly, ProveNextLayerParams, build_and_prove_aggregation_layer};

    let probe_config = arity8_probe_config();
    let mem_boundary = MemBoundaryWitness::default();
    let umem_boundary = UMemBoundaryWitness::default();

    let mint_leaf = |amount: u64| {
        let (desc, trace, dpis) = rotated_transfer_fixture(amount);
        let proof = prove_vm_descriptor2_for_config(
            &desc,
            &trace,
            &dpis,
            &mem_boundary,
            &[],
            &umem_boundary,
            &probe_config,
        )
        .expect("rotated transfer proves at the probe config");
        let (_, schedule) = fold_schedule(&proof);
        assert!(
            schedule.iter().any(|&a| a >= 2),
            "leaf proof never folds by >2 — vacuous"
        );
        dregg_circuit_prove::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config(
            &desc,
            &proof,
            &dpis,
            &probe_config,
        )
        .expect("arity-8 rotated leaf wraps at the probe config")
    };

    let left_out = mint_leaf(50);
    let right_out = mint_leaf(70);

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();
    // ⚑ VK-identity pinned, as every 2-to-1 fold in this crate now is (`fold_vk_pin`).
    let pins = dregg_circuit_prove::fold_vk_pin::FoldVkPins::tracked(&left_out, &right_out)
        .expect("both probe leaves carry a preprocessed commitment");
    let left = left_out.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right = right_out.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let t0 = Instant::now();
    let agg =
        build_and_prove_aggregation_layer::<DreggRecursionConfig, BatchOnly, BatchOnly, _, 4>(
            &left,
            &right,
            &probe_config,
            &backend,
            &params,
            None,
        )
        .expect(
            "E2 ESCALATION = NO-GO: two arity-8 rotated leaves do NOT aggregate at the probe \
             config — the aggregation layer rejects arity-8 children",
        );
    println!(
        "E2 PROBE aggregation: two arity-8 leaves aggregated in {:?}",
        t0.elapsed()
    );
    verify_recursive_batch_proof_with_config(&agg.0, &probe_config)
        .expect("the aggregated arity-8 root verifies in-circuit at the probe config");
}
