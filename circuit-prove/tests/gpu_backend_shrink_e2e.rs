//! THE GPU-PROVER MEASUREMENT: a REAL `ir2_leaf_wrap` apex proof, shrunk
//! BN254-native under BOTH configs — the CPU `DreggOuterConfig` and the
//! GPU-backed `GpuDreggOuterConfig` — head-to-head wall-clock, with the
//! strongest possible parity gate: the two shrink proofs must be
//! BYTE-IDENTICAL, and the GPU-minted proof must round-trip through the
//! UNCHANGED CPU `verify_shrink_proof`.
//!
//! This is the same real fixture as `apex_shrink_bn254_tooth.rs` (a 2-turn
//! rotated transfer chain folded to an apex), plus the GPU lane.
//!
//! Real folds + two shrink proving runs take minutes; `#[ignore]`, run with:
//!   cargo test -p dregg-circuit-prove --release --test gpu_backend_shrink_e2e -- --ignored --nocapture

use std::time::Instant;

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::apex_shrink::{shrink_apex_to_outer, verify_shrink_proof};
use dregg_circuit_prove::dregg_outer_config::create_outer_config;
use dregg_circuit_prove::gpu_backend::{
    create_gpu_outer_config, gpu_shrink_proof_to_cpu, shrink_apex_to_gpu_outer,
    verify_gpu_shrink_proof,
};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::verify_recursive_batch_proof_with_config;
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

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

fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// One `IncrementNonce` turn — the `apex_shrink_gnark_fixture.rs` /
/// `apex_shrink_blowup_sweep.rs` fixture. (The tooth's `Effect::Transfer`
/// body currently fails host admission mid-flag-day — GAP #4 wide-registry
/// cutover, see the HONEST LABEL in `apex_shrink_gnark_fixture.rs`; the apex
/// is equally real either way, and this measurement only needs a real apex.)
fn make_turn(balance: u64, nonce: u32) -> FinalizedTurn {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::IncrementNonce];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell(balance as i64, nonce as u64);
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        None,
    )
    .expect("rotated leg mints");
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

fn the_chain() -> Vec<FinalizedTurn> {
    vec![make_turn(1000, 0), make_turn(1000, 1)]
}

#[test]
#[ignore = "SLOW: one real 2-turn fold + TWO BN254-native-hash shrink proves (CPU + GPU, ~minutes); run with --ignored --nocapture — THE GPU-prover measurement"]
fn gpu_backend_real_shrink_gpu_vs_cpu_measured() {
    // ---- 1. the REAL apex ---------------------------------------------
    let t0 = Instant::now();
    let whole = prove_turn_chain_recursive(&the_chain()).expect("the fixed 2-turn chain folds");
    let apex_time = t0.elapsed();
    println!("[e2e] apex fold (2-turn rotated chain): {apex_time:.2?}");

    let inner_config = ir2_leaf_wrap_config();
    verify_recursive_batch_proof_with_config(&whole.root.0, &inner_config)
        .expect("the real apex verifies under ir2_leaf_wrap_config");

    // ---- 2. CPU shrink (the baseline) ----------------------------------
    let cpu_config = create_outer_config();
    let t1 = Instant::now();
    let cpu_shrink = shrink_apex_to_outer(&whole.root, &inner_config, &cpu_config)
        .expect("the real apex shrinks under DreggOuterConfig (CPU)");
    let cpu_total = t1.elapsed().as_secs_f64();
    println!("[e2e] CPU shrink total (circuit build + witness gen + prove): {cpu_total:.2}s");

    // ---- 3. GPU shrink --------------------------------------------------
    let gpu_config = create_gpu_outer_config();
    let t2 = Instant::now();
    let gpu_shrink = shrink_apex_to_gpu_outer(&whole.root, &inner_config, &gpu_config)
        .expect("the real apex shrinks under GpuDreggOuterConfig");
    let gpu_total = t2.elapsed().as_secs_f64();
    println!(
        "[e2e] GPU shrink total: {gpu_total:.2}s  (prepare {:.2}s [config-independent CPU work] + prove {:.2}s [the GPU-accelerated phase])",
        gpu_shrink.prepare_seconds, gpu_shrink.prove_seconds
    );

    // The prepare phase (verifier-circuit build, table-AIR extraction,
    // witness generation) is the IDENTICAL CPU code path in both runs, so
    // the config-dependent prove-phase baseline is cpu_total - prepare.
    let cpu_prove_derived = cpu_total - gpu_shrink.prepare_seconds;
    println!("[e2e] ===== MEASURED RESULT =====");
    println!(
        "[e2e] shrink e2e total:   CPU {cpu_total:.2}s | GPU {gpu_total:.2}s | {:.2}x",
        cpu_total / gpu_total
    );
    println!(
        "[e2e] prove phase only:   CPU ~{cpu_prove_derived:.2}s (derived: total - shared prepare) | GPU {:.2}s | {:.2}x",
        gpu_shrink.prove_seconds,
        cpu_prove_derived / gpu_shrink.prove_seconds
    );

    // ---- 4. the strongest parity gate: BYTE-IDENTICAL proofs ------------
    let cpu_bytes = postcard::to_allocvec(&cpu_shrink.proof).expect("cpu shrink proof serializes");
    let gpu_bytes = postcard::to_allocvec(&gpu_shrink.proof).expect("gpu shrink proof serializes");
    assert_eq!(
        cpu_bytes, gpu_bytes,
        "GPU shrink proof is not byte-identical to the CPU shrink proof"
    );
    println!(
        "[e2e] parity: GPU and CPU shrink proofs are BYTE-IDENTICAL ({} bytes)",
        gpu_bytes.len()
    );

    // ---- 5. round-trip: both verifiers accept ---------------------------
    let t3 = Instant::now();
    verify_gpu_shrink_proof(&gpu_shrink.proof, &gpu_config)
        .expect("GPU shrink proof verifies under the GPU config");
    let as_cpu =
        gpu_shrink_proof_to_cpu(&gpu_shrink.proof).expect("GPU proof re-types to the CPU config");
    verify_shrink_proof(&as_cpu, &cpu_config)
        .expect("GPU-minted shrink proof verifies under the UNCHANGED CPU verifier");
    println!(
        "[e2e] round-trip: GPU proof ACCEPTED by both verifiers ({:.2?})",
        t3.elapsed()
    );

    // ---- 6. REJECT polarity (the accept is not vacuous) ------------------
    let mut tampered = gpu_bytes.clone();
    let mid = tampered.len() / 2;
    tampered[mid] ^= 0x01;
    if let Ok(bad) = postcard::from_bytes::<
        p3_circuit_prover::BatchStarkProof<dregg_circuit_prove::gpu_backend::GpuDreggOuterConfig>,
    >(&tampered)
    {
        assert!(
            verify_gpu_shrink_proof(&bad, &gpu_config).is_err(),
            "tampered shrink proof accepted"
        );
        println!("[e2e] reject polarity: tampered proof REJECTED");
    } else {
        println!("[e2e] reject polarity: tampered bytes fail to even deserialize (also a reject)");
    }
}
