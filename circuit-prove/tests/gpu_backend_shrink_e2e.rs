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
    create_gpu_outer_config, gpu_shrink_proof_to_cpu, lde_residency_counters,
    recursion_dispatch_counters, recursion_dispatch_profile, shrink_apex_to_gpu_outer,
    verify_gpu_shrink_proof,
};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive, verify_turn_chain_recursive,
    verify_turn_chain_recursive_from_parts,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, recursion_vk_fingerprint, verify_recursive_batch_proof_with_config,
};
use dregg_turn_prover::rotation_witness::mint_rotated_participant_leg;
use p3_field::PrimeCharacteristicRing;

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
#[ignore = "SLOW: real 2-turn fold on CPU + GPU, then CPU + GPU BN254 shrink (~minutes); run with --ignored --nocapture — THE full GPU-prover measurement"]
fn gpu_backend_real_shrink_gpu_vs_cpu_measured() {
    let adapter = dregg_circuit_prove::gpu_backend::GpuDft::default()
        .adapter_name()
        .expect("no GPU adapter — this full-fold gate must run on the GPU lane");
    println!("[e2e] GPU adapter: {adapter}");
    let chain = the_chain();

    // ---- 1a. the REAL apex through the original CPU production path ----
    // This ignored test is always invoked as the sole test filter.  The env
    // override is process-local and restores the normal auto policy below.
    unsafe { std::env::set_var("DREGG_GPU_RECURSION", "cpu") };
    let (gpu_layers0, cpu_layers0) = recursion_dispatch_counters();
    let cpu_profile0 = recursion_dispatch_profile();
    let t0 = Instant::now();
    let cpu_whole = prove_turn_chain_recursive(&chain).expect("the fixed 2-turn chain CPU-folds");
    let cpu_fold_total = t0.elapsed().as_secs_f64();
    let (gpu_layers1, cpu_layers1) = recursion_dispatch_counters();
    let cpu_profile1 = recursion_dispatch_profile();
    assert_eq!(
        gpu_layers1 - gpu_layers0,
        0,
        "forced CPU fold dispatched a GPU layer"
    );
    assert_eq!(
        cpu_layers1 - cpu_layers0,
        3,
        "2-turn CPU fold must dispatch 2 leaves + 1 aggregation"
    );
    println!("[e2e] CPU apex fold (2-turn rotated chain): {cpu_fold_total:.2}s");
    println!(
        "[e2e] CPU recursion dispatch: leaves {:.2}s | aggregation {:.2}s",
        (cpu_profile1.cpu_leaf_ns - cpu_profile0.cpu_leaf_ns) as f64 / 1e9,
        (cpu_profile1.cpu_aggregation_ns - cpu_profile0.cpu_aggregation_ns) as f64 / 1e9,
    );

    let inner_config = ir2_leaf_wrap_config();
    verify_recursive_batch_proof_with_config(&cpu_whole.root.0, &inner_config)
        .expect("the CPU apex verifies under ir2_leaf_wrap_config");

    // ---- 1b. the SAME complete fold through production GPU dispatch ----
    unsafe { std::env::set_var("DREGG_GPU_RECURSION", "gpu") };
    let (gpu_layers0, cpu_layers0) = recursion_dispatch_counters();
    let gpu_profile0 = recursion_dispatch_profile();
    let t_gpu_fold = Instant::now();
    let gpu_whole = prove_turn_chain_recursive(&chain).expect("the fixed 2-turn chain GPU-folds");
    let gpu_fold_total = t_gpu_fold.elapsed().as_secs_f64();
    let (gpu_layers1, cpu_layers1) = recursion_dispatch_counters();
    let gpu_profile1 = recursion_dispatch_profile();
    assert_eq!(
        cpu_layers1 - cpu_layers0,
        0,
        "forced GPU fold dispatched a CPU layer"
    );
    assert_eq!(
        gpu_layers1 - gpu_layers0,
        3,
        "2-turn GPU fold must dispatch 2 leaves + 1 aggregation"
    );
    unsafe { std::env::remove_var("DREGG_GPU_RECURSION") };
    println!(
        "[e2e] GPU recursion dispatch: leaves prepare {:.2}s + prove {:.2}s | aggregation prepare {:.2}s + prove {:.2}s",
        (gpu_profile1.gpu_leaf_prepare_ns - gpu_profile0.gpu_leaf_prepare_ns) as f64 / 1e9,
        (gpu_profile1.gpu_leaf_prove_ns - gpu_profile0.gpu_leaf_prove_ns) as f64 / 1e9,
        (gpu_profile1.gpu_aggregation_prepare_ns - gpu_profile0.gpu_aggregation_prepare_ns) as f64
            / 1e9,
        (gpu_profile1.gpu_aggregation_prove_ns - gpu_profile0.gpu_aggregation_prove_ns) as f64
            / 1e9,
    );

    let cpu_root_bytes =
        postcard::to_allocvec(&cpu_whole.root.0).expect("CPU apex proof serializes");
    let gpu_root_bytes =
        postcard::to_allocvec(&gpu_whole.root.0).expect("GPU apex proof serializes");
    assert!(
        gpu_root_bytes == cpu_root_bytes,
        "production GPU full-fold proof differs from CPU: CPU {} bytes, GPU {} bytes, first difference {:?}",
        cpu_root_bytes.len(),
        gpu_root_bytes.len(),
        cpu_root_bytes
            .iter()
            .zip(&gpu_root_bytes)
            .position(|(cpu, gpu)| cpu != gpu),
    );
    assert_eq!(
        format!("{:?}", gpu_whole.root.0.stark_common.lookups),
        format!("{:?}", cpu_whole.root.0.stark_common.lookups),
        "production GPU fold did not retain the CPU lookup-expression ordering"
    );
    let cpu_vk = cpu_whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&gpu_whole, &cpu_vk)
        .expect("GPU full-fold proof is accepted by the unchanged CPU whole-chain verifier");
    println!(
        "[e2e] FOLD result: CPU {cpu_fold_total:.2}s | GPU {gpu_fold_total:.2}s | {:.2}x; BYTE-IDENTICAL ({} bytes), CPU verifier ACCEPT",
        cpu_fold_total / gpu_fold_total,
        gpu_root_bytes.len(),
    );

    // Full-fold reject polarity: alter one FRI-bound opening in a fresh
    // deserialized copy, then send it through the unchanged CPU verifier.
    let mut tampered_root = postcard::from_bytes::<
        p3_circuit_prover::BatchStarkProof<
            dregg_circuit_prove::plonky3_recursion_impl::recursive::DreggRecursionConfig,
        >,
    >(&gpu_root_bytes)
    .expect("GPU apex proof deserializes as CPU config");
    tampered_root.proof.opened_values.instances[0]
        .base_opened_values
        .trace_local[0] += <dregg_circuit_prove::plonky3_recursion_impl::recursive::DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge::ONE;
    assert!(
        verify_turn_chain_recursive_from_parts(
            &tampered_root,
            &gpu_whole.binding_proof,
            gpu_whole.genesis_root,
            gpu_whole.final_root,
            gpu_whole.chain_digest,
            gpu_whole.num_turns,
            &cpu_vk,
        )
        .is_err(),
        "unchanged CPU verifier accepted a tampered GPU full-fold proof"
    );
    println!("[e2e] full-fold reject polarity: tampered GPU proof REJECTED");

    // ---- 2. CPU shrink (the baseline) ----------------------------------
    let cpu_config = create_outer_config();
    let t1 = Instant::now();
    let cpu_shrink = shrink_apex_to_outer(&cpu_whole.root, &inner_config, &cpu_config)
        .expect("the real apex shrinks under DreggOuterConfig (CPU)");
    let cpu_total = t1.elapsed().as_secs_f64();
    println!("[e2e] CPU shrink total (circuit build + witness gen + prove): {cpu_total:.2}s");
    let cpu_bytes = postcard::to_allocvec(&cpu_shrink.proof).expect("cpu shrink proof serializes");

    // Save the driver-independent CPU baselines before running the GPU side of
    // the gate. If parity catches a backend bug, the expensive CPU result is
    // still reusable by the GPU-only iteration/second-driver test.
    if let Some(dir) = std::env::var_os("DREGG_FULL_FOLD_SAVE_DIR") {
        let dir = std::path::PathBuf::from(dir);
        std::fs::create_dir_all(&dir).expect("create full-fold baseline directory");
        std::fs::write(dir.join("cpu-root.postcard"), &cpu_root_bytes)
            .expect("write CPU root baseline");
        std::fs::write(dir.join("cpu-shrink.postcard"), &cpu_bytes)
            .expect("write CPU shrink baseline");
        std::fs::write(
            dir.join("cpu-seconds.txt"),
            format!("{cpu_fold_total:.9}\n{cpu_total:.9}\n"),
        )
        .expect("write CPU timing baseline");
        println!(
            "[e2e] saved driver-independent CPU baselines at {}",
            dir.display()
        );
    }

    // ---- 3. GPU shrink --------------------------------------------------
    let gpu_config = create_gpu_outer_config();
    let (lde_hits0, lde_misses0) = lde_residency_counters();
    let t2 = Instant::now();
    let gpu_shrink = shrink_apex_to_gpu_outer(&gpu_whole.root, &inner_config, &gpu_config)
        .expect("the real apex shrinks under GpuDreggOuterConfig");
    let gpu_total = t2.elapsed().as_secs_f64();
    println!(
        "[e2e] GPU shrink total: {gpu_total:.2}s  (prepare {:.2}s [config-independent CPU work] + prove {:.2}s [the GPU-accelerated phase])",
        gpu_shrink.prepare_seconds, gpu_shrink.prove_seconds
    );
    let (lde_hits, lde_misses) = lde_residency_counters();
    println!(
        "[e2e] LDE device-residency: {} tree-build matrices fed by device-resident blits, {} by host upload",
        lde_hits - lde_hits0,
        lde_misses - lde_misses0
    );

    // The prepare phase (verifier-circuit build, table-AIR extraction,
    // witness generation) is the IDENTICAL CPU code path in both runs, so
    // the config-dependent prove-phase baseline is cpu_total - prepare.
    let cpu_prove_derived = cpu_total - gpu_shrink.prepare_seconds;
    println!("[e2e] ===== MEASURED RESULT =====");
    println!(
        "[e2e] full pipeline:      CPU {:.2}s | GPU {:.2}s | {:.2}x",
        cpu_fold_total + cpu_total,
        gpu_fold_total + gpu_total,
        (cpu_fold_total + cpu_total) / (gpu_fold_total + gpu_total),
    );
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
    let gpu_bytes = postcard::to_allocvec(&gpu_shrink.proof).expect("gpu shrink proof serializes");
    assert!(
        cpu_bytes == gpu_bytes,
        "GPU shrink proof differs from CPU: CPU {} bytes, GPU {} bytes, first difference {:?}",
        cpu_bytes.len(),
        gpu_bytes.len(),
        cpu_bytes
            .iter()
            .zip(&gpu_bytes)
            .position(|(cpu, gpu)| cpu != gpu),
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

#[test]
#[ignore = "SLOW GPU-only second-driver run; requires DREGG_FULL_FOLD_SAVE_DIR from the complete baseline test"]
fn gpu_backend_full_fold_second_driver_against_saved_cpu() {
    let dir = std::path::PathBuf::from(
        std::env::var_os("DREGG_FULL_FOLD_SAVE_DIR")
            .expect("set DREGG_FULL_FOLD_SAVE_DIR to the first-driver baseline directory"),
    );
    let cpu_root_bytes =
        std::fs::read(dir.join("cpu-root.postcard")).expect("read saved CPU root proof");
    let cpu_shrink_bytes =
        std::fs::read(dir.join("cpu-shrink.postcard")).expect("read saved CPU shrink proof");
    let seconds =
        std::fs::read_to_string(dir.join("cpu-seconds.txt")).expect("read CPU baseline timing");
    let mut seconds = seconds
        .lines()
        .map(|s| s.parse::<f64>().expect("timing is f64"));
    let cpu_fold_total = seconds.next().expect("CPU fold timing present");
    let cpu_shrink_total = seconds.next().expect("CPU shrink timing present");

    let adapter = dregg_circuit_prove::gpu_backend::GpuDft::default()
        .adapter_name()
        .expect("no GPU adapter — this second-driver gate must run on the Navi22");
    println!("[second-driver] GPU adapter: {adapter}");
    let chain = the_chain();
    unsafe { std::env::set_var("DREGG_GPU_RECURSION", "gpu") };
    let profile0 = recursion_dispatch_profile();
    let t_fold = Instant::now();
    let gpu_whole = prove_turn_chain_recursive(&chain).expect("second-driver GPU fold proves");
    let gpu_fold_total = t_fold.elapsed().as_secs_f64();
    let profile1 = recursion_dispatch_profile();
    unsafe { std::env::remove_var("DREGG_GPU_RECURSION") };

    let gpu_root_bytes =
        postcard::to_allocvec(&gpu_whole.root.0).expect("second-driver root serializes");
    assert!(
        gpu_root_bytes == cpu_root_bytes,
        "second-driver GPU root differs from saved CPU: saved {} bytes, GPU {} bytes, first difference {:?}",
        cpu_root_bytes.len(),
        gpu_root_bytes.len(),
        cpu_root_bytes
            .iter()
            .zip(&gpu_root_bytes)
            .position(|(cpu, gpu)| cpu != gpu),
    );
    let cpu_root =
        postcard::from_bytes::<p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>>(
            &cpu_root_bytes,
        )
        .expect("saved CPU root deserializes");
    let cpu_vk = recursion_vk_fingerprint(&cpu_root);
    verify_turn_chain_recursive(&gpu_whole, &cpu_vk)
        .expect("second-driver GPU root verifies under unchanged CPU verifier");

    // Diagnostic stage isolation can be requested without slowing/changing the
    // BabyBear fold above: apply outer-only overrides immediately before the
    // BN254 shrink.
    for (outer_var, stage_var) in [
        ("DREGG_GPU_OUTER_DFT", "DREGG_GPU_DFT"),
        ("DREGG_GPU_OUTER_MMCS", "DREGG_GPU_BN254_MMCS"),
    ] {
        if let Ok(value) = std::env::var(outer_var) {
            unsafe { std::env::set_var(stage_var, &value) };
            println!("[second-driver] {stage_var}={value}");
        }
    }

    let inner_config = ir2_leaf_wrap_config();
    let gpu_config = create_gpu_outer_config();
    let t_shrink = Instant::now();
    let gpu_shrink = shrink_apex_to_gpu_outer(&gpu_whole.root, &inner_config, &gpu_config)
        .expect("second-driver GPU shrink proves");
    let gpu_shrink_total = t_shrink.elapsed().as_secs_f64();
    let gpu_shrink_bytes =
        postcard::to_allocvec(&gpu_shrink.proof).expect("second-driver shrink serializes");
    // Keep the failing artifact when the byte-parity gate fires.  This makes
    // a production-shape backend regression diagnosable without paying for
    // another complete fold merely to recover the GPU transcript.
    std::fs::write(dir.join("gpu-shrink.postcard"), &gpu_shrink_bytes)
        .expect("write GPU shrink diagnostic artifact");
    let as_cpu = gpu_shrink_proof_to_cpu(&gpu_shrink.proof).expect("GPU shrink retags to CPU");
    let cpu_shrink = postcard::from_bytes::<
        p3_circuit_prover::BatchStarkProof<
            dregg_circuit_prove::dregg_outer_config::DreggOuterConfig,
        >,
    >(&cpu_shrink_bytes)
    .expect("saved CPU shrink deserializes");
    macro_rules! same {
        ($left:expr, $right:expr $(,)?) => {
            postcard::to_allocvec($left).expect("serialize CPU component")
                == postcard::to_allocvec($right).expect("serialize GPU component")
        };
    }
    println!(
        "[second-driver] transcript parity: main={} permutation={} quotient={} opened={} fri={}",
        same!(
            &cpu_shrink.proof.commitments.main,
            &as_cpu.proof.commitments.main,
        ),
        same!(
            &cpu_shrink.proof.commitments.permutation,
            &as_cpu.proof.commitments.permutation,
        ),
        same!(
            &cpu_shrink.proof.commitments.quotient_chunks,
            &as_cpu.proof.commitments.quotient_chunks,
        ),
        same!(&cpu_shrink.proof.opened_values, &as_cpu.proof.opened_values),
        same!(&cpu_shrink.proof.opening_proof, &as_cpu.proof.opening_proof),
    );
    assert!(
        gpu_shrink_bytes == cpu_shrink_bytes,
        "second-driver GPU shrink differs from saved CPU: saved {} bytes, GPU {} bytes, first difference {:?}",
        cpu_shrink_bytes.len(),
        gpu_shrink_bytes.len(),
        cpu_shrink_bytes
            .iter()
            .zip(&gpu_shrink_bytes)
            .position(|(cpu, gpu)| cpu != gpu),
    );
    verify_gpu_shrink_proof(&gpu_shrink.proof, &gpu_config)
        .expect("second-driver GPU shrink verifies under GPU config");
    verify_shrink_proof(&as_cpu, &create_outer_config())
        .expect("second-driver GPU shrink verifies under unchanged CPU verifier");
    let mut tampered = gpu_shrink_bytes.clone();
    let mid = tampered.len() / 2;
    tampered[mid] ^= 1;
    if let Ok(bad) = postcard::from_bytes::<
        p3_circuit_prover::BatchStarkProof<dregg_circuit_prove::gpu_backend::GpuDreggOuterConfig>,
    >(&tampered)
    {
        assert!(
            verify_gpu_shrink_proof(&bad, &gpu_config).is_err(),
            "second-driver verifier accepted a tampered shrink proof"
        );
    }

    println!("[second-driver] root parity + CPU verifier: PASS");
    println!(
        "[second-driver] fold: CPU {cpu_fold_total:.2}s | GPU {gpu_fold_total:.2}s | {:.2}x",
        cpu_fold_total / gpu_fold_total,
    );
    println!(
        "[second-driver] GPU recursion: leaves prepare {:.2}s + prove {:.2}s | aggregation prepare {:.2}s + prove {:.2}s",
        (profile1.gpu_leaf_prepare_ns - profile0.gpu_leaf_prepare_ns) as f64 / 1e9,
        (profile1.gpu_leaf_prove_ns - profile0.gpu_leaf_prove_ns) as f64 / 1e9,
        (profile1.gpu_aggregation_prepare_ns - profile0.gpu_aggregation_prepare_ns) as f64 / 1e9,
        (profile1.gpu_aggregation_prove_ns - profile0.gpu_aggregation_prove_ns) as f64 / 1e9,
    );
    println!(
        "[second-driver] full pipeline: CPU {:.2}s | GPU {:.2}s | {:.2}x",
        cpu_fold_total + cpu_shrink_total,
        gpu_fold_total + gpu_shrink_total,
        (cpu_fold_total + cpu_shrink_total) / (gpu_fold_total + gpu_shrink_total),
    );
}

#[test]
#[ignore = "diagnostic: prints the real saved CPU shrink commitment shapes"]
fn saved_cpu_shrink_shape_report() {
    let dir = std::path::PathBuf::from(
        std::env::var_os("DREGG_FULL_FOLD_SAVE_DIR")
            .expect("set DREGG_FULL_FOLD_SAVE_DIR to a complete baseline directory"),
    );
    let bytes = std::fs::read(dir.join("cpu-shrink.postcard")).expect("read CPU shrink proof");
    let proof = postcard::from_bytes::<
        p3_circuit_prover::BatchStarkProof<
            dregg_circuit_prove::dregg_outer_config::DreggOuterConfig,
        >,
    >(&bytes)
    .expect("deserialize CPU shrink proof");
    println!("instance count: {}", proof.proof.degree_bits.len());
    for (i, (degree_bits, opened)) in proof
        .proof
        .degree_bits
        .iter()
        .zip(&proof.proof.opened_values.instances)
        .enumerate()
    {
        println!(
            "instance {i:02}: degree_bits={degree_bits:02} trace_w={} permutation_w={} quotient_chunks={}",
            opened.base_opened_values.trace_local.len(),
            opened.permutation_local.len(),
            opened.base_opened_values.quotient_chunks.len(),
        );
    }
}

#[test]
#[ignore = "diagnostic: compares saved CPU/GPU shrink transcript components"]
fn saved_shrink_transcript_parity_report() {
    type CpuProof = p3_circuit_prover::BatchStarkProof<
        dregg_circuit_prove::dregg_outer_config::DreggOuterConfig,
    >;
    let dir = std::path::PathBuf::from(
        std::env::var_os("DREGG_FULL_FOLD_SAVE_DIR")
            .expect("set DREGG_FULL_FOLD_SAVE_DIR to a complete baseline directory"),
    );
    let cpu_bytes = std::fs::read(dir.join("cpu-shrink.postcard")).expect("read CPU shrink");
    let gpu_bytes = std::fs::read(dir.join("gpu-shrink.postcard")).expect("read GPU shrink");
    let cpu = postcard::from_bytes::<CpuProof>(&cpu_bytes).expect("deserialize CPU shrink");
    // Config types are zero-sized serde markers; the wire proof has exactly
    // the same field representation under the CPU and GPU configs.
    let gpu = postcard::from_bytes::<CpuProof>(&gpu_bytes).expect("deserialize GPU shrink");
    macro_rules! same {
        ($left:expr, $right:expr $(,)?) => {
            postcard::to_allocvec($left).expect("serialize CPU component")
                == postcard::to_allocvec($right).expect("serialize GPU component")
        };
    }
    let cf = &cpu.proof.opening_proof;
    let gf = &gpu.proof.opening_proof;
    println!(
        "commitments: main={} permutation={} quotient={}",
        same!(&cpu.proof.commitments.main, &gpu.proof.commitments.main),
        same!(
            &cpu.proof.commitments.permutation,
            &gpu.proof.commitments.permutation,
        ),
        same!(
            &cpu.proof.commitments.quotient_chunks,
            &gpu.proof.commitments.quotient_chunks,
        ),
    );
    println!(
        "fri: phase_commits={} phase_pow={} final_poly={} query_pow={} queries={}",
        same!(&cf.commit_phase_commits, &gf.commit_phase_commits),
        same!(&cf.commit_pow_witnesses, &gf.commit_pow_witnesses),
        same!(&cf.final_poly, &gf.final_poly),
        same!(&cf.query_pow_witness, &gf.query_pow_witness),
        same!(&cf.query_proofs, &gf.query_proofs),
    );
    println!(
        "query_pow CPU={:?} GPU={:?}",
        cf.query_pow_witness, gf.query_pow_witness
    );
    for (i, (cq, gq)) in cf.query_proofs.iter().zip(&gf.query_proofs).enumerate() {
        if !same!(cq, gq) {
            println!(
                "first divergent query {i}: input={} commit_phase_openings={}",
                same!(&cq.input_proof, &gq.input_proof),
                same!(&cq.commit_phase_openings, &gq.commit_phase_openings),
            );
            break;
        }
    }
}
