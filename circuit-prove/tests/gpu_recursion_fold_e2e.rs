//! THE FOLD, END-TO-END ON GPU: a REAL recursion layer (the in-circuit STARK
//! verifier over a `P3MerklePoseidon2Air` inner proof — the canonical recursion
//! leaf the whole-chain fold wraps) PROVED under the GPU fold config
//! (`GpuDreggRecursionConfig`: `GpuDft` + `GpuBabyBearMmcs` behind the two
//! `TwoAdicFriPcs` seams), and shown BYTE-IDENTICAL to the CPU fold path.
//!
//! This completes the GPU proving stack the prior lane left at stage level
//! (`gpu_babybear_merkle_e2e.rs` measured the Merkle+DFT COMMIT stages
//! byte-identical; this measures the WHOLE fold layer end-to-end):
//!
//! 1. mint a real inner uni-STARK proof (`P3MerklePoseidon2Air`, degree-7, the
//!    real recursion leaf shape) under the recursion FRI engine;
//! 2. wrap it in the recursion verifier circuit and prove that layer TWICE:
//!    once via the recursion library's `build_and_prove_next_layer` (the REAL
//!    CPU fold path), once via `prove_recursion_layer_gpu` (GPU fold config);
//! 3. assert the GPU proof is BYTE-IDENTICAL to the real CPU fold proof (both
//!    provers deterministic + the GPU path bit-exact); round-trip the GPU proof
//!    into `BatchStarkProof<DreggRecursionConfig>` and VERIFY it under the
//!    UNTOUCHED CPU verifier (`verify_recursive_batch_proof`);
//! 4. tamper one opened value — REJECT (the accept in step 3 is not vacuous);
//! 5. MEASURE the config-dependent PROVE phase (the GPU lever) CPU vs GPU, plus
//!    the whole-layer wall clock, parity re-asserted.
//!
//! This uses NO effect_vm rotated-descriptor leaf, so it is unaffected by the
//! concurrent descriptor-regen flag-day — a fully real fold layer that runs
//! today. (The full 2-turn `prove_turn_chain_recursive` apex adds fixed-cost
//! fold layers of the SAME shape on top; see the report for the honest scope.)
//!
//! GPU + slow (compiles + proves a verifier circuit twice); run LOCALLY on a
//! Metal box (persvati/hbox have no GPU):
//!   cargo test -p dregg-circuit-prove --release --test gpu_recursion_fold_e2e -- --ignored --nocapture

use std::time::Instant;

use dregg_circuit::field::BabyBear;
use dregg_circuit::plonky3_prover::{P3MerklePoseidon2Air, generate_sound_merkle_trace, to_p3};
use dregg_circuit::poseidon2_air::create_poseidon2_test_witness;
use dregg_circuit_prove::gpu_backend::{
    create_gpu_recursion_config, gpu_recursion_proof_to_cpu, prove_recursion_layer_cpu,
    prove_recursion_layer_gpu, verify_gpu_recursion_layer,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend, create_recursion_config, prove_for_recursion,
    verify_for_recursion, verify_recursive_batch_proof,
};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_recursion::{ProveNextLayerParams, RecursionInput, build_and_prove_next_layer};

const D: usize = 4;

#[test]
#[ignore = "GPU + slow: real recursion layer proved twice (~tens of seconds); run with --ignored --nocapture on a Metal box"]
fn real_fold_layer_byte_identical_on_gpu_and_measured() {
    // Fail loudly if no GPU: this gate must run on the GPU lane (a CPU-only run
    // would silently measure CPU-vs-CPU and report a bogus 1.0x).
    let gpu_config = create_gpu_recursion_config();
    // Touch the DFT device so a missing adapter is caught here, not hidden as a
    // silent CPU fallback deep in the prove.
    assert!(
        dregg_circuit_prove::gpu_backend::GpuDft::default()
            .adapter_name()
            .is_some(),
        "no GPU adapter — this end-to-end fold gate must run on the GPU lane"
    );
    let cpu_config = create_recursion_config();

    // ---- 1. a REAL inner proof: P3MerklePoseidon2Air over a sound Merkle trace
    let leaf = BabyBear::new(42424242);
    let witness = create_poseidon2_test_witness(leaf, 4);
    let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
    let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
    let (trace, public_inputs) = generate_sound_merkle_trace(leaf, &siblings, &positions);
    let inner_proof = prove_for_recursion(&trace, &public_inputs);
    verify_for_recursion(&inner_proof, &public_inputs).expect("inner proof verifies");

    // The wrap input — ONE object consumed by BOTH the CPU and GPU layer paths.
    let air = P3MerklePoseidon2Air;
    let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    let input = RecursionInput::UniStark {
        proof: &inner_proof,
        air: &air,
        public_inputs: p3_public,
        preprocessed_commit: None,
    };

    // ---- 2a. CPU (the REAL fold path): recursion library build+prove --------
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();
    let t = Instant::now();
    let cpu_library = build_and_prove_next_layer::<DreggRecursionConfig, _, _, D>(
        &input,
        &cpu_config,
        &backend,
        &params,
    )
    .expect("CPU fold layer proves via the recursion library");
    let cpu_library_total = t.elapsed().as_secs_f64();

    // ---- 2b. CPU (prepare/prove-split twin, for a clean prove-phase number) --
    let cpu = prove_recursion_layer_cpu(&input, &cpu_config, &cpu_config)
        .expect("CPU fold layer proves (split path)");

    // ---- 2c. GPU: the SAME layer under the GPU fold config ------------------
    let gpu = prove_recursion_layer_gpu(&input, &cpu_config, &gpu_config)
        .expect("GPU fold layer proves under GpuDreggRecursionConfig");

    // ---- 3. PARITY: byte-identical to the REAL CPU fold proof ---------------
    let cpu_lib_bytes =
        postcard::to_allocvec(&cpu_library.0).expect("cpu library proof serializes");
    let cpu_split_bytes = postcard::to_allocvec(&cpu.proof).expect("cpu split proof serializes");
    let gpu_bytes = postcard::to_allocvec(&gpu.proof).expect("gpu proof serializes");

    assert_eq!(
        cpu_split_bytes, cpu_lib_bytes,
        "the split CPU path diverged from the recursion library's fold proof"
    );
    assert_eq!(
        gpu_bytes, cpu_lib_bytes,
        "GPU fold-layer proof is NOT byte-identical to the real CPU fold proof"
    );

    // The GPU proof verifies under the GPU config...
    verify_gpu_recursion_layer(&gpu.proof, &gpu_config)
        .expect("GPU fold-layer proof verifies under the GPU config");

    // ...and round-trips into a CPU-config proof the UNTOUCHED CPU verifier
    // accepts (the next fold layer / the in-circuit recursion verifier consumes
    // it unchanged).
    let as_cpu =
        gpu_recursion_proof_to_cpu(&gpu.proof).expect("gpu proof re-tags to the CPU config");
    let as_cpu_bytes = postcard::to_allocvec(&as_cpu).expect("retagged proof serializes");
    assert_eq!(as_cpu_bytes, cpu_lib_bytes, "re-tag changed the bytes");
    verify_recursive_batch_proof(&as_cpu)
        .expect("GPU-minted fold-layer proof verifies under the untouched CPU verifier");

    // ---- 4. REJECT: a tampered opened value must not verify -----------------
    // (move `as_cpu` in — `BatchStarkProof` is not `Clone`, and it is unused
    // after this point.)
    let mut tampered = as_cpu;
    tampered.proof.opened_values.instances[0]
        .base_opened_values
        .trace_local[0] +=
        <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge::ONE;
    assert!(
        verify_recursive_batch_proof(&tampered).is_err(),
        "the CPU verifier accepted a tampered GPU fold proof — the ACCEPT above is vacuous"
    );

    // ---- committed table heights (documents the regime this layer commits) --
    // GpuDft engages at height >= 2^12. The fold layer commits several matrices
    // (the primitive Witness/Public/ALU tables + the non-primitive poseidon2 /
    // recompose / expose_claim tables), each LDE'd + Merkle-committed under the
    // GPU PCS; the aggregate LDE+hash work is what the GPU accelerates.
    println!("\n-- committed table heights (GpuDft engages at >= 2^12) --");
    println!("  primitive tables (rows): {:?}", gpu.proof.rows);
    let mut max_h = 0usize;
    for np in &gpu.proof.non_primitives {
        max_h = max_h.max(np.rows);
        println!(
            "  non-primitive {:?}: {} rows (~2^{:.1})",
            np.op_type,
            np.rows,
            (np.rows.max(1) as f64).log2()
        );
    }
    println!(
        "  => largest non-primitive table: {} rows (~2^{:.1})",
        max_h,
        (max_h.max(1) as f64).log2()
    );

    // ---- steady-state timing: the first CPU/GPU proves above already warmed
    // the CPU caches AND compiled the GPU WGSL->Metal pipelines (a one-time
    // per-process cost); best-of-3 on the config-dependent PROVE phase isolates
    // the steady-state kernel time from that one-shot warm-up + machine jitter.
    let mut cpu_prove = cpu.prove_seconds;
    let mut gpu_prove = gpu.prove_seconds;
    let mut cpu_prep = cpu.prepare_seconds;
    let mut gpu_prep = gpu.prepare_seconds;
    for _ in 0..2 {
        let c = prove_recursion_layer_cpu(&input, &cpu_config, &cpu_config).expect("cpu reprove");
        let g = prove_recursion_layer_gpu(&input, &cpu_config, &gpu_config).expect("gpu reprove");
        // Parity must hold on EVERY GPU re-prove (deterministic + bit-exact).
        assert_eq!(
            postcard::to_allocvec(&g.proof).expect("reprove serializes"),
            cpu_lib_bytes,
            "a GPU re-prove diverged from the real CPU fold proof"
        );
        cpu_prove = cpu_prove.min(c.prove_seconds);
        gpu_prove = gpu_prove.min(g.prove_seconds);
        cpu_prep = cpu_prep.min(c.prepare_seconds);
        gpu_prep = gpu_prep.min(g.prepare_seconds);
    }

    // ---- 5. MEASURE (best-of-3, parity re-asserted each GPU prove) ----------
    let gpu_total = gpu_prep + gpu_prove;
    let cpu_total = cpu_prep + cpu_prove;
    println!("\n=== REAL FOLD LAYER, END-TO-END ON GPU (P3MerklePoseidon2Air wrap, best-of-3) ===");
    println!(
        "adapter                    : {}",
        dregg_circuit_prove::gpu_backend::GpuDft::default()
            .adapter_name()
            .unwrap()
    );
    println!("proof bytes (identical)    : {}", gpu_bytes.len());
    println!("prepare phase (shared CPU) : CPU {cpu_prep:8.3} s | GPU {gpu_prep:8.3} s");
    println!(
        "PROVE phase (the GPU lever): CPU {:8.3} s | GPU {:8.3} s  =>  {:.2}x",
        cpu_prove,
        gpu_prove,
        cpu_prove / gpu_prove
    );
    println!(
        "whole layer (prepare+prove): CPU {:8.3} s | GPU {:8.3} s  =>  {:.2}x  (conservative: prepare is shared CPU)",
        cpu_total,
        gpu_total,
        cpu_total / gpu_total
    );
    println!(
        "CPU library whole-layer    : {cpu_library_total:8.3} s (cross-check on the real fold path)"
    );
    println!(
        "byte-identical to real fold: YES ({} bytes)",
        cpu_lib_bytes.len()
    );
}
