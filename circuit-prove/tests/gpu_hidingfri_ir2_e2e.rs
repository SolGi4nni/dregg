//! A real shielded proof through the portable GPU PCS, not a standalone shader.
//!
//! The statement is the Lean-emitted, depth-uniform 4-ary Merkle-membership
//! IR2 relation.  Both lanes use identical pinned randomness:
//!
//! - CPU: production `HidingFriPcs` + upstream `MerkleTreeHidingMmcs`;
//! - GPU: the same `HidingFriPcs` wire shape + `GpuDft` +
//!   `GpuHidingBabyBearMmcs` (salted Poseidon2 leaves and the resident tree).
//!
//! The gate requires a completed GPU Merkle commit, byte-compares the complete
//! batch proof, re-tags it into the CPU config, and asks the untouched CPU
//! verifier to accept it.  A second polarity test proves that
//! `DREGG_REQUIRE_WGPU=1` refuses an explicitly disabled Merkle stage instead
//! of silently reporting an all-CPU success.

use std::time::Instant;

use dregg_circuit::descriptor_ir2::{
    Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::membership_descriptor_4ary::{
    membership_descriptor_of_depth_4ary, membership_witness_4ary,
};
use dregg_circuit::poseidon2_air::create_poseidon2_test_witness;
use dregg_circuit::stark_zk::DreggZkStarkConfig;
use dregg_circuit_prove::gpu_backend::{
    create_cpu_zk_config_seeded, create_gpu_zk_config_seeded, hiding_gpu_dispatch_counters,
    lde_residency_counters, prove_vm_descriptor2_gpu_zk, require_hiding_gpu_dispatch_since,
};

// HidingFRI doubles the trace with interleaved random rows. Depth 2048 makes
// that randomized input exactly 2^12 rows, the first GPU-DFT production band;
// a smaller fixture would exercise GPU Merkle but honestly retain no LDE.
const DEPTH: usize = 2048;
const MMCS_SEED: [u8; 32] = [0x4d; 32];
const PCS_SEED: [u8; 32] = [0x5a; 32];

fn decode_cpu_proof_exact(bytes: &[u8]) -> Result<Ir2BatchProof<DreggZkStarkConfig>, String> {
    let (proof, remainder) = postcard::take_from_bytes(bytes)
        .map_err(|error| format!("proof decode failed: {error}"))?;
    if !remainder.is_empty() {
        return Err(format!(
            "proof decode left {} trailing bytes",
            remainder.len()
        ));
    }
    Ok(proof)
}

#[test]
#[ignore = "GPU + proof-heavy: run on hbox with DREGG_REQUIRE_WGPU=1 and --run-ignored all"]
fn lean_ir2_hidingfri_proof_uses_gpu_merkle_and_is_cpu_exact() {
    assert_eq!(
        std::env::var("DREGG_REQUIRE_WGPU").as_deref(),
        Ok("1"),
        "this gate is meaningful only in the hard DREGG_REQUIRE_WGPU=1 posture"
    );

    let leaf = BabyBear::new(0x00c0_ffee);
    let witness = create_poseidon2_test_witness(leaf, DEPTH);
    let siblings = witness
        .levels
        .iter()
        .map(|level| level.siblings)
        .collect::<Vec<_>>();
    let positions = witness
        .levels
        .iter()
        .map(|level| level.position)
        .collect::<Vec<_>>();
    let descriptor = membership_descriptor_of_depth_4ary(DEPTH);
    let (trace, public) = membership_witness_4ary(leaf, &siblings, &positions)
        .expect("depth-2048 4-ary witness builds");

    let gpu_config = create_gpu_zk_config_seeded(MMCS_SEED, PCS_SEED);
    let before = hiding_gpu_dispatch_counters();
    let (resident_hits_before, _) = lde_residency_counters();
    let gpu_started = Instant::now();
    let gpu_proof = prove_vm_descriptor2_for_config(
        &descriptor,
        &trace,
        &public,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &gpu_config,
    )
    .expect("Lean-emitted IR2 statement proves through GPU HidingFRI");
    let gpu_elapsed = gpu_started.elapsed();
    let after = require_hiding_gpu_dispatch_since(before)
        .expect("strict proof interval must contain a GPU Poseidon2 Merkle commit");
    let commit_delta = after.babybear_merkle_commits - before.babybear_merkle_commits;
    let readback_batch_delta =
        after.babybear_merkle_readback_batches - before.babybear_merkle_readback_batches;
    let readback_layer_delta =
        after.babybear_merkle_readback_layers - before.babybear_merkle_readback_layers;
    assert_eq!(
        readback_batch_delta, commit_delta,
        "each GPU Merkle commit must cross the host boundary exactly once"
    );
    assert!(
        readback_layer_delta > readback_batch_delta,
        "whole-tree readback counter did not include opening layers"
    );
    let (resident_hits_after, _) = lde_residency_counters();
    assert!(
        resident_hits_after > resident_hits_before,
        "GPU HidingFRI never consumed a retained GpuDft LDE buffer"
    );
    verify_vm_descriptor2_with_config(&descriptor, &gpu_proof, &public, &gpu_config)
        .expect("GPU-config HidingFRI verifier accepts its proof");

    let cpu_config = create_cpu_zk_config_seeded(MMCS_SEED, PCS_SEED);
    let cpu_started = Instant::now();
    let cpu_proof = prove_vm_descriptor2_for_config(
        &descriptor,
        &trace,
        &public,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &cpu_config,
    )
    .expect("same IR2 statement proves through CPU HidingFRI");
    let cpu_elapsed = cpu_started.elapsed();

    let gpu_bytes = postcard::to_allocvec(&gpu_proof).expect("GPU proof serializes");
    let cpu_bytes = postcard::to_allocvec(&cpu_proof).expect("CPU proof serializes");
    assert_eq!(
        gpu_bytes, cpu_bytes,
        "portable GPU HidingFRI proof diverged from the seeded CPU proof"
    );

    let as_cpu = decode_cpu_proof_exact(&gpu_bytes).expect("GPU proof re-tags exactly");
    verify_vm_descriptor2_with_config(&descriptor, &as_cpu, &public, &cpu_config)
        .expect("untouched CPU HidingFRI verifier accepts GPU-minted bytes");

    let mut wrong_public = public.clone();
    wrong_public[0] += BabyBear::ONE;
    assert!(
        verify_vm_descriptor2_with_config(&descriptor, &as_cpu, &wrong_public, &cpu_config)
            .is_err(),
        "CPU verifier accepted the GPU proof for a changed membership leaf"
    );

    let mut changed_proof_bytes = gpu_bytes.clone();
    let changed_index = changed_proof_bytes.len() / 2;
    changed_proof_bytes[changed_index] ^= 0x01;
    let changed_proof_accepted = decode_cpu_proof_exact(&changed_proof_bytes).is_ok_and(|proof| {
        verify_vm_descriptor2_with_config(&descriptor, &proof, &public, &cpu_config).is_ok()
    });
    assert!(
        !changed_proof_accepted,
        "CPU verifier accepted a mutated GPU HidingFRI proof"
    );

    assert!(
        decode_cpu_proof_exact(&gpu_bytes[..gpu_bytes.len() - 1]).is_err(),
        "exact proof decoder accepted a truncated GPU proof"
    );
    let mut trailing_proof = gpu_bytes.clone();
    trailing_proof.push(0);
    assert!(
        decode_cpu_proof_exact(&trailing_proof).is_err(),
        "exact proof decoder accepted a trailing byte"
    );

    // The production bridge draws fresh OS entropy, enforces the same strict
    // dispatch interval, re-tags to the established CPU receipt type, and
    // self-verifies under the untouched CPU HidingFRI config before returning.
    let production_proof = prove_vm_descriptor2_gpu_zk(
        &descriptor,
        &trace,
        &public,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
    )
    .expect("production GPU HidingFRI bridge proves and CPU-verifies");
    verify_vm_descriptor2_with_config(&descriptor, &production_proof, &public, &cpu_config)
        .expect("established CPU verifier accepts the production GPU receipt type");
    let production_bytes =
        postcard::to_allocvec(&production_proof).expect("production proof serializes");
    assert_ne!(
        production_bytes, gpu_bytes,
        "fresh production HidingFRI randomness unexpectedly reproduced the seeded proof"
    );

    eprintln!(
        "GPU HidingFRI IR2 depth={DEPTH}: proof={} bytes, GPU={:.3}s CPU={:.3}s, GPU commits +{}, whole-tree readback batches +{} ({} layers), DFT dispatches +{}, resident LDE blits +{}",
        gpu_bytes.len(),
        gpu_elapsed.as_secs_f64(),
        cpu_elapsed.as_secs_f64(),
        commit_delta,
        readback_batch_delta,
        readback_layer_delta,
        after.dft_dispatches - before.dft_dispatches,
        resident_hits_after - resident_hits_before,
    );
}

#[test]
#[ignore = "hostile strict-boundary polarity: run with DREGG_REQUIRE_WGPU=1"]
fn required_hidingfri_refuses_disabled_gpu_merkle_stage() {
    assert_eq!(
        std::env::var("DREGG_REQUIRE_WGPU").as_deref(),
        Ok("1"),
        "this refusal gate must run in the strict posture"
    );
    let previous = std::env::var_os("DREGG_GPU_BABYBEAR_MMCS");
    // Each nextest test has its own process; no other test can observe this
    // hostile stage override. Rust 2024 makes environment mutation explicitly
    // unsafe because it would race in a shared process.
    unsafe { std::env::set_var("DREGG_GPU_BABYBEAR_MMCS", "off") };
    let refusal = std::panic::catch_unwind(|| {
        let _ = create_gpu_zk_config_seeded(MMCS_SEED, PCS_SEED);
    });
    match previous {
        Some(value) => unsafe { std::env::set_var("DREGG_GPU_BABYBEAR_MMCS", value) },
        None => unsafe { std::env::remove_var("DREGG_GPU_BABYBEAR_MMCS") },
    }
    assert!(
        refusal.is_err(),
        "strict GPU config silently accepted an explicitly disabled Merkle stage"
    );
}
