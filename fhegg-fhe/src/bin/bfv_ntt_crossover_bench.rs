//! Light BFV-NTT GPU-vs-CPU crossover bench — the COMPUTE-BOUND kernel, measured without the heavy
//! `tfhe-integer` feature (which pulls tfhe-rs + bulletproofs and does not fit the disk-constrained boxes).
//!
//! The NTT engines (`RnsNttEngine::cpu_only`/`require_wgpu`, `forward_odd_batch`) live in the main lib, so
//! this bin builds light (no tfhe). It measures the deployed q0/q1/q2 odd NTT forward + inverse, CPU vs GPU,
//! BIT-EXACT (round-trip parity asserted), across batch sizes — the compute-bound op the fold analysis
//! ignored. NTT is O(n log n) modular-mul butterflies per poly vs the fold's one add/coeff, so this is where
//! the GPU is built to win. Honest exit(2) if no adapter.

use fhegg_fhe::bfv_lean::{RnsPoly, FOLD_MODULI};
use fhegg_fhe::bfv_ntt_gpu::{RnsNttBackend, RnsNttEngine};
use std::time::Instant;

const DEG: usize = 4096;
const REPS: usize = 5;
const BATCH_SIZES: &[usize] = &[1, 4, 16, 64, 256, 512, 1024, 2048];

/// A deterministic canonical deg-4096 RnsPoly over FOLD_MODULI (same synth style as the other benches).
fn deployed_poly(seed: u64) -> RnsPoly {
    let mut s = seed;
    let mut next = || {
        s = s
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .rotate_left(17)
            .wrapping_add(1);
        s
    };
    RnsPoly {
        rows: FOLD_MODULI
            .iter()
            .map(|&q| (0..DEG).map(|_| next() % q).collect())
            .collect(),
    }
}

fn best_ms<F: FnMut()>(mut f: F) -> f64 {
    let mut best = f64::MAX;
    for _ in 0..REPS {
        let t = Instant::now();
        f();
        best = best.min(t.elapsed().as_secs_f64() * 1000.0);
    }
    best
}

fn main() {
    println!("bfv_ntt_crossover_bench — the COMPUTE-BOUND NTT, GPU vs CPU (light build, no tfhe-integer)");
    let cpu = RnsNttEngine::cpu_only();
    let gpu = RnsNttEngine::require_wgpu();

    // Adapter ground truth + cold parity.
    let warm = deployed_poly(0x6750_4e54_0000);
    let cold = match gpu.forward_odd(&warm, &FOLD_MODULI) {
        Ok(c) => c,
        Err(e) => {
            println!("NO usable wgpu NTT adapter ({e}) — honest exit.");
            std::process::exit(2);
        }
    };
    let adapter = match &cold.backend {
        RnsNttBackend::Wgpu { adapter } => adapter.clone(),
        other => {
            println!("require_wgpu returned non-GPU backend {other:?} — honest exit.");
            std::process::exit(2);
        }
    };
    let cpu_warm = cpu.forward_odd(&warm, &FOLD_MODULI).expect("cpu forward");
    assert_eq!(
        cold.polynomial, cpu_warm.polynomial,
        "GPU forward NTT diverged from CPU (bit-exact parity broke)"
    );
    println!("adapter: {adapter}");
    println!(
        "\n{:>6} {:>8} | {:>11} {:>11} | {:>9} | {:>11} {:>11} | {:>9}",
        "batch", "MiB", "CPU fwd", "GPU fwd", "fwd g/c", "CPU inv", "GPU inv", "inv g/c"
    );

    for &batch in BATCH_SIZES {
        let inputs: Vec<RnsPoly> = (0..batch)
            .map(|i| deployed_poly(0x6750_4e54_1000 + i as u64))
            .collect();
        // Parity first: forward then inverse round-trips exactly.
        let fwd_ref = cpu
            .forward_odd_batch(&inputs, &FOLD_MODULI)
            .expect("cpu forward batch");
        let inv_ref = cpu
            .inverse_odd_batch(&fwd_ref.polynomials, &FOLD_MODULI)
            .expect("cpu inverse batch");
        assert_eq!(inv_ref.polynomials, inputs, "CPU NTT round-trip not exact");
        let gpu_fwd = gpu
            .forward_odd_batch(&inputs, &FOLD_MODULI)
            .expect("gpu forward batch");
        assert_eq!(
            gpu_fwd.polynomials, fwd_ref.polynomials,
            "GPU forward batch diverged from CPU at batch={batch}"
        );
        let gpu_inv = gpu
            .inverse_odd_batch(&gpu_fwd.polynomials, &FOLD_MODULI)
            .expect("gpu inverse batch");
        assert_eq!(
            gpu_inv.polynomials, inputs,
            "GPU NTT round-trip not exact at batch={batch}"
        );

        // 3 RNS rows * DEG coeffs * 8 B * batch, MiB.
        let mib = (3 * DEG * 8 * batch) as f64 / (1024.0 * 1024.0);
        let cpu_fwd_ms = best_ms(|| {
            let _ = cpu.forward_odd_batch(&inputs, &FOLD_MODULI).unwrap();
        });
        let gpu_fwd_ms = best_ms(|| {
            let _ = gpu.forward_odd_batch(&inputs, &FOLD_MODULI).unwrap();
        });
        let cpu_inv_ms = best_ms(|| {
            let _ = cpu
                .inverse_odd_batch(&fwd_ref.polynomials, &FOLD_MODULI)
                .unwrap();
        });
        let gpu_inv_ms = best_ms(|| {
            let _ = gpu
                .inverse_odd_batch(&fwd_ref.polynomials, &FOLD_MODULI)
                .unwrap();
        });
        println!(
            "{:>6} {:>8.2} | {:>9.3}ms {:>9.3}ms | {:>7.2}x | {:>9.3}ms {:>9.3}ms | {:>7.2}x  BIT-EXACT",
            batch,
            mib,
            cpu_fwd_ms,
            gpu_fwd_ms,
            cpu_fwd_ms / gpu_fwd_ms,
            cpu_inv_ms,
            gpu_inv_ms,
            cpu_inv_ms / gpu_inv_ms
        );
    }
    println!("\n(g/c > 1 = GPU faster. Forward+inverse odd NTT over the deployed q0/q1/q2 set, batch-parallel,");
    println!(" bit-exact vs the CPU engine. This is the compute-bound kernel the fold analysis ignored.)");
}
