//! Required-GPU crossover profile for the deployed q0/q1/q2 odd NTT.
//!
//! This is a performance measurement, not an acceptance authority. Every
//! timed GPU result is first required to identify a real wgpu adapter and then
//! compared residue-for-residue with the independently executable CPU path.
//! Run on hbox with `--run-ignored only --no-capture`.

use std::time::{Duration, Instant};

use fhegg_fhe::bfv_lean::{RnsPoly, FOLD_DEGREE, FOLD_MODULI};
use fhegg_fhe::bfv_ntt_gpu::{RnsNttBackend, RnsNttEngine};

const BATCH_SIZES: [usize; 9] = [1, 2, 4, 8, 16, 32, 64, 128, 256];
const REPS: usize = 3;

fn deployed_poly(seed: u64) -> RnsPoly {
    let mut state = seed;
    RnsPoly {
        rows: FOLD_MODULI
            .iter()
            .enumerate()
            .map(|(row, &q)| {
                (0..FOLD_DEGREE)
                    .map(|coefficient| {
                        state = state
                            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                            .rotate_left(17)
                            .wrapping_add((row + coefficient + 1) as u64);
                        match coefficient {
                            0 => 0,
                            1 => 1,
                            2 => q - 1,
                            3 => u64::from(u32::MAX),
                            4 => u64::from(u32::MAX) + 1,
                            _ => state % q,
                        }
                    })
                    .collect()
            })
            .collect(),
    }
}

fn median(mut samples: Vec<Duration>) -> Duration {
    samples.sort_unstable();
    samples[samples.len() / 2]
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1_000.0
}

#[test]
#[ignore = "requires the hbox discrete GPU and records release-mode crossover geometry"]
fn deployed_q0_q1_q2_forward_inverse_batch_crossover_is_exact() {
    let cpu = RnsNttEngine::cpu_only();
    let gpu = RnsNttEngine::require_wgpu();
    let warm_input = deployed_poly(0x6750_4e54_545f_0000);

    let cold_started = Instant::now();
    let cold = gpu
        .forward_odd(&warm_input, &FOLD_MODULI)
        .expect("required-wgpu cold forward transform");
    let cold_elapsed = cold_started.elapsed();
    let adapter = match &cold.backend {
        RnsNttBackend::Wgpu { adapter } => adapter.clone(),
        fallback => panic!("RequireWgpu returned a non-GPU backend: {fallback:?}"),
    };
    let warm_cpu = cpu
        .forward_odd(&warm_input, &FOLD_MODULI)
        .expect("CPU warm transform");
    assert_eq!(cold.polynomial, warm_cpu.polynomial);

    eprintln!(
        "BFV-NTT-CROSSOVER adapter={adapter} cold_forward_ms={:.3}",
        millis(cold_elapsed)
    );
    eprintln!(
        "BFV-NTT-CROSSOVER batch,input_mib,cpu_forward_ms,gpu_forward_ms,forward_gpu_over_cpu,cpu_inverse_ms,gpu_inverse_ms,inverse_gpu_over_cpu"
    );

    for batch_size in BATCH_SIZES {
        let inputs = (0..batch_size)
            .map(|index| deployed_poly(0x6750_4e54_545f_1000 + index as u64))
            .collect::<Vec<_>>();

        let reference_forward = cpu
            .forward_odd_batch(&inputs, &FOLD_MODULI)
            .expect("CPU forward batch");
        let reference_inverse = cpu
            .inverse_odd_batch(&reference_forward.polynomials, &FOLD_MODULI)
            .expect("CPU inverse batch");
        assert_eq!(reference_inverse.polynomials, inputs);

        let mut cpu_forward = Vec::with_capacity(REPS);
        let mut gpu_forward = Vec::with_capacity(REPS);
        let mut cpu_inverse = Vec::with_capacity(REPS);
        let mut gpu_inverse = Vec::with_capacity(REPS);

        for _ in 0..REPS {
            let started = Instant::now();
            let cpu_f = cpu
                .forward_odd_batch(&inputs, &FOLD_MODULI)
                .expect("timed CPU forward batch");
            cpu_forward.push(started.elapsed());

            let started = Instant::now();
            let gpu_f = gpu
                .forward_odd_batch(&inputs, &FOLD_MODULI)
                .expect("timed required-wgpu forward batch");
            gpu_forward.push(started.elapsed());
            assert_eq!(gpu_f.polynomials, cpu_f.polynomials);
            assert!(matches!(
                &gpu_f.backend,
                RnsNttBackend::Wgpu { adapter: actual } if actual == &adapter
            ));
            assert_eq!(gpu_f.plan.input_polynomials, batch_size);
            assert_eq!(gpu_f.plan.total_rns_rows, batch_size * FOLD_MODULI.len());
            assert_eq!(gpu_f.plan.gpu_input_uploads, 1);
            assert_eq!(gpu_f.plan.gpu_queue_submissions, 1);
            assert_eq!(gpu_f.plan.gpu_readbacks, 1);

            let started = Instant::now();
            let cpu_i = cpu
                .inverse_odd_batch(&reference_forward.polynomials, &FOLD_MODULI)
                .expect("timed CPU inverse batch");
            cpu_inverse.push(started.elapsed());

            let started = Instant::now();
            let gpu_i = gpu
                .inverse_odd_batch(&reference_forward.polynomials, &FOLD_MODULI)
                .expect("timed required-wgpu inverse batch");
            gpu_inverse.push(started.elapsed());
            assert_eq!(gpu_i.polynomials, cpu_i.polynomials);
            assert_eq!(gpu_i.polynomials, inputs);
            assert!(matches!(
                &gpu_i.backend,
                RnsNttBackend::Wgpu { adapter: actual } if actual == &adapter
            ));
        }

        let cpu_forward = median(cpu_forward);
        let gpu_forward = median(gpu_forward);
        let cpu_inverse = median(cpu_inverse);
        let gpu_inverse = median(gpu_inverse);
        let input_mib = batch_size * FOLD_MODULI.len() * FOLD_DEGREE * 8;
        eprintln!(
            "BFV-NTT-CROSSOVER {batch_size},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3}",
            input_mib as f64 / (1024.0 * 1024.0),
            millis(cpu_forward),
            millis(gpu_forward),
            gpu_forward.as_secs_f64() / cpu_forward.as_secs_f64(),
            millis(cpu_inverse),
            millis(gpu_inverse),
            gpu_inverse.as_secs_f64() / cpu_inverse.as_secs_f64(),
        );
    }
}
