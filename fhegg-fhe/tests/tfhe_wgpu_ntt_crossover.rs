//! Same-adapter crossover and differential gate for the exact TFHE RNS-NTT.
//!
//! The test forces both GPU algorithms, compares each against the frozen CPU
//! definition, and prints warm execution times. It fails closed on hosts used
//! for qualification (`DREGG_REQUIRE_WGPU=1`) and explicitly skips elsewhere.

use std::time::{Duration, Instant};

use fhegg_fhe::tfhe_wgpu::{
    torus_external_product_cpu, torus_external_product_with_mode, TorusExternalProductMode,
    TorusExternalProductParams, TorusMacBackend, TorusMacPolicy, TorusWgpuAlgorithm,
};

#[derive(Clone, Copy)]
struct XorShift64(u64);

impl XorShift64 {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn fixture_with_params(
    params: TorusExternalProductParams,
) -> (Vec<u64>, Vec<u64>, Vec<u64>, TorusExternalProductParams) {
    let mut rng = XorShift64(0x7472_616e_7366_6f72 ^ params.degree as u64);
    let glwe_coefficients = params.glwe_size * params.degree;
    let ggsw_coefficients =
        params.decomposition_level_count * params.glwe_size * params.glwe_size * params.degree;
    (
        (0..glwe_coefficients).map(|_| rng.next()).collect(),
        (0..glwe_coefficients).map(|_| rng.next()).collect(),
        (0..ggsw_coefficients).map(|_| rng.next()).collect(),
        params,
    )
}

fn fixture(degree: usize) -> (Vec<u64>, Vec<u64>, Vec<u64>, TorusExternalProductParams) {
    fixture_with_params(TorusExternalProductParams {
        degree,
        glwe_size: 2,
        decomposition_base_log: 23,
        decomposition_level_count: 1,
    })
}

fn timed_gpu(
    accumulator: &[u64],
    glwe: &[u64],
    ggsw: &[u64],
    params: TorusExternalProductParams,
    mode: TorusExternalProductMode,
) -> (Vec<u64>, TorusMacBackend, Duration) {
    let started = Instant::now();
    let result = torus_external_product_with_mode(
        accumulator,
        glwe,
        ggsw,
        params,
        TorusMacPolicy::RequireWgpu,
        mode,
    )
    .expect("qualification mode requires the requested GPU algorithm");
    (result.coefficients, result.backend, started.elapsed())
}

fn median_gpu(
    accumulator: &[u64],
    glwe: &[u64],
    ggsw: &[u64],
    params: TorusExternalProductParams,
    mode: TorusExternalProductMode,
    oracle: &[u64],
) -> (TorusMacBackend, Duration) {
    const SAMPLES: usize = 5;
    let mut samples = Vec::with_capacity(SAMPLES);
    let mut selected_backend = None;
    for _ in 0..SAMPLES {
        let (coefficients, backend, elapsed) = timed_gpu(accumulator, glwe, ggsw, params, mode);
        assert_eq!(
            coefficients, oracle,
            "GPU sample diverged from the CPU authority"
        );
        if let Some(expected) = &selected_backend {
            assert_eq!(
                &backend, expected,
                "backend changed within one median sample"
            );
        } else {
            selected_backend = Some(backend);
        }
        samples.push(elapsed);
    }
    samples.sort_unstable();
    (
        selected_backend.expect("the fixed-size sample set is non-empty"),
        samples[SAMPLES / 2],
    )
}

#[test]
fn exact_ntt_matches_full_width_oracle_and_reports_crossover() {
    if std::env::var_os("DREGG_REQUIRE_WGPU").is_none() {
        eprintln!("TFHE RNS-NTT crossover skipped: DREGG_REQUIRE_WGPU is not set");
        return;
    }

    // Independent process-cold startup at the deployed degree. The two GPU
    // implementations own separate retained contexts, so this compares their
    // actual first dispatch/pipeline cost before either is warmed.
    let (cold_accumulator, cold_glwe, cold_ggsw, cold_params) = fixture(2048);
    let cold_cpu_started = Instant::now();
    let cold_oracle =
        torus_external_product_cpu(&cold_accumulator, &cold_glwe, &cold_ggsw, cold_params)
            .expect("cold CPU oracle");
    let cold_cpu = cold_cpu_started.elapsed();
    let (cold_coefficient, _, cold_coefficient_time) = timed_gpu(
        &cold_accumulator,
        &cold_glwe,
        &cold_ggsw,
        cold_params,
        TorusExternalProductMode::CoefficientDomain,
    );
    let (cold_ntt, _, cold_ntt_time) = timed_gpu(
        &cold_accumulator,
        &cold_glwe,
        &cold_ggsw,
        cold_params,
        TorusExternalProductMode::ExactRnsNtt,
    );
    assert_eq!(cold_coefficient, cold_oracle);
    assert_eq!(cold_ntt, cold_oracle);
    eprintln!(
        "TFHE N=2048 process-cold: cpu={:.3}ms coefficient-gpu={:.3}ms exact-rns-ntt-gpu={:.3}ms",
        cold_cpu.as_secs_f64() * 1_000.0,
        cold_coefficient_time.as_secs_f64() * 1_000.0,
        cold_ntt_time.as_secs_f64() * 1_000.0,
    );

    let mut rows = Vec::new();
    for degree in [256usize, 512, 1024, 2048, 4096] {
        let (accumulator, glwe, ggsw, params) = fixture(degree);
        let cpu_started = Instant::now();
        let oracle = torus_external_product_cpu(&accumulator, &glwe, &ggsw, params)
            .expect("full-width coefficient oracle");
        let cpu_time = cpu_started.elapsed();

        // One untimed call initializes/caches each pipeline before the compared
        // warm samples. Both returned values still have to match the oracle.
        let (coefficient_warmup, _, _) = timed_gpu(
            &accumulator,
            &glwe,
            &ggsw,
            params,
            TorusExternalProductMode::CoefficientDomain,
        );
        let (ntt_warmup, _, _) = timed_gpu(
            &accumulator,
            &glwe,
            &ggsw,
            params,
            TorusExternalProductMode::ExactRnsNtt,
        );
        assert_eq!(
            coefficient_warmup, oracle,
            "quadratic GPU mismatch at N={degree}"
        );
        assert_eq!(ntt_warmup, oracle, "exact RNS-NTT mismatch at N={degree}");

        let (coefficient_backend, coefficient_time) = median_gpu(
            &accumulator,
            &glwe,
            &ggsw,
            params,
            TorusExternalProductMode::CoefficientDomain,
            &oracle,
        );
        let (ntt_backend, ntt_time) = median_gpu(
            &accumulator,
            &glwe,
            &ggsw,
            params,
            TorusExternalProductMode::ExactRnsNtt,
            &oracle,
        );
        assert!(matches!(
            coefficient_backend,
            TorusMacBackend::Wgpu {
                algorithm: TorusWgpuAlgorithm::CoefficientDomain,
                ..
            }
        ));
        assert!(matches!(
            ntt_backend,
            TorusMacBackend::Wgpu {
                algorithm: TorusWgpuAlgorithm::ExactRnsNtt,
                ..
            }
        ));
        rows.push((degree, cpu_time, coefficient_time, ntt_time));
    }

    eprintln!("TFHE exact external-product crossover on the selected adapter:");
    for (degree, cpu, coefficient, ntt) in rows {
        eprintln!(
            "  N={degree:4}: cpu={:.3}ms coefficient={:.3}ms exact-rns-ntt={:.3}ms ntt/coefficient={:.3}",
            cpu.as_secs_f64() * 1_000.0,
            coefficient.as_secs_f64() * 1_000.0,
            ntt.as_secs_f64() * 1_000.0,
            ntt.as_secs_f64() / coefficient.as_secs_f64(),
        );
    }
}

#[test]
fn exact_ntt_matches_cpu_for_two_level_full_width_external_product() {
    if std::env::var_os("DREGG_REQUIRE_WGPU").is_none() {
        eprintln!("TFHE multi-level RNS-NTT parity skipped: DREGG_REQUIRE_WGPU is not set");
        return;
    }

    // This is deliberately a harsher shape than the deployed level-one gate:
    // every source coefficient uses all 64 bits, the gadget digit can use 31
    // bits, and both decomposition levels participate in the batched CRT sum.
    let params = TorusExternalProductParams {
        degree: 512,
        glwe_size: 2,
        decomposition_base_log: 31,
        decomposition_level_count: 2,
    };
    let (accumulator, glwe, ggsw, params) = fixture_with_params(params);
    let oracle = torus_external_product_cpu(&accumulator, &glwe, &ggsw, params)
        .expect("multi-level CPU authority");
    let (ntt, backend, _) = timed_gpu(
        &accumulator,
        &glwe,
        &ggsw,
        params,
        TorusExternalProductMode::ExactRnsNtt,
    );
    assert_eq!(ntt, oracle);
    assert!(matches!(
        backend,
        TorusMacBackend::Wgpu {
            algorithm: TorusWgpuAlgorithm::ExactRnsNtt,
            ..
        }
    ));
}
