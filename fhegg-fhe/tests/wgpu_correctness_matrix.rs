//! Cross-backend correctness matrix for fhEgg's portable wgpu arithmetic.
//!
//! This test binary has two modes:
//!
//! - ordinary tests are capability-portable: every GPU result is checked against
//!   the independent CPU definition, and an unavailable adapter must be reported
//!   as an explicit CPU fallback;
//! - the ignored `require_real_wgpu_*` teeth are for the hbox GPU lane. They fail
//!   closed unless the supported kernels actually report device residency.
//!
//! Keep this integration-level. Kernel modules own their focused unit fixtures;
//! this file checks that backend selection cannot change accepted inputs or bits.

use fhegg_fhe::bfv_lean::{fold, BfvLeanError, LeanCiphertext, RnsPoly, FOLD_MODULI};
use fhegg_fhe::bfv_ntt_gpu::{multiply_rns_cpu, BfvNttError, RnsNttBackend, RnsNttEngine};
use fhegg_fhe::gpu_arena::{FoldBackend, FoldEngine};
use fhegg_fhe::tfhe_wgpu::{
    torus_negacyclic_mac_cpu, torus_negacyclic_mac_portable, torus_negacyclic_mac_with_policy,
    TorusMacBackend, TorusMacError, TorusMacPolicy,
};

const PLAINTEXT_MODULUS: u64 = 1 << 20;

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

fn synthetic_ciphertext(seed: u64, degree: usize, level: u64, plain_bound: u64) -> LeanCiphertext {
    let mut rng = XorShift64(seed);
    let polys = (0..2)
        .map(|poly_index| RnsPoly {
            rows: FOLD_MODULI
                .iter()
                .enumerate()
                .map(|(modulus_index, &q)| {
                    (0..degree)
                        .map(|coefficient_index| match coefficient_index % 11 {
                            // Deliberately cover both u32 limbs, conditional-subtract
                            // boundaries, and the additive identities in every matrix row.
                            0 => 0,
                            1 => 1,
                            2 => q - 1,
                            3 => q - 2,
                            4 => u64::from(u32::MAX).min(q - 1),
                            5 => (u64::from(u32::MAX) + 1).min(q - 1),
                            _ => {
                                rng.next()
                                    .wrapping_add((poly_index * 17 + modulus_index) as u64)
                                    % q
                            }
                        })
                        .collect()
                })
                .collect(),
        })
        .collect();
    LeanCiphertext {
        moduli: FOLD_MODULI.to_vec(),
        degree,
        level,
        variable_time: seed & 1 == 1,
        polys,
        plain_bound,
    }
}

fn assert_same_refusal(
    cpu_only: &FoldEngine,
    automatic: &FoldEngine,
    ciphertexts: &[LeanCiphertext],
) -> BfvLeanError {
    let cpu_error = cpu_only
        .fold(ciphertexts, PLAINTEXT_MODULUS)
        .expect_err("explicit CPU policy must refuse malformed input");
    let automatic_error = automatic
        .fold(ciphertexts, PLAINTEXT_MODULUS)
        .expect_err("automatic backend policy must refuse malformed input");
    assert_eq!(
        automatic_error, cpu_error,
        "adapter availability changed the public preflight refusal"
    );
    cpu_error
}

#[test]
fn bfv_randomized_matrix_is_bit_exact_and_reports_the_backend() {
    let automatic = FoldEngine::new();
    let cpu_only = FoldEngine::cpu_only();

    for (case_index, &(degree, count)) in [(1usize, 1usize), (7, 2), (64, 3), (257, 9), (4096, 2)]
        .iter()
        .enumerate()
    {
        let ciphertexts = (0..count)
            .map(|index| {
                synthetic_ciphertext(
                    0x5eed_0000_0000_0000 ^ ((case_index as u64) << 16) ^ index as u64,
                    degree,
                    case_index as u64,
                    3,
                )
            })
            .collect::<Vec<_>>();
        let oracle = fold(&ciphertexts, PLAINTEXT_MODULUS).expect("CPU arithmetic oracle");

        let forced_cpu = cpu_only
            .fold(&ciphertexts, PLAINTEXT_MODULUS)
            .expect("explicit CPU execution");
        assert_eq!(forced_cpu.ciphertext, oracle);
        assert_eq!(forced_cpu.backend, FoldBackend::CpuNoArena);

        let selected = automatic
            .fold(&ciphertexts, PLAINTEXT_MODULUS)
            .expect("automatic backend execution");
        assert_eq!(
            selected.ciphertext, oracle,
            "CPU/GPU bit parity failed for degree={degree}, count={count}"
        );
        match selected.backend {
            FoldBackend::GpuResident(plan) => {
                assert!(automatic.has_gpu_arena());
                assert_eq!(plan.input_ciphertexts, count);
                assert!(plan.ciphertexts_per_chunk > 0);
                assert!(plan.upload_chunks > 0);
            }
            FoldBackend::CpuNoArena => assert!(
                !automatic.has_gpu_arena(),
                "an available arena was silently relabelled as CPU fallback"
            ),
            FoldBackend::CpuUnsupportedShape => {
                panic!("the exact deployed FOLD_MODULI shape is GPU-supported")
            }
        }
    }
    eprintln!(
        "BFV fold matrix: 5 exact CPU-parity shapes; retained_wgpu_arena={}",
        automatic.has_gpu_arena()
    );
}

#[test]
fn bfv_preflight_acceptance_is_adapter_independent_and_fail_closed() {
    let automatic = FoldEngine::new();
    let cpu_only = FoldEngine::cpu_only();

    assert_eq!(
        assert_same_refusal(&cpu_only, &automatic, &[]),
        BfvLeanError::EmptyFold
    );

    let mut at_modulus = synthetic_ciphertext(1, 8, 0, PLAINTEXT_MODULUS);
    assert!(matches!(
        assert_same_refusal(&cpu_only, &automatic, &[at_modulus.clone()]),
        BfvLeanError::WrapRefused {
            bound_sum,
            plaintext_modulus: PLAINTEXT_MODULUS,
        } if bound_sum == u128::from(PLAINTEXT_MODULUS)
    ));

    at_modulus.plain_bound = PLAINTEXT_MODULUS - 1;
    let one_more = synthetic_ciphertext(2, 8, 0, 1);
    assert!(matches!(
        assert_same_refusal(&cpu_only, &automatic, &[at_modulus, one_more]),
        BfvLeanError::WrapRefused {
            bound_sum,
            plaintext_modulus: PLAINTEXT_MODULUS,
        } if bound_sum == u128::from(PLAINTEXT_MODULUS)
    ));

    let good = synthetic_ciphertext(3, 8, 0, 1);
    let mut mixed_level = synthetic_ciphertext(4, 8, 1, 1);
    assert!(matches!(
        assert_same_refusal(&cpu_only, &automatic, &[good.clone(), mixed_level.clone()]),
        BfvLeanError::Incompatible(_)
    ));
    mixed_level.level = 0;
    mixed_level.polys[0].rows[1].pop();
    assert!(matches!(
        assert_same_refusal(&cpu_only, &automatic, &[good.clone(), mixed_level]),
        BfvLeanError::Incompatible(_)
    ));

    let mut noncanonical = good.clone();
    noncanonical.polys[1].rows[2][3] = FOLD_MODULI[2];
    assert_eq!(
        assert_same_refusal(&cpu_only, &automatic, &[noncanonical]),
        BfvLeanError::NonCanonical { modulus_index: 2 }
    );

    // The WGSL one-subtract proof and Rust add path are deliberately pinned to
    // the deployed RNS basis. An arbitrary three-modulus impostor must not be
    // mistaken for the accelerated shape merely because its vector length is 3.
    let mut unsafe_modulus = good;
    unsafe_modulus.moduli[2] = u64::MAX - 58;
    unsafe_modulus.polys[0].rows[2].fill(u64::MAX - 59);
    unsafe_modulus.polys[1].rows[2].fill(u64::MAX - 59);
    assert!(matches!(
        assert_same_refusal(
            &cpu_only,
            &automatic,
            &[unsafe_modulus.clone(), unsafe_modulus]
        ),
        BfvLeanError::Incompatible(_)
    ));
    eprintln!("BFV fold preflight: 7 adapter-independent adversarial refusals");
}

#[test]
fn bfv_unsupported_shape_fallback_is_explicit_and_bit_exact() {
    let automatic = FoldEngine::new();
    let cpu_only = FoldEngine::cpu_only();
    let mut ciphertexts = (0..3)
        .map(|index| synthetic_ciphertext(index + 20, 31, 0, 2))
        .collect::<Vec<_>>();
    for ciphertext in &mut ciphertexts {
        ciphertext.moduli.pop();
        for poly in &mut ciphertext.polys {
            poly.rows.pop();
        }
    }
    let oracle = fold(&ciphertexts, PLAINTEXT_MODULUS).expect("two-modulus CPU oracle");
    let forced = cpu_only
        .fold(&ciphertexts, PLAINTEXT_MODULUS)
        .expect("explicit CPU fallback");
    assert_eq!(forced.ciphertext, oracle);
    assert_eq!(forced.backend, FoldBackend::CpuNoArena);

    let selected = automatic
        .fold(&ciphertexts, PLAINTEXT_MODULUS)
        .expect("automatic unsupported-shape fallback");
    assert_eq!(selected.ciphertext, oracle);
    assert_eq!(
        selected.backend,
        if automatic.has_gpu_arena() {
            FoldBackend::CpuUnsupportedShape
        } else {
            FoldBackend::CpuNoArena
        }
    );
}

fn synthetic_rns_poly(seed: u64, degree: usize, moduli: &[u64]) -> RnsPoly {
    let mut rng = XorShift64(seed);
    RnsPoly {
        rows: moduli
            .iter()
            .enumerate()
            .map(|(row, &q)| {
                (0..degree)
                    .map(|coefficient| match coefficient % 9 {
                        0 => 0,
                        1 => 1,
                        2 => q - 1,
                        3 => q - 2,
                        4 => u64::from(u32::MAX).min(q - 1),
                        5 => (u64::from(u32::MAX) + 1).min(q - 1),
                        _ => rng.next().wrapping_add(row as u64) % q,
                    })
                    .collect()
            })
            .collect(),
    }
}

fn assert_same_ntt_refusal(
    cpu_only: &RnsNttEngine,
    automatic: &RnsNttEngine,
    lhs: &RnsPoly,
    rhs: &RnsPoly,
    moduli: &[u64],
) -> BfvNttError {
    let cpu_error = cpu_only
        .multiply(lhs, rhs, moduli)
        .expect_err("explicit NTT CPU policy must refuse malformed input");
    let automatic_error = automatic
        .multiply(lhs, rhs, moduli)
        .expect_err("automatic NTT policy must refuse malformed input");
    assert_eq!(
        automatic_error, cpu_error,
        "NTT adapter selection changed preflight semantics"
    );
    cpu_error
}

#[test]
fn bfv_ntt_randomized_matrix_is_bit_exact_and_backend_is_honest() {
    let automatic = RnsNttEngine::new();
    let cpu_only = RnsNttEngine::cpu_only();
    for (case_index, degree) in [8usize, 16, 64, 256, 4096].into_iter().enumerate() {
        let lhs = synthetic_rns_poly(0x4e77_1000 ^ case_index as u64, degree, &FOLD_MODULI);
        let rhs = synthetic_rns_poly(0x4e77_2000 ^ case_index as u64, degree, &FOLD_MODULI);
        let oracle = multiply_rns_cpu(&lhs, &rhs, &FOLD_MODULI).expect("exact CPU NTT oracle");

        let forced = cpu_only
            .multiply(&lhs, &rhs, &FOLD_MODULI)
            .expect("explicit NTT CPU execution");
        assert_eq!(forced.polynomial, oracle);
        assert_eq!(forced.backend, RnsNttBackend::CpuPolicy);

        let selected = automatic
            .multiply(&lhs, &rhs, &FOLD_MODULI)
            .expect("automatic NTT execution");
        assert_eq!(
            selected.polynomial, oracle,
            "NTT parity failed at degree={degree}"
        );
        match selected.backend {
            RnsNttBackend::Wgpu { adapter } => {
                assert!(automatic.has_gpu());
                assert!(!adapter.is_empty());
            }
            RnsNttBackend::CpuUnavailable { reason }
            | RnsNttBackend::CpuAdapterLimits { reason } => {
                assert!(!reason.is_empty());
            }
            RnsNttBackend::CpuPolicy => {
                panic!("automatic NTT engine reported an explicit-policy backend")
            }
        }
    }
    eprintln!(
        "BFV NTT matrix: 5 exact CPU-parity shapes; wgpu_context={}",
        automatic.has_gpu()
    );
}

#[test]
fn bfv_ntt_malformed_shapes_are_refused_before_backend_selection() {
    let automatic = RnsNttEngine::new();
    let cpu_only = RnsNttEngine::cpu_only();
    let good = synthetic_rns_poly(71, 8, &FOLD_MODULI);

    assert!(matches!(
        assert_same_ntt_refusal(&cpu_only, &automatic, &good, &good, &[]),
        BfvNttError::InvalidShape(_)
    ));

    let short = synthetic_rns_poly(72, 4, &FOLD_MODULI);
    assert!(matches!(
        assert_same_ntt_refusal(&cpu_only, &automatic, &short, &short, &FOLD_MODULI),
        BfvNttError::InvalidShape(_)
    ));

    let mut wrong_rows = good.clone();
    wrong_rows.rows.pop();
    assert!(matches!(
        assert_same_ntt_refusal(&cpu_only, &automatic, &wrong_rows, &good, &FOLD_MODULI),
        BfvNttError::InvalidShape(_)
    ));

    let mut noncanonical = good.clone();
    noncanonical.rows[1][3] = FOLD_MODULI[1];
    assert!(matches!(
        assert_same_ntt_refusal(&cpu_only, &automatic, &noncanonical, &good, &FOLD_MODULI,),
        BfvNttError::NonCanonical {
            operand: "lhs",
            row: 1,
            coefficient: 3,
            ..
        }
    ));

    let too_large_moduli = [FOLD_MODULI[0], FOLD_MODULI[1], 1u64 << 62];
    let lhs = synthetic_rns_poly(73, 8, &too_large_moduli);
    let rhs = synthetic_rns_poly(74, 8, &too_large_moduli);
    assert!(matches!(
        assert_same_ntt_refusal(&cpu_only, &automatic, &lhs, &rhs, &too_large_moduli),
        BfvNttError::UnsupportedParameters(_)
    ));
    eprintln!("BFV NTT preflight: 5 adapter-independent adversarial refusals");
}

fn torus_fixture(seed: u64, degree: usize, products: usize) -> (Vec<u64>, Vec<u64>, Vec<u64>) {
    let mut rng = XorShift64(seed);
    let mut value = |index: usize| match index % 9 {
        0 => 0,
        1 => 1,
        2 => u64::MAX,
        3 => u64::from(u32::MAX),
        4 => u64::from(u32::MAX) + 1,
        5 => 1 << 63,
        _ => rng.next(),
    };
    let accumulator = (0..degree).map(&mut value).collect();
    let lhs = (0..degree * products)
        .map(|index| value(index + degree))
        .collect();
    let rhs = (0..degree * products)
        .map(|index| value(index + degree * (products + 1)))
        .collect();
    (accumulator, lhs, rhs)
}

#[test]
fn torus_mac_randomized_wraparound_matrix_matches_cpu_bit_for_bit() {
    let mut observed_wgpu = None;
    for (case_index, &(degree, products)) in
        [(1usize, 1usize), (2, 3), (4, 2), (8, 5), (32, 3), (64, 2)]
            .iter()
            .enumerate()
    {
        let (accumulator, lhs, rhs) =
            torus_fixture(0xd1ce_f00d_0000_0000 ^ case_index as u64, degree, products);
        let oracle = torus_negacyclic_mac_cpu(&accumulator, &lhs, &rhs, degree)
            .expect("bit-exact CPU torus oracle");
        let forced = torus_negacyclic_mac_with_policy(
            &accumulator,
            &lhs,
            &rhs,
            degree,
            TorusMacPolicy::CpuOnly,
        )
        .expect("explicit torus CPU policy");
        assert_eq!(forced.coefficients, oracle);
        assert_eq!(forced.backend, TorusMacBackend::CpuOnly);
        let selected = torus_negacyclic_mac_portable(&accumulator, &lhs, &rhs, degree)
            .expect("portable torus MAC");
        assert_eq!(
            selected.coefficients, oracle,
            "torus parity failed for degree={degree}, products={products}"
        );
        let is_wgpu = matches!(selected.backend, TorusMacBackend::Wgpu { .. });
        if let Some(previous) = observed_wgpu {
            assert_eq!(
                is_wgpu, previous,
                "small supported shapes changed backend within one retained context"
            );
        } else {
            observed_wgpu = Some(is_wgpu);
        }
        match selected.backend {
            TorusMacBackend::Wgpu {
                adapter_name,
                backend,
                ..
            } => {
                assert!(!adapter_name.is_empty());
                assert!(!backend.is_empty());
            }
            TorusMacBackend::CpuFallback(_) => {}
            TorusMacBackend::CpuOnly => {
                panic!("automatic torus policy reported the explicit CPU backend")
            }
        }
    }
    eprintln!(
        "TFHE torus matrix: 6 exact CPU-parity shapes; wgpu={}",
        observed_wgpu.unwrap_or(false)
    );
}

#[test]
fn torus_malformed_shapes_are_refused_before_backend_selection() {
    let cases = [
        (
            torus_negacyclic_mac_portable(&[], &[], &[], 0),
            TorusMacError::ZeroDegree,
        ),
        (
            torus_negacyclic_mac_portable(&[0; 3], &[0; 3], &[0; 3], 3),
            TorusMacError::DegreeNotPowerOfTwo { degree: 3 },
        ),
        (
            torus_negacyclic_mac_portable(&[0; 4], &[], &[], 4),
            TorusMacError::EmptyProductBatch,
        ),
        (
            torus_negacyclic_mac_portable(&[0; 3], &[0; 4], &[0; 4], 4),
            TorusMacError::AccumulatorLength {
                expected: 4,
                actual: 3,
            },
        ),
        (
            torus_negacyclic_mac_portable(&[0; 4], &[0; 4], &[0; 8], 4),
            TorusMacError::OperandLengthMismatch { lhs: 4, rhs: 8 },
        ),
        (
            torus_negacyclic_mac_portable(&[0; 4], &[0; 6], &[0; 6], 4),
            TorusMacError::OperandLengthNotMultiple { len: 6, degree: 4 },
        ),
    ];
    for (actual, expected) in cases {
        assert_eq!(actual.expect_err("malformed shape must fail"), expected);
    }
    eprintln!("TFHE torus preflight: 6 adapter-independent adversarial refusals");
}

#[test]
#[ignore = "hbox GPU tooth: requires a real wgpu adapter and fails closed without it"]
fn require_real_wgpu_bfv_and_torus_residency() {
    let engine = FoldEngine::new();
    assert!(engine.has_gpu_arena(), "no retained BFV wgpu arena");
    let ciphertexts = (0..17)
        .map(|index| synthetic_ciphertext(index + 100, 4096, 0, 3))
        .collect::<Vec<_>>();
    let oracle = fold(&ciphertexts, PLAINTEXT_MODULUS).expect("CPU BFV oracle");
    let selected = engine
        .fold(&ciphertexts, PLAINTEXT_MODULUS)
        .expect("resident BFV fold");
    assert_eq!(selected.ciphertext, oracle);
    assert!(
        matches!(selected.backend, FoldBackend::GpuResident(_)),
        "real-adapter lane did not execute the resident BFV backend: {:?}",
        selected.backend
    );
    eprintln!("hard BFV fold backend: {:?}", selected.backend);

    let (accumulator, lhs, rhs) = torus_fixture(0x51a7_5eed, 256, 2);
    let oracle = torus_negacyclic_mac_cpu(&accumulator, &lhs, &rhs, 256).expect("CPU torus oracle");
    let selected = torus_negacyclic_mac_with_policy(
        &accumulator,
        &lhs,
        &rhs,
        256,
        TorusMacPolicy::RequireWgpu,
    )
    .expect("required wgpu torus MAC");
    assert_eq!(selected.coefficients, oracle);
    assert!(
        matches!(selected.backend, TorusMacBackend::Wgpu { .. }),
        "real-adapter lane did not execute the torus wgpu backend: {:?}",
        selected.backend
    );
    eprintln!("hard TFHE torus backend: {:?}", selected.backend);

    let lhs = synthetic_rns_poly(0x4e77_aa, 4096, &FOLD_MODULI);
    let rhs = synthetic_rns_poly(0x4e77_bb, 4096, &FOLD_MODULI);
    let oracle = multiply_rns_cpu(&lhs, &rhs, &FOLD_MODULI).expect("CPU NTT oracle");
    let ntt = RnsNttEngine::new();
    assert!(ntt.has_gpu(), "no wgpu context for the BFV NTT kernel");
    let selected = ntt
        .multiply(&lhs, &rhs, &FOLD_MODULI)
        .expect("wgpu BFV NTT multiply");
    assert_eq!(selected.polynomial, oracle);
    assert!(
        matches!(selected.backend, RnsNttBackend::Wgpu { .. }),
        "real-adapter lane did not execute the BFV NTT backend: {:?}",
        selected.backend
    );
    eprintln!("hard BFV NTT backend: {:?}", selected.backend);
}
