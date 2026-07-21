//! Strict exact gate for the first device-resident blind-rotation chain.

use std::time::{Duration, Instant};

use fhegg_fhe::tfhe_wgpu::{
    torus_blind_rotate_cpu, torus_blind_rotate_with_policy, torus_pbs_modulus_switch,
    TorusExternalProductParams, TorusMacBackend, TorusMacPolicy, TorusWgpuAlgorithm,
};
use tfhe::core_crypto::algorithms::polynomial_algorithms::{
    polynomial_wrapping_add_mul_assign, polynomial_wrapping_monic_monomial_div,
    polynomial_wrapping_monic_monomial_mul,
};
use tfhe::core_crypto::entities::Polynomial;
use tfhe::core_crypto::prelude::*;
use tfhe::shortint::parameters::PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128;

fn rotate_tfhe(input: &[u64], params: TorusExternalProductParams, degree: usize) -> Vec<u64> {
    let mut output = vec![0u64; input.len()];
    for polynomial in 0..params.glwe_size {
        let start = polynomial * params.degree;
        let end = start + params.degree;
        let source = Polynomial::from_container(&input[start..end]);
        let mut destination = Polynomial::from_container(&mut output[start..end]);
        polynomial_wrapping_monic_monomial_mul(&mut destination, &source, MonomialDegree(degree));
    }
    output
}

fn divide_tfhe(input: &[u64], params: TorusExternalProductParams, degree: usize) -> Vec<u64> {
    let mut output = vec![0u64; input.len()];
    for polynomial in 0..params.glwe_size {
        let start = polynomial * params.degree;
        let end = start + params.degree;
        let source = Polynomial::from_container(&input[start..end]);
        let mut destination = Polynomial::from_container(&mut output[start..end]);
        polynomial_wrapping_monic_monomial_div(&mut destination, &source, MonomialDegree(degree));
    }
    output
}

fn independent_tfhe_blind_rotation(
    accumulator: &[u64],
    lwe_mask: &[u64],
    lwe_body: u64,
    standard_bsk: &[u64],
    params: TorusExternalProductParams,
) -> Vec<u64> {
    let glwe_coefficients = params.glwe_size * params.degree;
    let ggsw_coefficients =
        params.decomposition_level_count * params.glwe_size * params.glwe_size * params.degree;
    let body_degree = torus_pbs_modulus_switch(lwe_body, params.degree).unwrap();
    let mut current = divide_tfhe(accumulator, params, body_degree);
    let decomposer = SignedDecomposer::<u64>::new(
        DecompositionBaseLog(params.decomposition_base_log),
        DecompositionLevelCount(params.decomposition_level_count),
    );
    for (step, &mask_coefficient) in lwe_mask.iter().enumerate() {
        let rotation = torus_pbs_modulus_switch(mask_coefficient, params.degree).unwrap();
        if rotation == 0 {
            continue;
        }
        let rotated = rotate_tfhe(&current, params, rotation);
        let difference = rotated
            .iter()
            .zip(&current)
            .map(|(&then_coefficient, &else_coefficient)| {
                then_coefficient.wrapping_sub(else_coefficient)
            })
            .collect::<Vec<_>>();
        let mut decomposed = vec![0u64; params.decomposition_level_count * glwe_coefficients];
        for (coefficient, &value) in difference.iter().enumerate() {
            for (level, term) in decomposer.decompose(value).enumerate() {
                decomposed[level * glwe_coefficients + coefficient] = term.value();
            }
        }
        let key_start = step * ggsw_coefficients;
        for level in 0..params.decomposition_level_count {
            for row in 0..params.glwe_size {
                let digit_start = level * glwe_coefficients + row * params.degree;
                let digit = Polynomial::from_container(
                    &decomposed[digit_start..digit_start + params.degree],
                );
                for output_polynomial in 0..params.glwe_size {
                    let matrix_start = key_start
                        + ((level * params.glwe_size + row) * params.glwe_size + output_polynomial)
                            * params.degree;
                    let matrix = Polynomial::from_container(
                        &standard_bsk[matrix_start..matrix_start + params.degree],
                    );
                    let output_start = output_polynomial * params.degree;
                    let mut output = Polynomial::from_container(
                        &mut current[output_start..output_start + params.degree],
                    );
                    polynomial_wrapping_add_mul_assign(&mut output, &digit, &matrix);
                }
            }
        }
    }
    current
}

fn median(mut samples: Vec<Duration>) -> Duration {
    samples.sort_unstable();
    samples[samples.len() / 2]
}

#[test]
fn encrypted_four_step_blind_rotation_is_exact_and_device_resident() {
    let deployed = PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128;
    let params = TorusExternalProductParams {
        degree: deployed.polynomial_size.0,
        glwe_size: deployed.glwe_dimension.to_glwe_size().0,
        decomposition_base_log: deployed.pbs_base_log.0,
        decomposition_level_count: deployed.pbs_level.0,
    };
    assert_eq!(params.degree, 2048);
    assert_eq!(params.glwe_size, 2);
    assert_eq!(params.decomposition_base_log, 23);
    assert_eq!(params.decomposition_level_count, 1);

    let mut seeder = new_seeder();
    let seeder = seeder.as_mut();
    let mut encryption_generator =
        EncryptionRandomGenerator::<DefaultRandomGenerator>::new(seeder.seed(), seeder);
    let mut secret_generator = SecretRandomGenerator::<DefaultRandomGenerator>::new(seeder.seed());
    let output_secret = allocate_and_generate_new_binary_glwe_secret_key(
        deployed.glwe_dimension,
        deployed.polynomial_size,
        &mut secret_generator,
    );

    // This is a genuine standard bootstrapping-key prefix: each noisy GGSW
    // encrypts one binary input-LWE secret coefficient under the output GLWE key.
    let selector_bits = [1u64, 0, 1, 1];
    let mut standard_bsk = Vec::new();
    for &bit in &selector_bits {
        let mut ggsw = GgswCiphertext::new(
            0u64,
            deployed.glwe_dimension.to_glwe_size(),
            deployed.polynomial_size,
            deployed.pbs_base_log,
            deployed.pbs_level,
            deployed.ciphertext_modulus,
        );
        encrypt_constant_ggsw_ciphertext(
            &output_secret,
            &mut ggsw,
            Cleartext(bit),
            deployed.glwe_noise_distribution,
            &mut encryption_generator,
        );
        standard_bsk.extend_from_slice(ggsw.as_ref());
    }

    let log_modulus = (2 * params.degree).ilog2();
    let encode_rotation = |rotation: u64| rotation << (u64::BITS - log_modulus);
    let desired_rotations = [13usize, 257, 1023, 2047];
    let lwe_mask = desired_rotations
        .iter()
        .map(|&rotation| encode_rotation(rotation as u64))
        .collect::<Vec<_>>();
    let body_rotation = 333usize;
    let lwe_body = encode_rotation(body_rotation as u64);
    for (&coefficient, &expected) in lwe_mask.iter().zip(&desired_rotations) {
        assert_eq!(
            torus_pbs_modulus_switch(coefficient, params.degree),
            Ok(expected)
        );
    }
    assert_eq!(
        torus_pbs_modulus_switch(lwe_body, params.degree),
        Ok(body_rotation)
    );

    // A trivial GLWE accumulator with a coarse exact LUT in the body.
    let mut accumulator = vec![0u64; params.glwe_size * params.degree];
    let lut = (0..params.degree)
        .map(|index| ((index % 8) as u64) << 60)
        .collect::<Vec<_>>();
    accumulator[params.degree..].copy_from_slice(&lut);

    let cpu_started = Instant::now();
    let cpu =
        torus_blind_rotate_cpu(&accumulator, &lwe_mask, lwe_body, &standard_bsk, params).unwrap();
    let cpu_time = cpu_started.elapsed();
    let independent =
        independent_tfhe_blind_rotation(&accumulator, &lwe_mask, lwe_body, &standard_bsk, params);
    assert_eq!(
        cpu, independent,
        "CPU authority diverged from tfhe-rs primitives"
    );

    let policy = if std::env::var_os("DREGG_REQUIRE_WGPU").is_some() {
        TorusMacPolicy::RequireWgpu
    } else {
        TorusMacPolicy::Auto
    };
    let cold_started = Instant::now();
    let cold = torus_blind_rotate_with_policy(
        &accumulator,
        &lwe_mask,
        lwe_body,
        &standard_bsk,
        params,
        policy,
    )
    .unwrap();
    let cold_time = cold_started.elapsed();
    assert_eq!(cold.coefficients, independent);

    let mut warm_samples = Vec::new();
    for _ in 0..5 {
        let started = Instant::now();
        let result = torus_blind_rotate_with_policy(
            &accumulator,
            &lwe_mask,
            lwe_body,
            &standard_bsk,
            params,
            policy,
        )
        .unwrap();
        warm_samples.push(started.elapsed());
        assert_eq!(result.coefficients, independent);
        if policy == TorusMacPolicy::RequireWgpu {
            assert!(matches!(
                result.backend,
                TorusMacBackend::Wgpu {
                    algorithm: TorusWgpuAlgorithm::ExactDeviceResidentBlindRotation,
                    ..
                }
            ));
        }
    }
    let warm_time = median(warm_samples);

    // Semantic check: encrypted selector bits produce the same aggregate
    // rotation of the LUT after decrypting the final GLWE ciphertext.
    let modulus = 2 * params.degree;
    let selected_rotation = desired_rotations.iter().zip(selector_bits).fold(
        (modulus - body_rotation) % modulus,
        |rotation, (&step, bit)| (rotation + step * bit as usize) % modulus,
    );
    let expected_lut = rotate_tfhe(
        &lut,
        TorusExternalProductParams {
            glwe_size: 1,
            ..params
        },
        selected_rotation,
    );
    let output = GlweCiphertext::from_container(
        cold.coefficients,
        deployed.polynomial_size,
        deployed.ciphertext_modulus,
    );
    let mut decrypted = PlaintextList::new(0u64, PlaintextCount(params.degree));
    decrypt_glwe_ciphertext(&output_secret, &output, &mut decrypted);
    let rounder = SignedDecomposer::<u64>::new(DecompositionBaseLog(4), DecompositionLevelCount(1));
    for (actual, &expected) in decrypted.iter().zip(&expected_lut) {
        assert_eq!(rounder.closest_representable(*actual.0), expected);
    }

    // A one-bin mask edit must alter the exact ciphertext result.  This catches
    // implementations which upload the key but fail to bind the rotation list.
    let mut mutated_mask = lwe_mask.clone();
    mutated_mask[0] = encode_rotation((desired_rotations[0] + 1) as u64);
    let mutated =
        torus_blind_rotate_cpu(&accumulator, &mutated_mask, lwe_body, &standard_bsk, params)
            .unwrap();
    assert_ne!(mutated, independent, "mask rotation was not load-bearing");

    eprintln!(
        "TFHE blind rotation N=2048, steps=4: cpu={:.3}ms gpu-cold={:.3}ms gpu-warm-median={:.3}ms backend={:?}",
        cpu_time.as_secs_f64() * 1_000.0,
        cold_time.as_secs_f64() * 1_000.0,
        warm_time.as_secs_f64() * 1_000.0,
        cold.backend,
    );
}
