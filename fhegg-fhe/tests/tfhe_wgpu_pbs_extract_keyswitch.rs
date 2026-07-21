//! PBS-shaped exact gate: blind rotate, sample extract, and key switch in one GPU submission.

use std::time::{Duration, Instant};

use fhegg_fhe::tfhe_wgpu::{
    torus_blind_rotate_cpu, torus_pbs_extract_keyswitch_cpu,
    torus_pbs_extract_keyswitch_with_policy, TorusExternalProductParams, TorusKeyswitchParams,
    TorusMacBackend, TorusMacPolicy, TorusWgpuAlgorithm,
};
use tfhe::core_crypto::prelude::*;
use tfhe::shortint::parameters::PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128;

fn median(mut samples: Vec<Duration>) -> Duration {
    samples.sort_unstable();
    samples[samples.len() / 2]
}

#[test]
fn blind_rotate_extract_and_keyswitch_matches_tfhe_exactly() {
    let deployed = PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128;
    let external_params = TorusExternalProductParams {
        degree: deployed.polynomial_size.0,
        glwe_size: deployed.glwe_dimension.to_glwe_size().0,
        decomposition_base_log: deployed.pbs_base_log.0,
        decomposition_level_count: deployed.pbs_level.0,
    };
    let keyswitch_params = TorusKeyswitchParams {
        // The input side is still the complete extracted 2048-coefficient GLWE
        // secret. A narrow output keeps this default-path gate cheap enough for
        // normal qualification; the deployed 918-output envelope is separate.
        output_lwe_dimension: 8,
        decomposition_base_log: deployed.ks_base_log.0,
        decomposition_level_count: deployed.ks_level.0,
    };

    let mut seeder = new_seeder();
    let seeder = seeder.as_mut();
    let mut encryption_generator =
        EncryptionRandomGenerator::<DefaultRandomGenerator>::new(seeder.seed(), seeder);
    let mut secret_generator = SecretRandomGenerator::<DefaultRandomGenerator>::new(seeder.seed());
    let output_glwe_secret = allocate_and_generate_new_binary_glwe_secret_key(
        deployed.glwe_dimension,
        deployed.polynomial_size,
        &mut secret_generator,
    );
    let post_keyswitch_secret = allocate_and_generate_new_binary_lwe_secret_key(
        LweDimension(keyswitch_params.output_lwe_dimension),
        &mut secret_generator,
    );

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
            &output_glwe_secret,
            &mut ggsw,
            Cleartext(bit),
            deployed.glwe_noise_distribution,
            &mut encryption_generator,
        );
        standard_bsk.extend_from_slice(ggsw.as_ref());
    }
    let equivalent_glwe_lwe_secret = output_glwe_secret.clone().into_lwe_secret_key();
    assert_eq!(
        equivalent_glwe_lwe_secret.lwe_dimension(),
        LweDimension(2048)
    );
    let standard_ksk = allocate_and_generate_new_lwe_keyswitch_key(
        &equivalent_glwe_lwe_secret,
        &post_keyswitch_secret,
        deployed.ks_base_log,
        deployed.ks_level,
        deployed.lwe_noise_distribution,
        deployed.ciphertext_modulus,
        &mut encryption_generator,
    );

    let log_modulus = (2 * external_params.degree).ilog2();
    let encode_rotation = |rotation: u64| rotation << (u64::BITS - log_modulus);
    let lwe_mask = [13u64, 257, 1023, 2047].map(encode_rotation).to_vec();
    let lwe_body = encode_rotation(333);
    let mut accumulator = vec![0u64; external_params.glwe_size * external_params.degree];
    for (index, coefficient) in accumulator[external_params.degree..].iter_mut().enumerate() {
        *coefficient = ((index % 8) as u64) << 60;
    }

    // Independent tfhe-rs authority for the newly added boundary. Blind
    // rotation itself already has a separate polynomial-level differential gate.
    let rotated = torus_blind_rotate_cpu(
        &accumulator,
        &lwe_mask,
        lwe_body,
        &standard_bsk,
        external_params,
    )
    .unwrap();
    let rotated_glwe = GlweCiphertext::from_container(
        rotated,
        deployed.polynomial_size,
        deployed.ciphertext_modulus,
    );
    let mut extracted = LweCiphertext::new(
        0u64,
        LweDimension(2048).to_lwe_size(),
        deployed.ciphertext_modulus,
    );
    extract_lwe_sample_from_glwe_ciphertext(&rotated_glwe, &mut extracted, MonomialDegree(0));
    let mut tfhe_expected = LweCiphertext::new(
        0u64,
        post_keyswitch_secret.lwe_dimension().to_lwe_size(),
        deployed.ciphertext_modulus,
    );
    keyswitch_lwe_ciphertext(&standard_ksk, &extracted, &mut tfhe_expected);

    let cpu_started = Instant::now();
    let cpu = torus_pbs_extract_keyswitch_cpu(
        &accumulator,
        &lwe_mask,
        lwe_body,
        &standard_bsk,
        external_params,
        standard_ksk.as_ref(),
        keyswitch_params,
    )
    .unwrap();
    let cpu_time = cpu_started.elapsed();
    assert_eq!(cpu, tfhe_expected.as_ref());

    let policy = if std::env::var_os("DREGG_REQUIRE_WGPU").is_some() {
        TorusMacPolicy::RequireWgpu
    } else {
        TorusMacPolicy::Auto
    };
    let cold_started = Instant::now();
    let cold = torus_pbs_extract_keyswitch_with_policy(
        &accumulator,
        &lwe_mask,
        lwe_body,
        &standard_bsk,
        external_params,
        standard_ksk.as_ref(),
        keyswitch_params,
        policy,
    )
    .unwrap();
    let cold_time = cold_started.elapsed();
    assert_eq!(cold.coefficients, tfhe_expected.as_ref());
    if policy == TorusMacPolicy::RequireWgpu {
        assert!(matches!(
            cold.backend,
            TorusMacBackend::Wgpu {
                algorithm: TorusWgpuAlgorithm::ExactDeviceResidentPbsExtractKeyswitch,
                ..
            }
        ));
    }

    let mut warm_samples = Vec::new();
    for _ in 0..5 {
        let started = Instant::now();
        let result = torus_pbs_extract_keyswitch_with_policy(
            &accumulator,
            &lwe_mask,
            lwe_body,
            &standard_bsk,
            external_params,
            standard_ksk.as_ref(),
            keyswitch_params,
            policy,
        )
        .unwrap();
        warm_samples.push(started.elapsed());
        assert_eq!(result.coefficients, tfhe_expected.as_ref());
    }
    let warm_time = median(warm_samples);

    let output = LweCiphertext::from_container(cold.coefficients, deployed.ciphertext_modulus);
    let decrypted = decrypt_lwe_ciphertext(&post_keyswitch_secret, &output);
    let expected_decrypted = decrypt_lwe_ciphertext(&post_keyswitch_secret, &tfhe_expected);
    let rounder = SignedDecomposer::<u64>::new(DecompositionBaseLog(4), DecompositionLevelCount(1));
    assert_eq!(
        rounder.closest_representable(decrypted.0),
        rounder.closest_representable(expected_decrypted.0)
    );

    let mut corrupted_ksk = standard_ksk.as_ref().to_vec();
    corrupted_ksk[0] ^= 1u64 << 60;
    let corrupted = torus_pbs_extract_keyswitch_cpu(
        &accumulator,
        &lwe_mask,
        lwe_body,
        &standard_bsk,
        external_params,
        &corrupted_ksk,
        keyswitch_params,
    )
    .unwrap();
    assert_ne!(
        corrupted,
        tfhe_expected.as_ref(),
        "keyswitch key was not load-bearing"
    );

    eprintln!(
        "TFHE PBS-shaped N=2048, blind-steps=4, KS=2048->8 (base_log={}, levels={}): cpu={:.3}ms gpu-cold={:.3}ms gpu-warm-median={:.3}ms backend={:?}",
        keyswitch_params.decomposition_base_log,
        keyswitch_params.decomposition_level_count,
        cpu_time.as_secs_f64() * 1_000.0,
        cold_time.as_secs_f64() * 1_000.0,
        warm_time.as_secs_f64() * 1_000.0,
        cold.backend,
    );
}
