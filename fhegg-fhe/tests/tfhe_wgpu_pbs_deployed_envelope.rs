//! Deployed dense PBS qualification.
//!
//! This gate uses the deployed 918-coefficient blind mask and 918-coefficient
//! post-key-switch mask. Every mask coefficient has a nonzero modulus-switched
//! rotation and every BSK slot is a genuinely noisy GGSW encryption of the
//! corresponding bit of a real input secret. This is the honest quadratic
//! coefficient baseline for the transform-resident implementation, not a claim
//! that the coefficient route is the final deployed backend.

use std::time::{Duration, Instant};

use fhegg_fhe::tfhe_wgpu::{
    prepare_torus_pbs_transform_wgpu_plan, prepare_torus_pbs_wgpu_plan, torus_blind_rotate_cpu,
    torus_pbs_extract_keyswitch_cpu, torus_pbs_extract_keyswitch_prepared,
    torus_pbs_extract_keyswitch_transform_prepared, torus_pbs_modulus_switch,
    TorusExternalProductParams, TorusKeyswitchParams, TorusMacBackend, TorusMacError,
    TorusWgpuAlgorithm,
};
use tfhe::core_crypto::prelude::*;
use tfhe::shortint::parameters::PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128;

fn median(mut samples: Vec<Duration>) -> Duration {
    samples.sort_unstable();
    samples[samples.len() / 2]
}

#[test]
fn deployed_918_by_918_dense_pbs_matches_tfhe_and_reuses_device_keys() {
    if std::env::var_os("DREGG_REQUIRE_WGPU").is_none() {
        eprintln!("set DREGG_REQUIRE_WGPU=1 to run the deployed GPU envelope gate");
        return;
    }

    let deployed = PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128;
    let external_params = TorusExternalProductParams {
        degree: deployed.polynomial_size.0,
        glwe_size: deployed.glwe_dimension.to_glwe_size().0,
        decomposition_base_log: deployed.pbs_base_log.0,
        decomposition_level_count: deployed.pbs_level.0,
    };
    let keyswitch_params = TorusKeyswitchParams {
        output_lwe_dimension: deployed.lwe_dimension.0,
        decomposition_base_log: deployed.ks_base_log.0,
        decomposition_level_count: deployed.ks_level.0,
    };
    let blind_mask_dimension = deployed.lwe_dimension.0;
    assert_eq!(blind_mask_dimension, 918);
    assert_eq!(keyswitch_params.output_lwe_dimension, 918);

    let mut seeder = new_seeder();
    let seeder = seeder.as_mut();
    let mut encryption_generator =
        EncryptionRandomGenerator::<DefaultRandomGenerator>::new(seeder.seed(), seeder);
    let mut secret_generator = SecretRandomGenerator::<DefaultRandomGenerator>::new(seeder.seed());
    let input_lwe_secret = allocate_and_generate_new_binary_lwe_secret_key(
        deployed.lwe_dimension,
        &mut secret_generator,
    );
    let output_glwe_secret = allocate_and_generate_new_binary_glwe_secret_key(
        deployed.glwe_dimension,
        deployed.polynomial_size,
        &mut secret_generator,
    );
    let post_keyswitch_secret = allocate_and_generate_new_binary_lwe_secret_key(
        deployed.lwe_dimension,
        &mut secret_generator,
    );

    let ggsw_coefficients = deployed.pbs_level.0
        * deployed.glwe_dimension.to_glwe_size().0
        * deployed.glwe_dimension.to_glwe_size().0
        * deployed.polynomial_size.0;
    let mut standard_bsk = allocate_and_generate_new_lwe_bootstrap_key(
        &input_lwe_secret,
        &output_glwe_secret,
        deployed.pbs_base_log,
        deployed.pbs_level,
        deployed.glwe_noise_distribution,
        deployed.ciphertext_modulus,
        &mut encryption_generator,
    );

    let equivalent_glwe_lwe_secret = output_glwe_secret.clone().into_lwe_secret_key();
    let standard_ksk = allocate_and_generate_new_lwe_keyswitch_key(
        &equivalent_glwe_lwe_secret,
        &post_keyswitch_secret,
        deployed.ks_base_log,
        deployed.ks_level,
        deployed.lwe_noise_distribution,
        deployed.ciphertext_modulus,
        &mut encryption_generator,
    );
    assert_eq!(
        standard_bsk.as_ref().len() * std::mem::size_of::<u64>(),
        60_162_048
    );
    assert_eq!(
        standard_ksk.as_ref().len() * std::mem::size_of::<u64>(),
        60_227_584
    );

    // Rejection-sample a real encrypted input until all 918 modulus-switched
    // mask values are nonzero. The test therefore executes every CMUX; there
    // are no sparse/no-op mask slots hiding inside the dense timing.
    let (lwe_mask, lwe_body) = loop {
        let input = allocate_and_encrypt_new_lwe_ciphertext(
            &input_lwe_secret,
            Plaintext(3u64 << 60),
            deployed.lwe_noise_distribution,
            deployed.ciphertext_modulus,
            &mut encryption_generator,
        );
        let (mask, body) = input.get_mask_and_body();
        if mask.as_ref().iter().all(|&coefficient| {
            torus_pbs_modulus_switch(coefficient, external_params.degree).unwrap() != 0
        }) {
            break (mask.as_ref().to_vec(), *body.data);
        }
    };
    assert_eq!(lwe_mask.len(), 918);
    assert_eq!(
        lwe_mask
            .iter()
            .filter(|&&coefficient| {
                torus_pbs_modulus_switch(coefficient, external_params.degree).unwrap() != 0
            })
            .count(),
        918
    );
    let mut accumulator = vec![0u64; external_params.glwe_size * external_params.degree];
    for (index, coefficient) in accumulator[external_params.degree..].iter_mut().enumerate() {
        *coefficient = ((index % 8) as u64) << 60;
    }

    let cpu_started = Instant::now();
    let cpu = torus_pbs_extract_keyswitch_cpu(
        &accumulator,
        &lwe_mask,
        lwe_body,
        standard_bsk.as_ref(),
        external_params,
        standard_ksk.as_ref(),
        keyswitch_params,
    )
    .unwrap();
    let cpu_time = cpu_started.elapsed();

    // Keep tfhe-rs itself as the independent authority for the complete
    // sample-extraction/key-switch fanout, including output coefficient 918.
    let rotated = torus_blind_rotate_cpu(
        &accumulator,
        &lwe_mask,
        lwe_body,
        standard_bsk.as_ref(),
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
        equivalent_glwe_lwe_secret.lwe_dimension().to_lwe_size(),
        deployed.ciphertext_modulus,
    );
    extract_lwe_sample_from_glwe_ciphertext(&rotated_glwe, &mut extracted, MonomialDegree(0));
    let mut tfhe_expected = LweCiphertext::new(
        0u64,
        post_keyswitch_secret.lwe_dimension().to_lwe_size(),
        deployed.ciphertext_modulus,
    );
    keyswitch_lwe_ciphertext(&standard_ksk, &extracted, &mut tfhe_expected);
    assert_eq!(cpu, tfhe_expected.as_ref());

    let prepare_started = Instant::now();
    let plan = prepare_torus_pbs_wgpu_plan(
        blind_mask_dimension,
        standard_bsk.as_ref(),
        external_params,
        standard_ksk.as_ref(),
        keyswitch_params,
    )
    .unwrap();
    let prepare_time = prepare_started.elapsed();

    let transform_prepare_started = Instant::now();
    let transform_plan = prepare_torus_pbs_transform_wgpu_plan(
        blind_mask_dimension,
        standard_bsk.as_ref(),
        external_params,
        standard_ksk.as_ref(),
        keyswitch_params,
    )
    .unwrap();
    let transform_prepare_time = transform_prepare_started.elapsed();

    let mut one_step_mask = lwe_mask.clone();
    one_step_mask[1..].fill(0);
    let one_step_expected = torus_pbs_extract_keyswitch_cpu(
        &accumulator,
        &one_step_mask,
        lwe_body,
        standard_bsk.as_ref(),
        external_params,
        standard_ksk.as_ref(),
        keyswitch_params,
    )
    .unwrap();
    let transform_one_started = Instant::now();
    let transform_one = torus_pbs_extract_keyswitch_transform_prepared(
        &transform_plan,
        &accumulator,
        &one_step_mask,
        lwe_body,
    )
    .unwrap();
    let transform_one_time = transform_one_started.elapsed();
    assert_eq!(transform_one.coefficients, one_step_expected);
    eprintln!(
        "TFHE transform plan: prepare={:.3}ms one-step={:.3}ms backend={:?}",
        transform_prepare_time.as_secs_f64() * 1_000.0,
        transform_one_time.as_secs_f64() * 1_000.0,
        transform_one.backend,
    );

    let transform_dense_started = Instant::now();
    let transform_dense = torus_pbs_extract_keyswitch_transform_prepared(
        &transform_plan,
        &accumulator,
        &lwe_mask,
        lwe_body,
    )
    .unwrap();
    let transform_dense_time = transform_dense_started.elapsed();
    assert_eq!(transform_dense.coefficients, tfhe_expected.as_ref());
    let mut transform_warm_samples = Vec::new();
    for _ in 0..3 {
        let started = Instant::now();
        let result = torus_pbs_extract_keyswitch_transform_prepared(
            &transform_plan,
            &accumulator,
            &lwe_mask,
            lwe_body,
        )
        .unwrap();
        transform_warm_samples.push(started.elapsed());
        assert_eq!(result.coefficients, tfhe_expected.as_ref());
    }
    let transform_warm_time = median(transform_warm_samples);
    eprintln!(
        "TFHE transform dense 918: first={:.3}ms warm-median={:.3}ms backend={:?}",
        transform_dense_time.as_secs_f64() * 1_000.0,
        transform_warm_time.as_secs_f64() * 1_000.0,
        transform_dense.backend,
    );

    let first_started = Instant::now();
    let first =
        torus_pbs_extract_keyswitch_prepared(&plan, &accumulator, &lwe_mask, lwe_body).unwrap();
    let first_time = first_started.elapsed();
    assert_eq!(first.coefficients, tfhe_expected.as_ref());
    assert!(matches!(
        first.backend,
        TorusMacBackend::Wgpu {
            algorithm: TorusWgpuAlgorithm::ExactDeviceResidentPbsExtractKeyswitch,
            ..
        }
    ));

    let mut warm_samples = Vec::new();
    for _ in 0..3 {
        let started = Instant::now();
        let result =
            torus_pbs_extract_keyswitch_prepared(&plan, &accumulator, &lwe_mask, lwe_body).unwrap();
        warm_samples.push(started.elapsed());
        assert_eq!(result.coefficients, tfhe_expected.as_ref());
    }
    let warm_time = median(warm_samples);

    let mut scaling = Vec::new();
    for active_steps in [64usize, 256, 512] {
        let mut prefix_mask = lwe_mask.clone();
        prefix_mask[active_steps..].fill(0);
        let prefix_cpu_started = Instant::now();
        let prefix_cpu = torus_pbs_extract_keyswitch_cpu(
            &accumulator,
            &prefix_mask,
            lwe_body,
            standard_bsk.as_ref(),
            external_params,
            standard_ksk.as_ref(),
            keyswitch_params,
        )
        .unwrap();
        let prefix_cpu_time = prefix_cpu_started.elapsed();
        let prefix_gpu_started = Instant::now();
        let prefix_gpu =
            torus_pbs_extract_keyswitch_prepared(&plan, &accumulator, &prefix_mask, lwe_body)
                .unwrap();
        let prefix_gpu_time = prefix_gpu_started.elapsed();
        assert_eq!(prefix_gpu.coefficients, prefix_cpu);
        let prefix_transform_started = Instant::now();
        let prefix_transform = torus_pbs_extract_keyswitch_transform_prepared(
            &transform_plan,
            &accumulator,
            &prefix_mask,
            lwe_body,
        )
        .unwrap();
        let prefix_transform_time = prefix_transform_started.elapsed();
        assert_eq!(prefix_transform.coefficients, prefix_cpu);
        scaling.push((
            active_steps,
            prefix_cpu_time,
            prefix_gpu_time,
            prefix_transform_time,
        ));
    }

    assert!(matches!(
        torus_pbs_extract_keyswitch_prepared(&plan, &accumulator, &lwe_mask[..917], lwe_body),
        Err(TorusMacError::BlindRotationMaskLength {
            expected: 918,
            actual: 917,
        })
    ));
    assert!(matches!(
        torus_pbs_extract_keyswitch_transform_prepared(
            &transform_plan,
            &accumulator,
            &lwe_mask[..917],
            lwe_body,
        ),
        Err(TorusMacError::BlindRotationMaskLength {
            expected: 918,
            actual: 917,
        })
    ));

    // The far-end encrypted BSK slot is genuinely addressed, and the prepared
    // plan owns its device snapshot rather than consulting the host key again.
    let last_key_start = 917 * ggsw_coefficients;
    standard_bsk.as_mut()[last_key_start..last_key_start + ggsw_coefficients].fill(0);
    let without_last_selector = torus_pbs_extract_keyswitch_cpu(
        &accumulator,
        &lwe_mask,
        lwe_body,
        standard_bsk.as_ref(),
        external_params,
        standard_ksk.as_ref(),
        keyswitch_params,
    )
    .unwrap();
    assert_ne!(
        without_last_selector,
        tfhe_expected.as_ref(),
        "the final BSK slot was not load-bearing"
    );
    let retained =
        torus_pbs_extract_keyswitch_prepared(&plan, &accumulator, &lwe_mask, lwe_body).unwrap();
    assert_eq!(retained.coefficients, tfhe_expected.as_ref());
    let transform_retained = torus_pbs_extract_keyswitch_transform_prepared(
        &transform_plan,
        &accumulator,
        &lwe_mask,
        lwe_body,
    )
    .unwrap();
    assert_eq!(transform_retained.coefficients, tfhe_expected.as_ref());

    let mutated_transform_plan = prepare_torus_pbs_transform_wgpu_plan(
        blind_mask_dimension,
        standard_bsk.as_ref(),
        external_params,
        standard_ksk.as_ref(),
        keyswitch_params,
    )
    .unwrap();
    let mutated_transform = torus_pbs_extract_keyswitch_transform_prepared(
        &mutated_transform_plan,
        &accumulator,
        &lwe_mask,
        lwe_body,
    )
    .unwrap();
    assert_eq!(mutated_transform.coefficients, without_last_selector);
    assert_ne!(mutated_transform.coefficients, tfhe_expected.as_ref());

    eprintln!(
        "TFHE exact dense scaling (active CMUX, full 2048->918 KS): {}",
        scaling
            .iter()
            .map(|(steps, cpu, gpu, transform)| format!(
                "{steps}:cpu={:.3}ms/coeff={:.3}ms/ntt={:.3}ms",
                cpu.as_secs_f64() * 1_000.0,
                gpu.as_secs_f64() * 1_000.0,
                transform.as_secs_f64() * 1_000.0,
            ))
            .collect::<Vec<_>>()
            .join(", ")
    );

    eprintln!(
        "TFHE deployed dense PBS: mask=918 (918 active/noisy BSK), KS=2048->918, BSK={:.2}MiB KSK={:.2}MiB cpu={:.3}ms prepare/upload={:.3}ms first={:.3}ms warm-median={:.3}ms backend={:?}",
        standard_bsk.as_ref().len() as f64 * 8.0 / 1_048_576.0,
        standard_ksk.as_ref().len() as f64 * 8.0 / 1_048_576.0,
        cpu_time.as_secs_f64() * 1_000.0,
        prepare_time.as_secs_f64() * 1_000.0,
        first_time.as_secs_f64() * 1_000.0,
        warm_time.as_secs_f64() * 1_000.0,
        first.backend,
    );
}
