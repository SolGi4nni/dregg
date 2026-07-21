//! Production-shaped PBS buffer/addressing qualification.
//!
//! This gate uses the deployed 918-coefficient blind mask and 918-coefficient
//! post-key-switch mask, while keeping only four blind-rotation coefficients
//! active. It therefore qualifies the full BSK/KSK footprint, first/middle/last
//! BSK addressing, full output fanout, and prepared-key reuse. It is not a dense
//! 918-CMUX performance claim; the coefficient-domain chain is not suitable for
//! that claim until transform-form residency lands.

use std::time::{Duration, Instant};

use fhegg_fhe::tfhe_wgpu::{
    prepare_torus_pbs_wgpu_plan, torus_blind_rotate_cpu, torus_pbs_extract_keyswitch_cpu,
    torus_pbs_extract_keyswitch_prepared, TorusExternalProductParams, TorusKeyswitchParams,
    TorusMacBackend, TorusMacError, TorusWgpuAlgorithm,
};
use tfhe::core_crypto::prelude::*;
use tfhe::shortint::parameters::PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128;

fn median(mut samples: Vec<Duration>) -> Duration {
    samples.sort_unstable();
    samples[samples.len() / 2]
}

#[test]
fn deployed_918_by_918_sparse_pbs_matches_tfhe_and_reuses_device_keys() {
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
    let mut standard_bsk = vec![0u64; blind_mask_dimension * ggsw_coefficients];
    let active_steps = [(0usize, 1u64), (306, 0), (612, 1), (917, 1)];
    for &(step, selector) in &active_steps {
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
            Cleartext(selector),
            deployed.glwe_noise_distribution,
            &mut encryption_generator,
        );
        let start = step * ggsw_coefficients;
        standard_bsk[start..start + ggsw_coefficients].copy_from_slice(ggsw.as_ref());
    }

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
    assert_eq!(standard_bsk.len() * std::mem::size_of::<u64>(), 60_162_048);
    assert_eq!(
        standard_ksk.as_ref().len() * std::mem::size_of::<u64>(),
        60_227_584
    );

    let log_modulus = (2 * external_params.degree).ilog2();
    let encode_rotation = |rotation: u64| rotation << (u64::BITS - log_modulus);
    let mut lwe_mask = vec![0u64; blind_mask_dimension];
    for (offset, &(step, _)) in active_steps.iter().enumerate() {
        lwe_mask[step] = encode_rotation([13u64, 257, 1023, 2047][offset]);
    }
    let lwe_body = encode_rotation(333);
    let mut accumulator = vec![0u64; external_params.glwe_size * external_params.degree];
    for (index, coefficient) in accumulator[external_params.degree..].iter_mut().enumerate() {
        *coefficient = ((index % 8) as u64) << 60;
    }

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

    // Keep tfhe-rs itself as the independent authority for the complete
    // sample-extraction/key-switch fanout, including output coefficient 918.
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
        &standard_bsk,
        external_params,
        standard_ksk.as_ref(),
        keyswitch_params,
    )
    .unwrap();
    let prepare_time = prepare_started.elapsed();

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
    for _ in 0..5 {
        let started = Instant::now();
        let result =
            torus_pbs_extract_keyswitch_prepared(&plan, &accumulator, &lwe_mask, lwe_body).unwrap();
        warm_samples.push(started.elapsed());
        assert_eq!(result.coefficients, tfhe_expected.as_ref());
    }
    let warm_time = median(warm_samples);

    assert!(matches!(
        torus_pbs_extract_keyswitch_prepared(&plan, &accumulator, &lwe_mask[..917], lwe_body),
        Err(TorusMacError::BlindRotationMaskLength {
            expected: 918,
            actual: 917,
        })
    ));

    // The far-end BSK slot is genuinely addressed, and the prepared plan owns
    // its device snapshot rather than consulting the host slice again.
    let last_key_start = 917 * ggsw_coefficients;
    standard_bsk[last_key_start..last_key_start + ggsw_coefficients].fill(0);
    let without_last_selector = torus_pbs_extract_keyswitch_cpu(
        &accumulator,
        &lwe_mask,
        lwe_body,
        &standard_bsk,
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

    eprintln!(
        "TFHE production-shaped sparse PBS: mask=918 (4 active), KS=2048->918, BSK={:.2}MiB KSK={:.2}MiB cpu={:.3}ms prepare/upload={:.3}ms first={:.3}ms warm-median={:.3}ms backend={:?}",
        standard_bsk.len() as f64 * 8.0 / 1_048_576.0,
        standard_ksk.as_ref().len() as f64 * 8.0 / 1_048_576.0,
        cpu_time.as_secs_f64() * 1_000.0,
        prepare_time.as_secs_f64() * 1_000.0,
        first_time.as_secs_f64() * 1_000.0,
        warm_time.as_secs_f64() * 1_000.0,
        first.backend,
    );
}
