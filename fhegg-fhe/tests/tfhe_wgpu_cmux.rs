//! Hard parity and semantic gate for the first real portable TFHE conditional.
//!
//! This exercises fhEgg's deployed tfhe-rs shape (N=2048, GLWE size 2,
//! base_log=23, level_count=1), including a genuinely encrypted GGSW selector.
//! It remains the exact O(N^2) coefficient-domain rung: this is CMUX, not yet
//! blind rotation or a complete programmable bootstrap.

use fhegg_fhe::tfhe_wgpu::{
    torus_cmux_cpu, torus_cmux_with_policy, TorusExternalProductParams, TorusMacBackend,
    TorusMacPolicy,
};
use tfhe::core_crypto::algorithms::polynomial_algorithms::polynomial_wrapping_add_mul_assign;
use tfhe::core_crypto::entities::Polynomial;
use tfhe::core_crypto::prelude::*;
use tfhe::shortint::parameters::PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128;

fn independent_tfhe_coefficient_oracle(
    ct0: &[u64],
    ct1: &[u64],
    ggsw: &[u64],
    params: TorusExternalProductParams,
) -> Vec<u64> {
    let glwe_coefficients = params.glwe_size * params.degree;
    let difference: Vec<u64> = ct1
        .iter()
        .zip(ct0)
        .map(|(&then_coefficient, &else_coefficient)| {
            then_coefficient.wrapping_sub(else_coefficient)
        })
        .collect();
    let decomposer = SignedDecomposer::<u64>::new(
        DecompositionBaseLog(params.decomposition_base_log),
        DecompositionLevelCount(params.decomposition_level_count),
    );
    let mut decomposed = vec![0u64; params.decomposition_level_count * glwe_coefficients];
    for (coefficient, &value) in difference.iter().enumerate() {
        for (level, term) in decomposer.decompose(value).enumerate() {
            decomposed[level * glwe_coefficients + coefficient] = term.value();
        }
    }

    let mut output = ct0.to_vec();
    for level in 0..params.decomposition_level_count {
        for row in 0..params.glwe_size {
            let digit_start = level * glwe_coefficients + row * params.degree;
            let digit =
                Polynomial::from_container(&decomposed[digit_start..digit_start + params.degree]);
            for output_polynomial in 0..params.glwe_size {
                let ggsw_start = ((level * params.glwe_size + row) * params.glwe_size
                    + output_polynomial)
                    * params.degree;
                let matrix_polynomial =
                    Polynomial::from_container(&ggsw[ggsw_start..ggsw_start + params.degree]);
                let output_start = output_polynomial * params.degree;
                let mut output_polynomial = Polynomial::from_container(
                    &mut output[output_start..output_start + params.degree],
                );
                polynomial_wrapping_add_mul_assign(
                    &mut output_polynomial,
                    &digit,
                    &matrix_polynomial,
                );
            }
        }
    }
    output
}

#[test]
fn portable_encrypted_cmux_matches_tfhe_at_deployed_degree() {
    let deployed = PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128;
    assert_eq!(deployed.polynomial_size, PolynomialSize(2048));
    assert_eq!(deployed.glwe_dimension, GlweDimension(1));
    assert_eq!(deployed.pbs_base_log, DecompositionBaseLog(23));
    assert_eq!(deployed.pbs_level, DecompositionLevelCount(1));

    let glwe_size = deployed.glwe_dimension.to_glwe_size();
    let params = TorusExternalProductParams {
        degree: deployed.polynomial_size.0,
        glwe_size: glwe_size.0,
        decomposition_base_log: deployed.pbs_base_log.0,
        decomposition_level_count: deployed.pbs_level.0,
    };
    let mut seeder = new_seeder();
    let seeder = seeder.as_mut();
    let mut encryption_generator =
        EncryptionRandomGenerator::<DefaultRandomGenerator>::new(seeder.seed(), seeder);
    let mut secret_generator = SecretRandomGenerator::<DefaultRandomGenerator>::new(seeder.seed());
    let secret_key = allocate_and_generate_new_binary_glwe_secret_key(
        deployed.glwe_dimension,
        deployed.polynomial_size,
        &mut secret_generator,
    );

    // A real, noisy GGSW encryption of condition=1.  No selector key or clear
    // selector crosses the portable backend boundary.
    let mut encrypted_selector = GgswCiphertext::new(
        0u64,
        glwe_size,
        deployed.polynomial_size,
        deployed.pbs_base_log,
        deployed.pbs_level,
        deployed.ciphertext_modulus,
    );
    encrypt_constant_ggsw_ciphertext(
        &secret_key,
        &mut encrypted_selector,
        Cleartext(1u64),
        deployed.glwe_noise_distribution,
        &mut encryption_generator,
    );

    let else_plaintext = Plaintext(1u64 << 60);
    let then_plaintext = Plaintext(3u64 << 60);
    let else_plaintexts =
        PlaintextList::new(else_plaintext.0, PlaintextCount(deployed.polynomial_size.0));
    let then_plaintexts =
        PlaintextList::new(then_plaintext.0, PlaintextCount(deployed.polynomial_size.0));
    let mut ct0 = GlweCiphertext::new(
        0u64,
        glwe_size,
        deployed.polynomial_size,
        deployed.ciphertext_modulus,
    );
    let mut ct1 = ct0.clone();
    encrypt_glwe_ciphertext(
        &secret_key,
        &mut ct0,
        &else_plaintexts,
        deployed.glwe_noise_distribution,
        &mut encryption_generator,
    );
    encrypt_glwe_ciphertext(
        &secret_key,
        &mut ct1,
        &then_plaintexts,
        deployed.glwe_noise_distribution,
        &mut encryption_generator,
    );

    let independent = independent_tfhe_coefficient_oracle(
        ct0.as_ref(),
        ct1.as_ref(),
        encrypted_selector.as_ref(),
        params,
    );
    let cpu = torus_cmux_cpu(
        ct0.as_ref(),
        ct1.as_ref(),
        encrypted_selector.as_ref(),
        params,
    )
    .unwrap();
    assert_eq!(
        cpu, independent,
        "CPU seam diverged from tfhe-rs primitives"
    );

    let policy = if std::env::var_os("DREGG_REQUIRE_WGPU").is_some() {
        TorusMacPolicy::RequireWgpu
    } else {
        TorusMacPolicy::Auto
    };
    let portable = torus_cmux_with_policy(
        ct0.as_ref(),
        ct1.as_ref(),
        encrypted_selector.as_ref(),
        params,
        policy,
    )
    .unwrap();
    assert_eq!(
        portable.coefficients, independent,
        "portable encrypted CMUX diverged via {:?}",
        portable.backend
    );

    let output_ciphertext = GlweCiphertext::from_container(
        portable.coefficients,
        deployed.polynomial_size,
        deployed.ciphertext_modulus,
    );
    let mut decrypted = PlaintextList::new(0u64, PlaintextCount(deployed.polynomial_size.0));
    decrypt_glwe_ciphertext(&secret_key, &output_ciphertext, &mut decrypted);
    // Match tfhe-rs's CMUX oracle convention: compare after rounding away the
    // encryption/external-product noise at a comfortably coarse message scale.
    let message_rounder =
        SignedDecomposer::<u64>::new(DecompositionBaseLog(4), DecompositionLevelCount(1));
    assert!(decrypted
        .iter()
        .all(|value| message_rounder.closest_representable(*value.0) == then_plaintext.0));

    eprintln!("encrypted CMUX backend: {:?}", portable.backend);
    match portable.backend {
        TorusMacBackend::Wgpu {
            adapter_name,
            backend,
        } => {
            assert!(!adapter_name.is_empty());
            assert!(!backend.is_empty());
        }
        TorusMacBackend::CpuFallback(_) => {}
        TorusMacBackend::CpuOnly => panic!("the integration gate did not request CpuOnly"),
    }
}
