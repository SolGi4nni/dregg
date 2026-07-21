//! Parity gate for the first portable torus arithmetic primitive.
//!
//! This does not test or claim a complete external product/PBS.  It anchors the
//! implemented batched polynomial MAC to tfhe-rs's own wrapping CPU primitive at
//! fhEgg's default TFHE polynomial degree.

use fhegg_fhe::tfhe_wgpu::{
    torus_negacyclic_mac_cpu, torus_negacyclic_mac_with_policy, TorusMacBackend, TorusMacPolicy,
};
use tfhe::core_crypto::algorithms::polynomial_algorithms::polynomial_wrapping_add_mul_assign;
use tfhe::core_crypto::entities::Polynomial;

fn next_u64(state: &mut u64) -> u64 {
    // Deterministic, dependency-free fixture generation.  Values intentionally
    // occupy all 64 bits so limb/carry mistakes cannot hide behind small inputs.
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

#[test]
fn portable_torus_mac_matches_tfhe_at_fhegg_default_degree() {
    // ConfigBuilder::default() in tfhe 1.6.3 selects
    // PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128, whose polynomial size is 2048.
    const DEGREE: usize = 2048;
    // The selected GLWE dimension is 1 (GLWE size 2), PBS level count is 1.
    // One coefficient-domain output row of the external-product reference shape
    // therefore accumulates two polynomial products.
    const PRODUCTS: usize = 2;

    let mut state = 0xd1ce_f00d_5eed_1234;
    let accumulator: Vec<u64> = (0..DEGREE).map(|_| next_u64(&mut state)).collect();
    let lhs: Vec<u64> = (0..DEGREE * PRODUCTS)
        .map(|_| next_u64(&mut state))
        .collect();
    let rhs: Vec<u64> = (0..DEGREE * PRODUCTS)
        .map(|_| next_u64(&mut state))
        .collect();

    let mut upstream = Polynomial::from_container(accumulator.clone());
    for (lhs_poly, rhs_poly) in lhs.chunks_exact(DEGREE).zip(rhs.chunks_exact(DEGREE)) {
        polynomial_wrapping_add_mul_assign(
            &mut upstream,
            &Polynomial::from_container(lhs_poly),
            &Polynomial::from_container(rhs_poly),
        );
    }

    let cpu = torus_negacyclic_mac_cpu(&accumulator, &lhs, &rhs, DEGREE).unwrap();
    assert_eq!(
        cpu,
        upstream.as_ref(),
        "CPU reference diverged from tfhe-rs"
    );

    let policy = if std::env::var_os("DREGG_REQUIRE_WGPU").is_some() {
        TorusMacPolicy::RequireWgpu
    } else {
        TorusMacPolicy::Auto
    };
    let portable =
        torus_negacyclic_mac_with_policy(&accumulator, &lhs, &rhs, DEGREE, policy).unwrap();
    assert_eq!(
        portable.coefficients,
        upstream.as_ref(),
        "portable torus MAC diverged from tfhe-rs via {:?}",
        portable.backend
    );
    eprintln!("torus MAC backend: {:?}", portable.backend);
    match portable.backend {
        TorusMacBackend::Wgpu { adapter_name, .. } => assert!(!adapter_name.is_empty()),
        // A capability fallback is an expected, labelled result on headless CI.
        TorusMacBackend::CpuFallback(_) => {}
        TorusMacBackend::CpuOnly => panic!("the parity target did not request CpuOnly"),
    }
}
