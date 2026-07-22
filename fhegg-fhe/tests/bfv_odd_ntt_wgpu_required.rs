//! Fail-closed production odd-NTT residency tooth.
//!
//! Run on hbox through `scripts/test-fhegg-wgpu-matrix.sh`. This test does not
//! accept a capability fallback: both directions must execute on a named wgpu
//! adapter and match the exact q0/q1/q2 CPU transform at every residue.

use fhegg_fhe::bfv_lean::{RnsPoly, FOLD_DEGREE, FOLD_MODULI};
use fhegg_fhe::bfv_ntt_gpu::{
    transform_odd_rns_cpu, verify_odd_ntt_execution, OddNttDirection, RnsNttBackend, RnsNttEngine,
    DEPLOYED_ODD_NTT_PSI,
};

fn production_input() -> RnsPoly {
    let mut state = 0x6750_4e54_545f_5747u64;
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

#[test]
#[ignore = "requires the hbox discrete GPU"]
fn production_q0_q1_q2_odd_forward_inverse_are_wgpu_resident_and_exact() {
    let input = production_input();
    let expected_forward = transform_odd_rns_cpu(&input, &FOLD_MODULI, OddNttDirection::Forward)
        .expect("CPU forward oracle");
    let engine = RnsNttEngine::new();
    let forward = engine
        .forward_odd(&input, &FOLD_MODULI)
        .expect("wgpu forward odd NTT");
    assert_eq!(forward.polynomial, expected_forward);
    assert_eq!(forward.schedule.psi, DEPLOYED_ODD_NTT_PSI);
    verify_odd_ntt_execution(&input, &FOLD_MODULI, &forward)
        .expect("forward output and schedule verify");
    let adapter = match &forward.backend {
        RnsNttBackend::Wgpu { adapter } => adapter.clone(),
        fallback => panic!("forward odd NTT did not execute on wgpu: {fallback:?}"),
    };

    let expected_inverse =
        transform_odd_rns_cpu(&expected_forward, &FOLD_MODULI, OddNttDirection::Inverse)
            .expect("CPU inverse oracle");
    let inverse = engine
        .inverse_odd(&forward.polynomial, &FOLD_MODULI)
        .expect("wgpu inverse odd NTT");
    assert_eq!(inverse.polynomial, expected_inverse);
    assert_eq!(inverse.polynomial, input, "production odd-NTT round trip");
    verify_odd_ntt_execution(&forward.polynomial, &FOLD_MODULI, &inverse)
        .expect("inverse output and schedule verify");
    match &inverse.backend {
        RnsNttBackend::Wgpu {
            adapter: inverse_adapter,
        } => assert_eq!(inverse_adapter, &adapter),
        fallback => panic!("inverse odd NTT did not execute on wgpu: {fallback:?}"),
    }

    eprintln!(
        "production scheduled odd NTT GREEN on {adapter}: \
         forward+inverse × q0/q1/q2 × 4096 exact residues"
    );
}
