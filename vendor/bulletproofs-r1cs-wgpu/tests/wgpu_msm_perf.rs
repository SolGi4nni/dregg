//! Isolated hardware parity/timing tooth for the bounded public-scalar MSM.

#![cfg(feature = "wgpu-msm")]

use std::time::Instant;

use bulletproofs::msm_backend::vartime_multiscalar_mul_wgpu;
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;

fn deterministic_scalar(domain: u64, index: u64) -> Scalar {
    let mut state = domain ^ index.wrapping_mul(0x9e37_79b9_7f4a_7c15);
    let mut wide = [0_u8; 64];
    for chunk in wide.chunks_exact_mut(8) {
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        state = state.wrapping_mul(0x2545_f491_4f6c_dd1d);
        chunk.copy_from_slice(&state.to_le_bytes());
    }
    Scalar::from_bytes_mod_order_wide(&wide)
}

#[test]
#[ignore = "hardware timing tooth; run explicitly on hbox"]
fn exact_public_msm_matrix() {
    assert_eq!(
        std::env::var("DREGG_BULLETPROOFS_WGPU").as_deref(),
        Ok("required")
    );
    let scalars: Vec<Scalar> = (0_u64..4096)
        .map(|index| deterministic_scalar(0x5343_414c_4152, index))
        .collect();
    let points: Vec<RistrettoPoint> = (0_u64..4096)
        .map(|index| deterministic_scalar(0x504f_494e_5453, index) * RISTRETTO_BASEPOINT_POINT)
        .collect();
    let scalar_bytes: Vec<[u8; 32]> = scalars.iter().map(Scalar::to_bytes).collect();
    let point_bytes: Vec<[u8; 32]> = points
        .iter()
        .map(|point| point.compress().to_bytes())
        .collect();

    // Initialize and compile outside the warm matrix.
    let cold_started = Instant::now();
    let cold = vartime_multiscalar_mul_wgpu(&scalar_bytes[..17], &point_bytes[..17])
        .expect("cold exact GPU MSM");
    eprintln!(
        "ristretto-msm-isolated-cold adapter={} terms=17 submit={}us call={}us",
        cold.adapter_name,
        cold.gpu_elapsed_micros,
        cold_started.elapsed().as_micros(),
    );

    for terms in [17_usize, 256, 1024, 4096] {
        let cpu_started = Instant::now();
        let expected = RistrettoPoint::vartime_multiscalar_mul(&scalars[..terms], &points[..terms])
            .compress()
            .to_bytes();
        let cpu_micros = cpu_started.elapsed().as_micros();
        let gpu_started = Instant::now();
        let result = vartime_multiscalar_mul_wgpu(&scalar_bytes[..terms], &point_bytes[..terms])
            .expect("warm exact GPU MSM");
        let gpu_call_micros = gpu_started.elapsed().as_micros();
        assert!(result.is_hardware);
        assert_eq!(result.compressed_result, expected);
        eprintln!(
            "ristretto-msm-isolated adapter={} terms={} cpu={}us submit={}us call={}us window_bits={} windows={} buckets={} chunks={} parity=exact",
            result.adapter_name,
            terms,
            cpu_micros,
            result.gpu_elapsed_micros,
            gpu_call_micros,
            result.window_bits,
            result.window_count,
            result.bucket_count,
            result.chunk_count,
        );
    }
}
