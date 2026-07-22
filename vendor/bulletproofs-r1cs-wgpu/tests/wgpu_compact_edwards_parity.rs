//! Hard-adapter parity and geometry tooth for compact Edwards arithmetic.

#![cfg(feature = "wgpu-msm")]

use bulletproofs::compact_edwards_wgpu::{
    add_compressed_point_pairs_compact_wgpu, compact_edwards_geometry_wgpu, CompactEdwardsError,
    COMPACT_POINT_BYTES,
};
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;

fn point(index: usize, domain: u64) -> RistrettoPoint {
    if index % 127 == 0 {
        return RistrettoPoint::identity();
    }
    let value = (index as u64)
        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .wrapping_add(domain);
    Scalar::from(value) * RISTRETTO_BASEPOINT_POINT
}

#[test]
#[ignore = "hardware WGPU tooth; run explicitly on hbox"]
fn compact_edwards_matches_dalek_at_boundaries_and_production_geometry_fits() {
    assert_eq!(std::env::var("DREGG_REQUIRE_WGPU").as_deref(), Ok("1"));

    let production_pairs = 1_usize << 21;
    let geometry =
        compact_edwards_geometry_wgpu(production_pairs).expect("actual-adapter compact geometry");
    assert!(
        geometry.is_hardware,
        "hard tooth selected software adapter {}",
        geometry.adapter_name
    );
    assert_eq!(
        geometry.input_bytes,
        2 * production_pairs as u64 * COMPACT_POINT_BYTES
    );
    assert_eq!(
        geometry.output_bytes,
        production_pairs as u64 * COMPACT_POINT_BYTES
    );
    assert_eq!(geometry.input_bytes, 1_342_177_280);
    assert_eq!(geometry.workgroups, 32_768);
    assert!(geometry.fits_adapter_limits, "{:?}", geometry);

    let pair_points: Vec<(RistrettoPoint, RistrettoPoint)> = (0..4096)
        .map(|index| {
            let left = point(index, 0x4c45_4654);
            let right = if index % 131 == 0 {
                -left
            } else {
                point(index, 0x5249_4748_54)
            };
            (left, right)
        })
        .collect();
    let pairs: Vec<([u8; 32], [u8; 32])> = pair_points
        .iter()
        .map(|(left, right)| (left.compress().to_bytes(), right.compress().to_bytes()))
        .collect();

    for count in [1_usize, 2, 63, 64, 65, 4096] {
        let result = add_compressed_point_pairs_compact_wgpu(&pairs[..count])
            .expect("exact compact GPU additions");
        assert!(result.is_hardware, "adapter={}", result.adapter_name);
        assert_eq!(result.compressed_sums.len(), count);
        for (index, ((left, right), actual)) in pair_points[..count]
            .iter()
            .zip(&result.compressed_sums)
            .enumerate()
        {
            assert_eq!(
                *actual,
                (*left + *right).compress().to_bytes(),
                "dalek parity mismatch at N={count}, pair={index}"
            );
        }
    }

    let malformed = [0xff_u8; 32];
    assert_eq!(
        add_compressed_point_pairs_compact_wgpu(&[(
            malformed,
            RISTRETTO_BASEPOINT_POINT.compress().to_bytes(),
        )]),
        Err(CompactEdwardsError::NonCanonicalPoint { index: 0 })
    );

    eprintln!(
        "compact-edwards adapter={} input_bytes={} output_bytes={} workgroups={} parity_counts=1,2,63,64,65,4096",
        geometry.adapter_name, geometry.input_bytes, geometry.output_bytes, geometry.workgroups
    );
}
