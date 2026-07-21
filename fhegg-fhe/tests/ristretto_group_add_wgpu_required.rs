//! Hard-hardware parity tooth for exact wgpu extended-Edwards addition.

use bulletproofs_r1cs::msm_backend::{add_compressed_point_pairs_wgpu, MsmBackendError};
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;

#[test]
#[ignore = "hardware wgpu tooth; run explicitly on hbox"]
fn required_wgpu_group_add_matches_canonical_dalek_bytes_and_refuses_malformed_points() {
    assert_eq!(std::env::var("DREGG_REQUIRE_WGPU").as_deref(), Ok("1"));

    let identity = RistrettoPoint::identity();
    let base = RISTRETTO_BASEPOINT_POINT;
    let p = Scalar::from(0x1234_5678_9abc_def0_u64) * base;
    let q = Scalar::from(0xfedc_ba98_7654_3210_u64) * base;
    let points = [
        identity,
        base,
        base + base,
        p,
        q,
        -p,
        Scalar::from(31_u64) * q,
    ];
    let pair_points = [
        (points[0], points[1]),
        (points[1], points[0]),
        (points[1], points[1]),
        (points[3], points[5]),
        (points[3], points[4]),
        (points[4], points[3]),
        (points[6], points[2]),
    ];
    let pairs: Vec<([u8; 32], [u8; 32])> = pair_points
        .iter()
        .map(|(left, right)| (left.compress().to_bytes(), right.compress().to_bytes()))
        .collect();

    let result = add_compressed_point_pairs_wgpu(&pairs).expect("exact GPU group additions");
    assert!(
        result.is_hardware,
        "hard tooth selected software adapter {}",
        result.adapter_name
    );
    assert_eq!(result.compressed_sums.len(), pairs.len());
    for (index, ((left, right), compressed)) in
        pair_points.iter().zip(&result.compressed_sums).enumerate()
    {
        let expected = (*left + *right).compress().to_bytes();
        assert_eq!(*compressed, expected, "dalek mismatch at pair {index}");
        let roundtrip = CompressedRistretto(*compressed)
            .decompress()
            .expect("GPU sum is canonical Ristretto");
        assert_eq!(roundtrip.compress().to_bytes(), *compressed);
    }
    eprintln!(
        "ristretto-group-add-wgpu adapter={} hardware={} pairs={} canonical_roundtrips={}",
        result.adapter_name,
        result.is_hardware,
        pairs.len(),
        result.compressed_sums.len()
    );

    let malformed = [0xff_u8; 32];
    assert_eq!(
        add_compressed_point_pairs_wgpu(&[(malformed, base.compress().to_bytes())]),
        Err(MsmBackendError::NonCanonicalPoint { index: 0 })
    );

    // The additive dalek import refuses both a malformed field alias and an
    // on-curve/extended tuple whose quotient point is not the CPU oracle.
    let expected = (p + q).compress();
    let mut coordinates = (p + q).dregg_extended_coordinates();
    coordinates[0] = [0xff; 32];
    assert!(
        RistrettoPoint::dregg_from_extended_coordinates_checked(&coordinates, &expected).is_none()
    );
    let mut wrong_point = (p + q).dregg_extended_coordinates();
    wrong_point[1][0] ^= 1;
    assert!(
        RistrettoPoint::dregg_from_extended_coordinates_checked(&wrong_point, &expected).is_none()
    );
}
