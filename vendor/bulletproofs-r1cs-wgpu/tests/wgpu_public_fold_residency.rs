//! Hard-adapter residency tooth for predetermined-public generator folds.

#![cfg(feature = "wgpu-msm")]

use bulletproofs::compact_edwards_wgpu::{
    fold_points_with_predetermined_public_challenges_compact_wgpu,
    predetermined_public_fold_challenges, CompactEdwardsError,
};
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;

fn public_point(index: usize) -> RistrettoPoint {
    if index % 17 == 0 {
        return RistrettoPoint::identity();
    }
    let word = (index as u64)
        .wrapping_mul(0xd6e8_feb8_6659_fd93)
        .wrapping_add(0x5055_424c_4943_5054);
    Scalar::from(word) * RISTRETTO_BASEPOINT_POINT
}

fn dalek_fold(mut points: Vec<RistrettoPoint>, rounds: usize) -> Vec<[u8; 32]> {
    for (left_bytes, right_bytes) in predetermined_public_fold_challenges(rounds) {
        let left = Option::<Scalar>::from(Scalar::from_canonical_bytes(left_bytes))
            .expect("fixed public inverse challenge");
        let right = Option::<Scalar>::from(Scalar::from_canonical_bytes(right_bytes))
            .expect("fixed public challenge");
        let half = points.len() / 2;
        points = (0..half)
            .map(|index| left * points[index] + right * points[index + half])
            .collect();
    }
    points
        .iter()
        .map(|point| point.compress().to_bytes())
        .collect()
}

#[test]
#[ignore = "hardware WGPU residency tooth; run explicitly on hbox"]
fn predetermined_public_fold_uploads_once_folds_k_times_and_reads_once() {
    assert_eq!(std::env::var("DREGG_REQUIRE_WGPU").as_deref(), Ok("1"));

    let points: Vec<RistrettoPoint> = (0..64).map(public_point).collect();
    let point_bytes: Vec<[u8; 32]> = points
        .iter()
        .map(|point| point.compress().to_bytes())
        .collect();

    // Odd and even K exercise both final ping-pong buffers. All intermediate
    // vectors remain device-resident in each call.
    for rounds in [5_usize, 6] {
        let expected = dalek_fold(points.clone(), rounds);
        let result =
            fold_points_with_predetermined_public_challenges_compact_wgpu(&point_bytes, rounds)
                .expect("exact predetermined-public resident fold");
        assert!(
            result.is_hardware,
            "hard tooth selected software adapter {}",
            result.adapter_name
        );
        assert_eq!(result.initial_point_count, 64);
        assert_eq!(result.final_point_count, 64 >> rounds);
        assert_eq!(result.round_count, rounds);
        assert_eq!(result.point_upload_count, 1);
        assert_eq!(result.challenge_upload_count, 1);
        assert_eq!(result.control_upload_count, 1);
        assert_eq!(result.dispatch_count, rounds as u32);
        assert_eq!(result.readback_count, 1);
        assert_eq!(result.compressed_points, expected);
        eprintln!(
            "public-fold-resident adapter={} initial={} rounds={} final={} point_uploads={} challenge_uploads={} control_uploads={} dispatches={} readbacks={} parity=exact",
            result.adapter_name,
            result.initial_point_count,
            result.round_count,
            result.final_point_count,
            result.point_upload_count,
            result.challenge_upload_count,
            result.control_upload_count,
            result.dispatch_count,
            result.readback_count,
        );
    }

    assert_eq!(
        fold_points_with_predetermined_public_challenges_compact_wgpu(&point_bytes[..6], 2),
        Err(CompactEdwardsError::InvalidFoldShape {
            points: 6,
            rounds: 2,
        })
    );
    let malformed = [0xff_u8; 32];
    assert_eq!(
        fold_points_with_predetermined_public_challenges_compact_wgpu(
            &[malformed, RISTRETTO_BASEPOINT_POINT.compress().to_bytes()],
            1,
        ),
        Err(CompactEdwardsError::NonCanonicalPoint { index: 0 })
    );
}
