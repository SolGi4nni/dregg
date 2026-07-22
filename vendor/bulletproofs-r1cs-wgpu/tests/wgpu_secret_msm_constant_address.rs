//! Hard-adapter tooth for the isolated constant-address witness MSM.

#![cfg(feature = "wgpu-msm")]

use bulletproofs::compact_edwards_wgpu::{
    constant_address_secret_multiscalar_mul_compact_wgpu, CompactEdwardsError,
};
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{Identity, MultiscalarMul};

fn dense_secret_scalar(index: usize) -> Scalar {
    if index == 0 {
        return Scalar::ZERO;
    }
    if index == 1 {
        return Scalar::ONE;
    }
    let mut state = (index as u64) ^ 0x5345_4352_4554_4d53;
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

fn public_point(index: usize) -> RistrettoPoint {
    if index % 19 == 0 {
        return RistrettoPoint::identity();
    }
    Scalar::from(
        (index as u64)
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .wrapping_add(0x5055_424c_4943_5054),
    ) * RISTRETTO_BASEPOINT_POINT
}

#[test]
#[ignore = "hardware WGPU witness tooth; run explicitly on hbox"]
fn secret_msm_is_exact_fixed_schedule_final_read_only_and_fail_closed() {
    assert_eq!(std::env::var("DREGG_REQUIRE_WGPU").as_deref(), Ok("1"));

    let scalars: Vec<Scalar> = (0..64).map(dense_secret_scalar).collect();
    let points: Vec<RistrettoPoint> = (0..64).map(public_point).collect();
    let scalar_bytes: Vec<[u8; 32]> = scalars.iter().map(Scalar::to_bytes).collect();
    let point_bytes: Vec<[u8; 32]> = points
        .iter()
        .map(|point| point.compress().to_bytes())
        .collect();

    for terms in [1_usize, 2, 64] {
        let expected = RistrettoPoint::multiscalar_mul(&scalars[..terms], &points[..terms])
            .compress()
            .to_bytes();
        let result = constant_address_secret_multiscalar_mul_compact_wgpu(
            &scalar_bytes[..terms],
            &point_bytes[..terms],
        )
        .expect("exact constant-address witness MSM");
        assert!(
            result.is_hardware,
            "hard tooth selected software adapter {}",
            result.adapter_name
        );
        assert_eq!(result.term_count, terms);
        assert_eq!(result.point_upload_count, 1);
        assert_eq!(result.scalar_upload_count, 1);
        assert_eq!(result.control_upload_count, 1);
        assert_eq!(result.dispatch_count, 1 + terms.trailing_zeros());
        assert_eq!(result.readback_count, 1);
        assert_eq!(result.witness_buffer_scrub_count, 4);
        assert_eq!(result.compressed_result, expected);
        eprintln!(
            "secret-msm-constant-address adapter={} terms={} dispatches={} readbacks={} witness_scrubs={} parity=exact",
            result.adapter_name,
            terms,
            result.dispatch_count,
            result.readback_count,
            result.witness_buffer_scrub_count,
        );
    }

    assert_eq!(
        constant_address_secret_multiscalar_mul_compact_wgpu(&scalar_bytes[..1], &point_bytes[..2]),
        Err(CompactEdwardsError::SecretMsmLengthMismatch {
            scalars: 1,
            points: 2,
        })
    );
    assert_eq!(
        constant_address_secret_multiscalar_mul_compact_wgpu(&[], &[]),
        Err(CompactEdwardsError::EmptySecretMsm)
    );
    assert_eq!(
        constant_address_secret_multiscalar_mul_compact_wgpu(&scalar_bytes[..3], &point_bytes[..3],),
        Err(CompactEdwardsError::SecretMsmNonPowerOfTwo { terms: 3 })
    );
    let noncanonical_scalar = [0xff_u8; 32];
    assert_eq!(
        constant_address_secret_multiscalar_mul_compact_wgpu(
            &[noncanonical_scalar],
            &point_bytes[..1],
        ),
        Err(CompactEdwardsError::NonCanonicalScalar { index: 0 })
    );
    let malformed_point = [0xff_u8; 32];
    assert_eq!(
        constant_address_secret_multiscalar_mul_compact_wgpu(
            &scalar_bytes[..1],
            &[malformed_point],
        ),
        Err(CompactEdwardsError::NonCanonicalPoint { index: 0 })
    );
}
