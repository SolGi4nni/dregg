//! Exact differential tooth for the host-parallel Ristretto prover MSM.
//!
//! This is deliberately independent of the variable-time WGPU verifier
//! experiment.  Both sides use dalek's constant-time MSM; the candidate side
//! merely schedules exact chunk sums across the retained Rayon pool.

use std::time::Instant;

use bulletproofs_r1cs::msm_backend::{
    constant_time_multiscalar_mul_parallel, constant_time_multiscalar_mul_parallel_typed,
};
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

#[test]
fn parallel_constant_time_msm_matches_single_dalek_exactly() {
    // Eight independent production-size scheduler chunks plus one term.
    const TERMS: usize = 131_073;
    let scalars: Vec<Scalar> = (0..TERMS)
        .map(|index| Scalar::from((index as u64).wrapping_mul(0x9e37_79b9) + 1))
        .collect();
    let doubled = RISTRETTO_BASEPOINT_POINT + RISTRETTO_BASEPOINT_POINT;
    let points: Vec<RistrettoPoint> = (0..TERMS)
        .map(|index| {
            if index & 1 == 0 {
                RISTRETTO_BASEPOINT_POINT
            } else {
                doubled
            }
        })
        .collect();
    let serial_started = Instant::now();
    let expected = RistrettoPoint::multiscalar_mul(&scalars, &points)
        .compress()
        .to_bytes();
    let serial = serial_started.elapsed();

    let parallel_started = Instant::now();
    let actual = constant_time_multiscalar_mul_parallel_typed(&scalars, &points)
        .expect("typed parallel prover MSM")
        .compress()
        .to_bytes();
    let parallel = parallel_started.elapsed();
    assert_eq!(actual, expected);

    eprintln!(
        "ristretto-parallel-prover terms={TERMS} serial={}us parallel={}us available_threads={} parity=exact constant_time=dalek",
        serial.as_micros(),
        parallel.as_micros(),
        std::thread::available_parallelism().map_or(1, usize::from),
    );

    let group_order = [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde,
        0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x10,
    ];
    assert!(constant_time_multiscalar_mul_parallel(
        &[group_order],
        &[RISTRETTO_BASEPOINT_POINT.compress().to_bytes()]
    )
    .is_err());
    assert!(
        constant_time_multiscalar_mul_parallel(&[Scalar::ONE.to_bytes()], &[[0xff; 32]]).is_err()
    );
}
