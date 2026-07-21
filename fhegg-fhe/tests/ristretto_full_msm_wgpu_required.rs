//! Hard-hardware tooth for the bounded complete public-scalar Ristretto MSM.

use std::time::Instant;

use bulletproofs_r1cs::msm_backend::{
    vartime_multiscalar_mul_wgpu, MsmBackendError, MAX_WGPU_MSM_TERMS,
};
use bulletproofs_r1cs::r1cs::{ConstraintSystem, Prover, Verifier};
use bulletproofs_r1cs::{BulletproofGens, PedersenGens};
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{Identity, VartimeMultiscalarMul};
use merlin::Transcript;

#[test]
#[ignore = "hardware wgpu tooth; run explicitly on hbox"]
fn required_complete_msm_matches_dalek_and_verifier_refuses_bad_boundaries() {
    assert_eq!(
        std::env::var("DREGG_BULLETPROOFS_WGPU").as_deref(),
        Ok("required")
    );

    let scalars: Vec<Scalar> = (0_u64..17)
        .map(|index| {
            Scalar::from(
                index
                    .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                    .wrapping_add(index.rotate_left(17)),
            )
        })
        .collect();
    let points: Vec<RistrettoPoint> = (0_u64..17)
        .map(|index| Scalar::from(index * index + 3 * index + 1) * RISTRETTO_BASEPOINT_POINT)
        .collect();
    let scalar_bytes: Vec<[u8; 32]> = scalars.iter().map(Scalar::to_bytes).collect();
    let point_bytes: Vec<[u8; 32]> = points
        .iter()
        .map(|point| point.compress().to_bytes())
        .collect();

    let cpu_started = Instant::now();
    let expected = RistrettoPoint::vartime_multiscalar_mul(&scalars, &points)
        .compress()
        .to_bytes();
    let cpu_elapsed = cpu_started.elapsed();
    let gpu_call_started = Instant::now();
    let result =
        vartime_multiscalar_mul_wgpu(&scalar_bytes, &point_bytes).expect("complete exact wgpu MSM");
    let gpu_call_elapsed = gpu_call_started.elapsed();
    assert!(
        result.is_hardware,
        "hard tooth selected software adapter {}",
        result.adapter_name
    );
    assert_eq!(result.term_count, scalars.len());
    assert_eq!(result.compressed_result, expected);
    eprintln!(
        "ristretto-full-msm-wgpu-cold adapter={} hardware={} terms={} cpu={}us gpu-submit={}us gpu-call={}us parity=exact",
        result.adapter_name,
        result.is_hardware,
        result.term_count,
        cpu_elapsed.as_micros(),
        result.gpu_elapsed_micros,
        gpu_call_elapsed.as_micros(),
    );

    let warm_started = Instant::now();
    let warm = vartime_multiscalar_mul_wgpu(&scalar_bytes, &point_bytes)
        .expect("warm complete exact wgpu MSM");
    let warm_elapsed = warm_started.elapsed();
    assert!(warm.is_hardware);
    assert_eq!(warm.compressed_result, expected);
    eprintln!(
        "ristretto-full-msm-wgpu-warm adapter={} terms={} gpu-submit={}us gpu-call={}us parity=exact",
        warm.adapter_name,
        warm.term_count,
        warm.gpu_elapsed_micros,
        warm_elapsed.as_micros(),
    );

    // A valid non-empty input may sum to the identity. The output is accepted
    // only after dalek validates the exact identity encoding and coordinates.
    let cancellation_scalars = [Scalar::ONE.to_bytes(), Scalar::ONE.to_bytes()];
    let cancellation_points = [
        RISTRETTO_BASEPOINT_POINT.compress().to_bytes(),
        (-RISTRETTO_BASEPOINT_POINT).compress().to_bytes(),
    ];
    let cancellation = vartime_multiscalar_mul_wgpu(&cancellation_scalars, &cancellation_points)
        .expect("exact identity-result MSM");
    assert_eq!(
        cancellation.compressed_result,
        RistrettoPoint::identity().compress().to_bytes()
    );

    assert_eq!(
        vartime_multiscalar_mul_wgpu(&[], &[]),
        Err(MsmBackendError::EmptyMsm)
    );
    assert_eq!(
        vartime_multiscalar_mul_wgpu(&[Scalar::ONE.to_bytes()], &[]),
        Err(MsmBackendError::LengthMismatch {
            scalars: 1,
            points: 0,
        })
    );
    let group_order = [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde,
        0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x10,
    ];
    assert_eq!(
        vartime_multiscalar_mul_wgpu(
            &[group_order],
            &[RISTRETTO_BASEPOINT_POINT.compress().to_bytes()]
        ),
        Err(MsmBackendError::NonCanonicalScalar { index: 0 })
    );
    assert_eq!(
        vartime_multiscalar_mul_wgpu(&[Scalar::ONE.to_bytes()], &[[0xff; 32]]),
        Err(MsmBackendError::NonCanonicalPoint { index: 0 })
    );
    assert_eq!(
        vartime_multiscalar_mul_wgpu(
            &[Scalar::ONE.to_bytes()],
            &[RistrettoPoint::identity().compress().to_bytes()]
        ),
        Err(MsmBackendError::IdentityPoint { index: 0 })
    );
    assert_eq!(
        vartime_multiscalar_mul_wgpu(
            &vec![Scalar::ZERO.to_bytes(); MAX_WGPU_MSM_TERMS + 1],
            &vec![RISTRETTO_BASEPOINT_POINT.compress().to_bytes(); MAX_WGPU_MSM_TERMS + 1]
        ),
        Err(MsmBackendError::TooManyTerms {
            terms: MAX_WGPU_MSM_TERMS + 1,
            maximum: MAX_WGPU_MSM_TERMS,
        })
    );

    // Build on the ordinary CPU path, then make the verifier's single mega-MSM
    // opt in fail-closed. A valid proof can pass only if the complete GPU MSM
    // runs on hardware and matches dalek exactly.
    std::env::set_var("DREGG_BULLETPROOFS_WGPU", "off");
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(8, 1);
    let value = Scalar::from(7_u64);
    let mut prover_transcript = Transcript::new(b"dregg.ristretto-full-msm-wgpu.required.v1");
    let mut prover = Prover::new(&pc_gens, &mut prover_transcript);
    let (commitment, variable) = prover.commit(value, Scalar::from(17_u64));
    prover.constrain(variable - value);
    let proof = prover.prove(&bp_gens).expect("CPU-authoritative proof");

    std::env::set_var("DREGG_BULLETPROOFS_WGPU", "required");
    let mut verifier_transcript = Transcript::new(b"dregg.ristretto-full-msm-wgpu.required.v1");
    let mut verifier = Verifier::new(&mut verifier_transcript);
    let verifier_variable = verifier.commit(commitment);
    verifier.constrain(verifier_variable - value);
    verifier
        .verify(&proof, &pc_gens, &bp_gens)
        .expect("CPU-authoritative verifier accepts exact required GPU MSM");
}
