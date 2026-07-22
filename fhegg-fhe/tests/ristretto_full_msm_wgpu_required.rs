//! Hard-hardware tooth for the bounded complete public-scalar Ristretto MSM.
//!
//! On hbox's RX 6750 XT the adaptive radix-16/radix-128 exact warm
//! 17/256/1024/4096 matrix remained much slower than dalek (about
//! 0.97/1.29/2.33/4.64 seconds versus 0.22/1.03/2.99/9.83 milliseconds).
//! This is a required-mode qualification tooth, not evidence for enabling the
//! default-disabled verifier backend.

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
use sha2::{Digest, Sha512};

fn deterministic_scalar(domain: u8, index: u64) -> Scalar {
    let mut seed = [0_u8; 9];
    seed[0] = domain;
    seed[1..].copy_from_slice(&index.to_le_bytes());
    let digest = Sha512::digest(seed);
    let mut wide = [0_u8; 64];
    wide.copy_from_slice(&digest);
    Scalar::from_bytes_mod_order_wide(&wide)
}

#[test]
#[ignore = "hardware wgpu tooth; run explicitly on hbox"]
fn required_complete_msm_matches_dalek_and_verifier_refuses_bad_boundaries() {
    assert_eq!(
        std::env::var("DREGG_BULLETPROOFS_WGPU").as_deref(),
        Ok("required")
    );

    let scalars: Vec<Scalar> = (0_u64..MAX_WGPU_MSM_TERMS as u64)
        .map(|index| deterministic_scalar(0x53, index))
        .collect();
    let points: Vec<RistrettoPoint> = (0_u64..MAX_WGPU_MSM_TERMS as u64)
        .map(|index| deterministic_scalar(0x50, index) * RISTRETTO_BASEPOINT_POINT)
        .collect();
    let scalar_bytes: Vec<[u8; 32]> = scalars.iter().map(Scalar::to_bytes).collect();
    let point_bytes: Vec<[u8; 32]> = points
        .iter()
        .map(|point| point.compress().to_bytes())
        .collect();

    // Pay and report one cold device/pipeline initialization separately. The
    // production cache is then shared by the exact 17/256/1024/4096 matrix.
    let cold_started = Instant::now();
    let cold = vartime_multiscalar_mul_wgpu(&scalar_bytes[..17], &point_bytes[..17])
        .expect("cold exact wgpu MSM");
    let cold_elapsed = cold_started.elapsed();
    assert!(
        cold.is_hardware,
        "hard tooth selected software adapter {}",
        cold.adapter_name
    );
    eprintln!(
        "ristretto-full-msm-wgpu-cold adapter={} hardware={} terms={} gpu-submit={}us gpu-call={}us parity=exact",
        cold.adapter_name,
        cold.is_hardware,
        cold.term_count,
        cold.gpu_elapsed_micros,
        cold_elapsed.as_micros(),
    );

    for terms in [17_usize, 256, 1024, 4096] {
        let cpu_started = Instant::now();
        let expected = RistrettoPoint::vartime_multiscalar_mul(&scalars[..terms], &points[..terms])
            .compress()
            .to_bytes();
        let cpu_elapsed = cpu_started.elapsed();
        let gpu_call_started = Instant::now();
        let result = vartime_multiscalar_mul_wgpu(&scalar_bytes[..terms], &point_bytes[..terms])
            .expect("warm exact wgpu MSM matrix row");
        let gpu_call_elapsed = gpu_call_started.elapsed();
        assert!(result.is_hardware);
        assert_eq!(result.term_count, terms);
        assert_eq!(result.compressed_result, expected);
        let (window_bits, chunk_terms) = if terms < 2_048 {
            (4_u32, 64_u32)
        } else {
            (7_u32, 256_u32)
        };
        assert_eq!(result.window_bits, window_bits);
        assert_eq!(result.window_count, 256_u32.div_ceil(window_bits));
        assert_eq!(result.bucket_count, (1_u32 << window_bits) - 1);
        assert_eq!(result.chunk_count, (terms as u32).div_ceil(chunk_terms));
        assert_eq!(
            result.partial_bucket_count,
            result.window_count * result.chunk_count * result.bucket_count
        );
        assert_eq!(result.dispatch_count, 4);
        assert_eq!(result.readback_count, 1);
        eprintln!(
            "ristretto-full-msm-wgpu-matrix adapter={} terms={} cpu={}us gpu-submit={}us gpu-call={}us chunks={} partial-buckets={} bucket-tests={} nonzero-digits={} post-add-upper={} dispatches={} readbacks={} parity=exact",
            result.adapter_name,
            result.term_count,
            cpu_elapsed.as_micros(),
            result.gpu_elapsed_micros,
            gpu_call_elapsed.as_micros(),
            result.chunk_count,
            result.partial_bucket_count,
            result.bucket_term_tests,
            result.nonzero_digits,
            result.post_bucket_addition_upper_bound,
            result.dispatch_count,
            result.readback_count,
        );
    }

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
