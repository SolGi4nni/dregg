//! Hardware tooth for the fork-owned Bulletproofs Ristretto MSM seam.
//!
//! This target is ignored in ordinary CPU/default gauntlets because it is
//! deliberately fail-closed without a wgpu adapter.  Run it on hbox with:
//!
//! ```text
//! DREGG_REQUIRE_WGPU=1 cargo nextest run --release -p fhegg-fhe \
//!   --features amm-input-binding --test ristretto_msm_wgpu_required \
//!   --run-ignored all
//! ```

use bulletproofs_r1cs::msm_backend::{
    prepare_scalar_windows_wgpu, validate_canonical_inputs, MsmBackendError, RADIX_256_WINDOWS,
};
use bulletproofs_r1cs::r1cs::{ConstraintSystem, Prover, Verifier};
use bulletproofs_r1cs::{BulletproofGens, PedersenGens};
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

#[test]
#[ignore = "hardware wgpu tooth; run explicitly on hbox"]
fn required_wgpu_prepares_exact_windows_and_proves_through_the_owned_seam() {
    // The invoking command must set the process-wide hard gate.  A missing
    // adapter or parity mismatch then makes `Prover::prove` return an error
    // rather than silently using CPU.
    assert_eq!(std::env::var("DREGG_REQUIRE_WGPU").as_deref(), Ok("1"));

    let scalars = [Scalar::from(1_u64), Scalar::from(0x0102_0304_0506_0708_u64)];
    let scalar_bytes = scalars.map(|scalar| scalar.to_bytes());
    let prepared = prepare_scalar_windows_wgpu(&scalar_bytes).expect("required wgpu preparation");
    assert!(!prepared.adapter_name.is_empty());
    assert!(
        prepared.is_hardware,
        "hard tooth selected software adapter {}",
        prepared.adapter_name
    );
    eprintln!(
        "ristretto-msm-wgpu adapter={} hardware={} preparation_scalars={} parity_windows={}",
        prepared.adapter_name,
        prepared.is_hardware,
        prepared.scalar_count,
        prepared.windows.len()
    );
    assert_eq!(prepared.scalar_count, scalars.len());
    assert_eq!(prepared.windows.len(), scalars.len() * RADIX_256_WINDOWS);
    for (index, bytes) in scalar_bytes.iter().enumerate() {
        assert_eq!(
            &prepared.windows[index * RADIX_256_WINDOWS..(index + 1) * RADIX_256_WINDOWS],
            bytes
        );
    }

    let points = [
        RISTRETTO_BASEPOINT_POINT.compress().to_bytes(),
        (Scalar::from(9_u64) * RISTRETTO_BASEPOINT_POINT)
            .compress()
            .to_bytes(),
    ];
    validate_canonical_inputs(&scalar_bytes, &points).expect("canonical typed inputs");

    let group_order = [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde,
        0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x10,
    ];
    assert_eq!(
        prepare_scalar_windows_wgpu(&[group_order]),
        Err(MsmBackendError::NonCanonicalScalar { index: 0 })
    );

    // A real R1CS proof exercises A_I1, A_O1, and S1 through the new seam.  If
    // the hard wgpu stage did not execute successfully, proof creation fails.
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(8, 1);
    let blinding = Scalar::from(17_u64);
    let value = Scalar::from(7_u64);
    let mut prover_transcript = Transcript::new(b"dregg.ristretto-msm-wgpu.required.v1");
    let mut prover = Prover::new(&pc_gens, &mut prover_transcript);
    let (commitment, variable) = prover.commit(value, blinding);
    prover.constrain(variable - value);
    let proof = prover.prove(&bp_gens).expect("hard-wgpu R1CS proof");

    let mut verifier_transcript = Transcript::new(b"dregg.ristretto-msm-wgpu.required.v1");
    let mut verifier = Verifier::new(&mut verifier_transcript);
    let verifier_variable = verifier.commit(commitment);
    verifier.constrain(verifier_variable - value);
    verifier
        .verify(&proof, &pc_gens, &bp_gens)
        .expect("dalek verifier accepts GPU-prepared proof");
}
