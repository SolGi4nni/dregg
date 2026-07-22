//! Executable receipt for the ring-aware eight-point residual zero test.

use fhe::bfv::{Encoding, Plaintext, PublicKey, RelinearizationKey, SecretKey};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter};
use sha2::{Digest, Sha256};

use fhegg_fhe::fhir::logic_schedule::{BfvLogicEngine, DeclaredEncryptedNat, ResidualEqualityPlan};
use fhegg_fhe::fhir::logic_zero_observation::{
    residual_statement_digest, BoundedEncryptedZeroEngine, SameOpeningReceipt,
};
use fhegg_fhe::fhir::logic_zero_observation_symmetric::{
    SymmetricEightZeroEngine, SymmetricEightZeroError, SYMMETRIC_EIGHT_TRUE_SCALE,
};
use fhegg_fhe::threshold::BfvParams;

fn opening_commitment(environments: &[Vec<u64>]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(b"dregg/test/symmetric-eight-opening/v1");
    for environment in environments {
        for &value in environment {
            hash.update(value.to_le_bytes());
        }
    }
    hash.finalize().into()
}

#[test]
fn symmetric_eight_is_exact_and_uses_three_multiplications_on_real_bfv() {
    const LIVE_SLOTS: usize = 4;
    // Reuse fhEgg's existing depth-oriented degree-8192 parameter set. The
    // additive fold set is intentionally tuned for additions, not this depth.
    let params = BfvParams::correlation_set().arc().clone();
    let mut rng = rand_09::rng();
    let secret = SecretKey::random(&params, &mut rng);
    let public = PublicKey::new(&secret, &mut rng);
    let relin = RelinearizationKey::new(&secret, &mut rng).expect("relinearization key");
    let logic_engine = BfvLogicEngine::new(&relin, params.clone()).expect("logic engine");
    let generic_engine =
        BoundedEncryptedZeroEngine::new(&relin, params.clone()).expect("generic zero engine");
    let symmetric_engine =
        SymmetricEightZeroEngine::new(&relin, params.clone()).expect("symmetric zero engine");

    let compiled = logic_engine
        .compile_residual_equalities(ResidualEqualityPlan {
            pairs: (0..8).map(|pair| (2 * pair, 2 * pair + 1)).collect(),
            input_bound: 1,
        })
        .expect("eight bit equalities");
    assert_eq!(compiled.certificate().maximum_residual_sum, 8);

    let environments = vec![
        vec![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
        vec![0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
        vec![1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1],
        vec![0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1],
    ];
    // Residuals are 0, 1, 4, and 6, exercising several interior roots.
    let mut inputs = Vec::new();
    for input_index in 0..16 {
        let slots = environments
            .iter()
            .map(|environment| environment[input_index])
            .collect::<Vec<_>>();
        let plaintext =
            Plaintext::try_encode(&slots, Encoding::simd(), &params).expect("encode input");
        inputs.push(DeclaredEncryptedNat::from_declared_bound(
            public.try_encrypt(&plaintext, &mut rng).expect("encrypt"),
            1,
        ));
    }

    let commitment = opening_commitment(&environments);
    let statement = residual_statement_digest(&compiled, &inputs, commitment);
    let receipt = SameOpeningReceipt::from_external_verifier(
        statement,
        commitment,
        [0x88; 32],
        "test-only transparent constructor; no zero-knowledge verifier",
    )
    .expect("receipt");
    let generic_plan = generic_engine
        .compile(&compiled, &inputs, receipt.clone(), LIVE_SLOTS)
        .expect("generic plan");
    let stale_receipt = SameOpeningReceipt::from_external_verifier(
        [0x99; 32],
        commitment,
        [0x98; 32],
        "test-only stale statement",
    )
    .expect("stale receipt is structurally valid");
    assert!(matches!(
        symmetric_engine.compile(&compiled, &inputs, stale_receipt, LIVE_SLOTS),
        Err(SymmetricEightZeroError::SameOpeningStatementMismatch)
    ));
    let symmetric_plan = symmetric_engine
        .compile(&compiled, &inputs, receipt, LIVE_SLOTS)
        .expect("symmetric plan");

    assert_eq!(
        generic_plan
            .manifest()
            .zero_conversion_cost
            .ciphertext_multiplications,
        7
    );
    assert_eq!(
        symmetric_plan
            .manifest()
            .zero_conversion_cost
            .ciphertext_multiplications,
        3
    );
    assert_eq!(
        symmetric_plan
            .manifest()
            .zero_conversion_cost
            .output_multiplicative_depth,
        generic_plan
            .manifest()
            .zero_conversion_cost
            .output_multiplicative_depth
    );

    let generic = generic_engine
        .execute(&logic_engine, &compiled, &inputs, &generic_plan)
        .expect("generic execute");
    let symmetric = symmetric_engine
        .execute(&logic_engine, &compiled, &inputs, &symmetric_plan)
        .expect("symmetric execute");

    let generic_plain = secret
        .try_decrypt(&generic.output)
        .expect("decrypt generic");
    let symmetric_plain = secret
        .try_decrypt(&symmetric.output)
        .expect("decrypt symmetric");
    let generic_slots =
        Vec::<u64>::try_decode(&generic_plain, Encoding::simd()).expect("decode generic");
    let symmetric_slots =
        Vec::<u64>::try_decode(&symmetric_plain, Encoding::simd()).expect("decode symmetric");
    assert_eq!(SYMMETRIC_EIGHT_TRUE_SCALE, 40_320);
    assert_eq!(&generic_slots[..LIVE_SLOTS], &[40_320, 0, 0, 0]);
    assert_eq!(&symmetric_slots[..LIVE_SLOTS], &[40_320, 0, 0, 0]);

    let generic_noise =
        unsafe { secret.measure_noise(&generic.output) }.expect("generic noise measurement");
    let symmetric_noise =
        unsafe { secret.measure_noise(&symmetric.output) }.expect("symmetric noise measurement");
    println!(
        "BFV_SYMMETRIC_EIGHT_ZERO_MEASUREMENT {}",
        serde_json::json!({
            "generic_ciphertext_multiplications": 7,
            "symmetric_ciphertext_multiplications": 3,
            "residual_ciphertext_multiplications": 8,
            "generic_total_ciphertext_multiplications": 15,
            "symmetric_total_ciphertext_multiplications": 11,
            "balanced_boolean_baseline_ciphertext_multiplications": 15,
            "output_multiplicative_depth": 4,
            "generic_zero_conversion_elapsed_ns": generic.zero_conversion_elapsed.as_nanos(),
            "symmetric_zero_conversion_elapsed_ns": symmetric.zero_conversion_elapsed.as_nanos(),
            "generic_observed_noise_bits": generic_noise,
            "symmetric_observed_noise_bits": symmetric_noise,
            "opened_by_single_key_oracle": &symmetric_slots[..LIVE_SLOTS],
            "leakage": "no opening in conversion; this test then uses a single-key oracle solely to validate output/noise",
            "claim_scope": "one real BFV execution; exact algebra and exact primitive count, but no threshold margin or general noise theorem"
        })
    );
}

#[test]
fn symmetric_specialization_refuses_wrong_bound() {
    let params = BfvParams::correlation_set().arc().clone();
    let mut rng = rand_09::rng();
    let secret = SecretKey::random(&params, &mut rng);
    let public = PublicKey::new(&secret, &mut rng);
    let relin = RelinearizationKey::new(&secret, &mut rng).expect("relinearization key");
    let logic = BfvLogicEngine::new(&relin, params.clone()).expect("logic engine");
    let symmetric =
        SymmetricEightZeroEngine::new(&relin, params.clone()).expect("symmetric engine");
    let compiled = logic
        .compile_residual_equalities(ResidualEqualityPlan {
            pairs: vec![(0, 1)],
            input_bound: 1,
        })
        .expect("one equality");
    let plaintext = Plaintext::try_encode(&[0u64], Encoding::simd(), &params).expect("encode");
    let inputs = vec![
        DeclaredEncryptedNat::from_declared_bound(
            public.try_encrypt(&plaintext, &mut rng).expect("encrypt"),
            1,
        ),
        DeclaredEncryptedNat::from_declared_bound(
            public.try_encrypt(&plaintext, &mut rng).expect("encrypt"),
            1,
        ),
    ];
    let commitment = [0x22; 32];
    let statement = residual_statement_digest(&compiled, &inputs, commitment);
    let receipt = SameOpeningReceipt::from_external_verifier(
        statement,
        commitment,
        [0x33; 32],
        "test receipt",
    )
    .expect("receipt");
    assert!(matches!(
        symmetric.compile(&compiled, &inputs, receipt, 1),
        Err(SymmetricEightZeroError::WrongResidualBound { got: 1 })
    ));
}
