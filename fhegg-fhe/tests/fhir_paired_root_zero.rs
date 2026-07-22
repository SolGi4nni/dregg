//! Differential and hostile tests for the complementary-root fhIR lowering.

use fhe::bfv::{Encoding, Plaintext, PublicKey, RelinearizationKey, SecretKey};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter};
use sha2::{Digest, Sha256};

use fhegg_fhe::fhir::logic_schedule::{BfvLogicEngine, DeclaredEncryptedNat, ResidualEqualityPlan};
use fhegg_fhe::fhir::logic_zero_observation::{
    residual_statement_digest, BoundedEncryptedZeroEngine, SameOpeningReceipt,
};
use fhegg_fhe::fhir_paired_root_zero::{
    paired_root_indicator_mod, PairedRootZeroEngine, PairedRootZeroError,
};
use fhegg_fhe::threshold::BfvParams;

fn generic_indicator_mod(residual: u64, bound: u64, modulus: u64) -> u64 {
    (1..=bound).fold(1, |acc, root| {
        let factor = (root + modulus - residual) % modulus;
        ((u128::from(acc) * u128::from(factor)) % u128::from(modulus)) as u64
    })
}

fn opening_commitment(environments: &[Vec<u64>]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(b"dregg/test/paired-root-zero-opening/v1");
    for environment in environments {
        for &value in environment {
            hash.update(value.to_le_bytes());
        }
    }
    hash.finalize().into()
}

#[test]
fn scalar_pairing_matches_every_generic_root_and_refuses_out_of_domain() {
    const MODULUS: u64 = 1_032_193;
    for bound in 4..=128 {
        for residual in 0..=bound {
            assert_eq!(
                paired_root_indicator_mod(residual, bound, MODULUS).unwrap(),
                generic_indicator_mod(residual, bound, MODULUS),
                "bound={bound}, residual={residual}"
            );
        }
    }
    assert!(matches!(
        paired_root_indicator_mod(17, 16, MODULUS),
        Err(PairedRootZeroError::ScalarDomainViolation { .. })
    ));
    assert!(matches!(
        paired_root_indicator_mod(0, 3, MODULUS),
        Err(PairedRootZeroError::UnsupportedResidualBound { bound: 3 })
    ));
}

#[test]
fn real_bfv_bound_sixteen_matches_generic_with_seven_fewer_multiplications() {
    const LIVE_SLOTS: usize = 4;
    const BOUND: usize = 16;
    let params = BfvParams::correlation_set().arc().clone();
    let mut rng = rand_09::rng();
    let secret = SecretKey::random(&params, &mut rng);
    let public = PublicKey::new(&secret, &mut rng);
    let relin = RelinearizationKey::new(&secret, &mut rng).expect("relinearization key");
    let logic = BfvLogicEngine::new(&relin, params.clone()).expect("logic engine");
    let generic = BoundedEncryptedZeroEngine::new(&relin, params.clone()).expect("generic engine");
    let paired = PairedRootZeroEngine::new(&relin, params.clone()).expect("paired engine");

    let compiled = logic
        .compile_residual_equalities(ResidualEqualityPlan {
            pairs: (0..BOUND).map(|pair| (2 * pair, 2 * pair + 1)).collect(),
            input_bound: 1,
        })
        .expect("bound-sixteen residual");
    assert_eq!(compiled.certificate().maximum_residual_sum, BOUND as u128);

    let mismatch_counts = [0usize, 1, 7, 16];
    let environments = mismatch_counts
        .into_iter()
        .map(|mismatches| {
            (0..BOUND)
                .flat_map(|pair| [0, u64::from(pair < mismatches)])
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut inputs = Vec::new();
    for input_index in 0..2 * BOUND {
        let slots = environments
            .iter()
            .map(|environment| environment[input_index])
            .collect::<Vec<_>>();
        let plaintext = Plaintext::try_encode(&slots, Encoding::simd(), &params).expect("encode");
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
        [0x61; 32],
        "test-only transparent receipt",
    )
    .expect("same-opening receipt");
    let generic_plan = generic
        .compile(&compiled, &inputs, receipt.clone(), LIVE_SLOTS)
        .expect("generic plan");
    let paired_plan = paired
        .compile(&compiled, &inputs, receipt, LIVE_SLOTS)
        .expect("paired plan");
    assert_eq!(
        generic_plan
            .manifest()
            .zero_conversion_cost
            .ciphertext_multiplications,
        15
    );
    assert_eq!(
        paired_plan
            .manifest()
            .zero_conversion_cost
            .ciphertext_multiplications,
        8
    );
    assert_eq!(
        paired_plan
            .manifest()
            .certificate
            .saved_ciphertext_multiplications,
        7
    );
    assert!(paired_plan.manifest().certificate.depth_preserved);

    let generic_execution = generic
        .execute(&logic, &compiled, &inputs, &generic_plan)
        .expect("generic execute");
    let paired_execution = paired
        .execute(&logic, &compiled, &inputs, &paired_plan)
        .expect("paired execute");
    let generic_plain = secret
        .try_decrypt(&generic_execution.output)
        .expect("decrypt generic");
    let paired_plain = secret
        .try_decrypt(&paired_execution.output)
        .expect("decrypt paired");
    let generic_slots =
        Vec::<u64>::try_decode(&generic_plain, Encoding::simd()).expect("decode generic");
    let paired_slots =
        Vec::<u64>::try_decode(&paired_plain, Encoding::simd()).expect("decode paired");
    assert_eq!(&paired_slots[..LIVE_SLOTS], &generic_slots[..LIVE_SLOTS]);
    assert_eq!(paired_slots[0], paired_plan.manifest().true_scale);
    assert_eq!(&paired_slots[1..LIVE_SLOTS], &[0, 0, 0]);
}

#[test]
fn stale_receipt_and_cross_plan_substitution_fail_closed() {
    let params = BfvParams::correlation_set().arc().clone();
    let mut rng = rand_09::rng();
    let secret = SecretKey::random(&params, &mut rng);
    let public = PublicKey::new(&secret, &mut rng);
    let relin = RelinearizationKey::new(&secret, &mut rng).expect("relinearization key");
    let logic = BfvLogicEngine::new(&relin, params.clone()).expect("logic engine");
    let paired = PairedRootZeroEngine::new(&relin, params.clone()).expect("paired engine");
    let zero = Plaintext::try_encode(&[0u64], Encoding::simd(), &params).expect("encode");
    let inputs = (0..10)
        .map(|_| {
            DeclaredEncryptedNat::from_declared_bound(
                public.try_encrypt(&zero, &mut rng).expect("encrypt"),
                1,
            )
        })
        .collect::<Vec<_>>();
    let first = logic
        .compile_residual_equalities(ResidualEqualityPlan {
            pairs: vec![(0, 1), (2, 3), (4, 5), (6, 7)],
            input_bound: 1,
        })
        .expect("first plan");
    let second = logic
        .compile_residual_equalities(ResidualEqualityPlan {
            pairs: vec![(1, 0), (2, 3), (4, 5), (6, 7)],
            input_bound: 1,
        })
        .expect("second plan");
    let commitment = [0x41; 32];
    let stale = SameOpeningReceipt::from_external_verifier(
        [0x42; 32],
        commitment,
        [0x43; 32],
        "stale test receipt",
    )
    .expect("structurally valid stale receipt");
    assert!(matches!(
        paired.compile(&first, &inputs, stale, 1),
        Err(PairedRootZeroError::SameOpeningStatementMismatch)
    ));

    let statement = residual_statement_digest(&first, &inputs, commitment);
    let receipt = SameOpeningReceipt::from_external_verifier(
        statement,
        commitment,
        [0x44; 32],
        "bound test receipt",
    )
    .expect("receipt");
    let plan = paired.compile(&first, &inputs, receipt, 1).expect("plan");
    assert!(matches!(
        paired.execute(&logic, &second, &inputs, &plan),
        Err(PairedRootZeroError::ManifestDrift)
    ));
}
