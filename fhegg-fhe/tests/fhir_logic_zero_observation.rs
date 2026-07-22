//! Real threshold zero observation for the corrected finite-logic residual.
//!
//! This test owns no joint secret key.  Two parties form a collective BFV key
//! and a matching multiparty relinearization key, encrypted Boolean openings
//! are evaluated as one residual ciphertext, and only that residual is opened
//! through the n-of-n smudged threshold path.  The receipt records the complete
//! residual-value leakage and remains fail-closed for the term "end-to-end"
//! because setup, encryption, and the external same-opening proof verifier are
//! not part of the boundary function's timed coverage.

use std::time::{Duration, Instant};

use fhe::bfv::{BfvParameters, Encoding, Plaintext, PublicKey, RelinearizationKey, SecretKey};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter};
use sha2::{Digest, Sha256};

use fhegg_fhe::additive::pick_params;
use fhegg_fhe::fhir::logic_schedule::{
    BfvCostManifest, BfvLogicEngine, DeclaredEncryptedNat, ResidualEqualityPlan,
};
use fhegg_fhe::fhir::logic_zero_observation::{
    compile_threshold_zero_observation, execute_final_threshold_zero_observation,
    execute_threshold_scaled_bit_observation, residual_statement_digest,
    BoundedEncryptedZeroEngine, SameOpeningReceipt, ZeroObservationError,
};
use fhegg_fhe::threshold::relin::{generate_relinearization_key, RelinKeySession};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};

fn collective_keygen(
    n: usize,
    params: &BfvParams,
) -> (KeygenSession, CollectivePublicKey, Vec<ThresholdParty>) {
    let session = KeygenSession::from_seed(n, [0x61; 32]).expect("keygen session");
    let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
    let mut parties = Vec::with_capacity(n);
    for party_index in 0..n {
        let root = [0x71 + party_index as u8; 32];
        let (party, contribution) =
            ThresholdParty::join_seeded(&session, party_index, params, &root)
                .expect("party keygen");
        coordinator
            .accept(contribution)
            .expect("public contribution");
        parties.push(party);
    }
    let collective = coordinator.finish().expect("collective public key");
    (session, collective, parties)
}

fn opening_commitment(environments: &[Vec<u64>]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(b"dregg/test/transparent-logic-opening/v1");
    hash.update((environments.len() as u64).to_le_bytes());
    for environment in environments {
        hash.update((environment.len() as u64).to_le_bytes());
        for &value in environment {
            hash.update(value.to_le_bytes());
        }
    }
    hash.finalize().into()
}

#[test]
fn residual_threshold_boundary_executes_prices_and_discloses_exactly_what_it_opens() {
    const PARTIES: usize = 2;
    const LIVE_SLOTS: usize = 4;

    let setup_started = Instant::now();
    let params = BfvParams::fold_set();
    let (keygen, collective, parties) = collective_keygen(PARTIES, &params);
    let relin_session = RelinKeySession::from_public_entropy(
        &keygen,
        &collective,
        [0x52; 32],
        Duration::from_secs(90),
    )
    .expect("relinearization session");
    let relin = generate_relinearization_key(&relin_session, &params, &collective, &parties)
        .expect("party-owned relinearization key");
    let engine = BfvLogicEngine::new(&relin, params.arc().clone()).expect("logic engine");
    let setup_elapsed = setup_started.elapsed();

    let pairs: Vec<(usize, usize)> = (0..8).map(|pair| (2 * pair, 2 * pair + 1)).collect();
    let residual_plan = ResidualEqualityPlan {
        pairs,
        input_bound: 1,
    };
    let compiled = engine
        .compile_residual_equalities(residual_plan)
        .expect("eight bit equalities fit the no-wrap window");
    assert_eq!(compiled.certificate().maximum_residual_sum, 8);
    assert_eq!(
        compiled.cost(),
        &BfvCostManifest {
            logical_input_reads: 16,
            ciphertext_additions: 7,
            ciphertext_subtractions: 8,
            ciphertext_multiplications: 8,
            relinearizations: 8,
            maximum_multiplicative_depth: 1,
            ..BfvCostManifest::default()
        }
    );

    let environments: Vec<Vec<u64>> = vec![
        vec![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
        vec![0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
        vec![1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0],
        vec![0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
    ];

    let encryption_started = Instant::now();
    let mut rng = rand_09::rng();
    let mut encrypted_inputs = Vec::new();
    for input_index in 0..16 {
        let slots = environments
            .iter()
            .map(|environment| environment[input_index])
            .collect::<Vec<_>>();
        let plaintext =
            Plaintext::try_encode(&slots, Encoding::simd(), params.arc()).expect("SIMD encode");
        let ciphertext = collective
            .pk
            .try_encrypt(&plaintext, &mut rng)
            .expect("collective encryption");
        encrypted_inputs.push(DeclaredEncryptedNat::from_declared_bound(ciphertext, 1));
    }
    let encryption_elapsed = encryption_started.elapsed();

    let commitment = opening_commitment(&environments);
    let statement = residual_statement_digest(&compiled, &encrypted_inputs, commitment);
    // The integration fixture owns the clear opening and encryption call, so
    // this deterministic digest is a transparent-construction receipt.  It is
    // not a ZK same-opening proof and the production manifest says so.
    let verifier_receipt_digest: [u8; 32] = Sha256::digest(
        [
            b"dregg/test/transparent-constructor-receipt/v1".as_slice(),
            commitment.as_slice(),
            statement.as_slice(),
        ]
        .concat(),
    )
    .into();
    let same_opening = SameOpeningReceipt::from_external_verifier(
        statement,
        commitment,
        verifier_receipt_digest,
        "test-only transparent constructor; no zero-knowledge verifier",
    )
    .expect("well-framed same-opening seam");
    let bounded_zero_engine =
        BoundedEncryptedZeroEngine::new(&relin, params.arc().clone()).expect("bounded zero engine");
    let bounded_zero_plan = bounded_zero_engine
        .compile(
            &compiled,
            &encrypted_inputs,
            same_opening.clone(),
            LIVE_SLOTS,
        )
        .expect("exact bounded encrypted zero-test plan");
    assert_eq!(
        bounded_zero_plan
            .manifest()
            .zero_conversion_cost
            .ciphertext_multiplications,
        7
    );
    assert_eq!(
        bounded_zero_plan
            .manifest()
            .zero_conversion_cost
            .output_multiplicative_depth,
        4
    );
    assert_eq!(
        compiled.cost().ciphertext_multiplications
            + bounded_zero_plan
                .manifest()
                .zero_conversion_cost
                .ciphertext_multiplications,
        15,
        "including the exact encrypted zero conversion erases the apparent 8-vs-15 multiplication win"
    );
    let bounded_zero_execution = bounded_zero_engine
        .execute(&engine, &compiled, &encrypted_inputs, &bounded_zero_plan)
        .expect("real bounded encrypted zero conversion");
    let bounded_bit_observation = execute_threshold_scaled_bit_observation(
        &bounded_zero_execution.output,
        bounded_zero_execution.manifest.true_scale,
        &parties,
        &params,
        LIVE_SLOTS,
    );
    let bounded_observation_status = match bounded_bit_observation {
        Ok(observation) => {
            assert_eq!(observation.opened_bits, vec![true, false, true, false]);
            "accepted with the exact two-valued output on this run"
        }
        Err(ZeroObservationError::OpenedBitNonCanonical { .. }) => {
            "REFUSED: threshold combine produced a value outside {0,B!} under an unproved multiplied-ciphertext noise envelope"
        }
        Err(error) => panic!("unexpected scaled-bit observation failure: {error}"),
    };

    let observation_plan = compile_threshold_zero_observation(
        &engine,
        &compiled,
        &encrypted_inputs,
        same_opening,
        PARTIES,
        LIVE_SLOTS,
        false,
    )
    .expect("final threshold observation plan");
    assert_eq!(
        observation_plan
            .manifest()
            .boundary_cost
            .decryption_share_messages,
        PARTIES
    );
    assert_eq!(
        observation_plan.manifest().boundary_cost.threshold_combines,
        1
    );
    assert_eq!(
        observation_plan
            .manifest()
            .boundary_cost
            .clear_zero_comparisons,
        LIVE_SLOTS
    );
    assert_eq!(
        observation_plan
            .manifest()
            .boundary_cost
            .ciphertext_reencryptions,
        0
    );

    let receipt = execute_final_threshold_zero_observation(
        &engine,
        &compiled,
        &encrypted_inputs,
        &observation_plan,
        &parties,
        &params,
    )
    .expect("real residual threshold opening");
    assert_eq!(receipt.opened_residuals, vec![0, 1, 0, 2]);
    assert_eq!(receipt.truth_bits, vec![true, false, true, false]);
    assert!(receipt.decryption_share_wire_bytes > 0);
    assert!(receipt.coverage.encrypted_evaluation_measured);
    assert!(receipt.coverage.every_zero_observation_measured);
    assert!(receipt.coverage.output_observation_measured);
    assert!(!receipt.coverage.key_setup_measured);
    assert!(!receipt.coverage.input_encryption_measured);
    assert!(!receipt.coverage.same_opening_verification_measured);
    assert!(
        !receipt.end_to_end_comparable(),
        "online residual+opening measurement must not be relabelled end-to-end"
    );

    println!(
        "BFV_THRESHOLD_ZERO_OBSERVATION_MEASUREMENT {}",
        serde_json::json!({
            "manifest": receipt.manifest,
            "opened_residuals": receipt.opened_residuals,
            "truth_bits": receipt.truth_bits,
            "setup_elapsed_ns": setup_elapsed.as_nanos(),
            "input_encryption_elapsed_ns": encryption_elapsed.as_nanos(),
            "bounded_encrypted_zero": {
                "manifest": bounded_zero_execution.manifest,
                "residual_evaluation_elapsed_ns": bounded_zero_execution.residual_evaluation_elapsed.as_nanos(),
                "zero_conversion_elapsed_ns": bounded_zero_execution.zero_conversion_elapsed.as_nanos(),
                "final_bit_observation": bounded_observation_status,
                "total_ciphertext_multiplications_including_zero_conversion": 15,
                "comparison": "the balanced Boolean baseline for the same eight equality conjunction also uses 15 ciphertext multiplications at depth four"
            },
            "encrypted_evaluation_elapsed_ns": receipt.encrypted_evaluation_elapsed_ns,
            "threshold_observation_elapsed_ns": receipt.threshold_observation_elapsed_ns,
            "decryption_share_wire_bytes": receipt.decryption_share_wire_bytes,
            "coverage": receipt.coverage,
            "end_to_end_comparable": receipt.end_to_end_comparable(),
            "noise_observation": "no joint secret key exists; multiplied-ciphertext noise was not measured and the fold-noise theorem does not cover this computation",
            "claim_scope": "one successful online residual evaluation plus n-of-n threshold opening; exact costs/leakage, no general latency/noise/security theorem"
        })
    );
}

#[test]
fn two_point_bounded_encrypted_scaled_zero_is_exact_under_single_key_oracle() {
    const LIVE_SLOTS: usize = 4;
    let params: std::sync::Arc<BfvParameters> = pick_params(20);
    let mut rng = rand_09::rng();
    let secret = SecretKey::random(&params, &mut rng);
    let public = PublicKey::new(&secret, &mut rng);
    let relin = RelinearizationKey::new(&secret, &mut rng).expect("relinearization key");
    let logic_engine = BfvLogicEngine::new(&relin, params.clone()).expect("logic engine");
    let zero_engine =
        BoundedEncryptedZeroEngine::new(&relin, params.clone()).expect("bounded zero engine");
    let compiled = logic_engine
        .compile_residual_equalities(ResidualEqualityPlan {
            pairs: (0..2).map(|pair| (2 * pair, 2 * pair + 1)).collect(),
            input_bound: 1,
        })
        .expect("bounded residual");
    let environments: Vec<Vec<u64>> = vec![
        vec![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
        vec![0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
        vec![1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0],
        vec![0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
    ];
    let mut inputs = Vec::new();
    for input_index in 0..4 {
        let slots = environments
            .iter()
            .map(|environment| environment[input_index])
            .collect::<Vec<_>>();
        let plaintext =
            Plaintext::try_encode(&slots, Encoding::simd(), &params).expect("encode input");
        inputs.push(DeclaredEncryptedNat::from_declared_bound(
            public
                .try_encrypt(&plaintext, &mut rng)
                .expect("encrypt input"),
            1,
        ));
    }
    let commitment = opening_commitment(&environments);
    let statement = residual_statement_digest(&compiled, &inputs, commitment);
    let same_opening = SameOpeningReceipt::from_external_verifier(
        statement,
        commitment,
        [0x55; 32],
        "test-only transparent constructor; no zero-knowledge verifier",
    )
    .expect("receipt");
    let plan = zero_engine
        .compile(&compiled, &inputs, same_opening, LIVE_SLOTS)
        .expect("bounded zero plan");
    assert_eq!(
        plan.manifest()
            .zero_conversion_cost
            .ciphertext_multiplications,
        1
    );
    assert_eq!(
        plan.manifest()
            .zero_conversion_cost
            .output_multiplicative_depth,
        2
    );
    let execution = zero_engine
        .execute(&logic_engine, &compiled, &inputs, &plan)
        .expect("bounded zero execution");
    let plaintext = secret
        .try_decrypt(&execution.output)
        .expect("single-key oracle decrypt");
    let slots = Vec::<u64>::try_decode(&plaintext, Encoding::simd()).expect("decode output");
    assert_eq!(execution.manifest.true_scale, 2);
    assert_eq!(&slots[..LIVE_SLOTS], &[2, 0, 2, 0]);
    let noise_bits = unsafe { secret.measure_noise(&execution.output) }
        .expect("single-key output noise measurement");
    println!(
        "BFV_BOUNDED_ENCRYPTED_ZERO_MEASUREMENT {}",
        serde_json::json!({
            "manifest": execution.manifest,
            "opened_by_single_key_oracle": &slots[..LIVE_SLOTS],
            "residual_evaluation_elapsed_ns": execution.residual_evaluation_elapsed.as_nanos(),
            "zero_conversion_elapsed_ns": execution.zero_conversion_elapsed.as_nanos(),
            "observed_output_noise_bits": noise_bits,
            "claim_scope": "two-point bounded scaled conversion exact on this single-key run; no no-viewer threshold-margin theorem and no general BFV noise theorem"
        })
    );
}

#[test]
fn statement_tamper_and_unimplemented_internal_continuation_fail_closed() {
    const PARTIES: usize = 2;
    let params = BfvParams::fold_set();
    let (keygen, collective, parties) = collective_keygen(PARTIES, &params);
    let relin_session = RelinKeySession::from_public_entropy(
        &keygen,
        &collective,
        [0x82; 32],
        Duration::from_secs(90),
    )
    .expect("relinearization session");
    let relin = generate_relinearization_key(&relin_session, &params, &collective, &parties)
        .expect("party-owned relinearization key");
    let engine = BfvLogicEngine::new(&relin, params.arc().clone()).expect("logic engine");
    let compiled = engine
        .compile_residual_equalities(ResidualEqualityPlan {
            pairs: vec![(0, 1)],
            input_bound: 1,
        })
        .expect("one equality");
    let mut rng = rand_09::rng();
    let mut encrypted_inputs = Vec::new();
    for value in [0u64, 0] {
        let plaintext =
            Plaintext::try_encode(&[value], Encoding::simd(), params.arc()).expect("encode input");
        encrypted_inputs.push(DeclaredEncryptedNat::from_declared_bound(
            collective
                .pk
                .try_encrypt(&plaintext, &mut rng)
                .expect("encrypt input"),
            1,
        ));
    }
    let commitment = [0x33; 32];
    let statement = residual_statement_digest(&compiled, &encrypted_inputs, commitment);
    let receipt =
        SameOpeningReceipt::from_external_verifier(statement, commitment, [0x44; 32], "test seam")
            .expect("receipt");
    let internal_plan = compile_threshold_zero_observation(
        &engine,
        &compiled,
        &encrypted_inputs,
        receipt,
        PARTIES,
        1,
        true,
    )
    .expect("priced internal boundary");
    assert_eq!(
        internal_plan
            .manifest()
            .boundary_cost
            .ciphertext_reencryptions,
        1
    );
    assert!(matches!(
        execute_final_threshold_zero_observation(
            &engine,
            &compiled,
            &encrypted_inputs,
            &internal_plan,
            &parties,
            &params,
        ),
        Err(ZeroObservationError::HybridContinuationNotImplemented)
    ));

    let replacement_plaintext =
        Plaintext::try_encode(&[1u64], Encoding::simd(), params.arc()).expect("encode replacement");
    encrypted_inputs[0] = DeclaredEncryptedNat::from_declared_bound(
        collective
            .pk
            .try_encrypt(&replacement_plaintext, &mut rng)
            .expect("encrypt replacement"),
        1,
    );
    assert!(matches!(
        execute_final_threshold_zero_observation(
            &engine,
            &compiled,
            &encrypted_inputs,
            &internal_plan,
            &parties,
            &params,
        ),
        Err(ZeroObservationError::HybridContinuationNotImplemented)
    ));

    // A final-boundary plan reaches the statement check and rejects the exact
    // ciphertext substitution before any encrypted computation executes.
    let mut final_manifest = internal_plan.manifest().same_opening.clone();
    final_manifest.verifier_id = "tamper check".to_owned();
    let final_plan = compile_threshold_zero_observation(
        &engine,
        &compiled,
        // Rebuild against the original statement is impossible after the
        // ciphertext replacement; the stale receipt must fail here.
        &encrypted_inputs,
        final_manifest,
        PARTIES,
        1,
        false,
    );
    assert!(matches!(
        final_plan,
        Err(ZeroObservationError::SameOpeningStatementMismatch)
    ));
}
