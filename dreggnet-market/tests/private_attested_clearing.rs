//! One exact fhEgg claim must pass both authentication and hidden-computation
//! verification. These teeth specifically prevent replacing the composite with
//! either a quorum-only assertion or a floating private proof.

#![cfg(feature = "private-attested-clearing")]

use std::time::Duration;

use dregg_circuit_prove::dark_bazaar_private::{self, PrivateBookWitness, PrivateOrder};
use dreggnet_market::private_attested_clearing::{
    PrivateAttestedClearingPolicy, PrivateAttestedClearingVerifier, PrivateAttestedEvidenceError,
    private_claim_session_felt, private_claim_session_nonce, private_order_root_commitment,
};
use ed25519_dalek::SigningKey;
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
    ComputationIntegrityEvidence, ComputationIntegrityResidual, ComputationIntegrityVerifier,
    ExpectedClearingContext, InMemoryReplayGuard, InputDigest,
};
use fhegg_fhe::mpc::Crossing;
use fhegg_fhe::mpc_party::{DistributedTranscript, PartyMpcSession, simulate_public_transcript};
use rand::{SeedableRng, rngs::StdRng};

fn keys() -> Vec<SigningKey> {
    [[0x31; 32], [0x32; 32], [0x33; 32]]
        .into_iter()
        .map(|seed| SigningKey::from_bytes(&seed))
        .collect()
}

fn bfv() -> BfvPublicIdentity {
    BfvPublicIdentity {
        n_parties: 3,
        opening_threshold: 2,
        degree: 4096,
        moduli_digest: [0x44; 32],
        plaintext_modulus: 65_537,
        crp_seed: [0x45; 32],
        collective_public_key_digest: [0x46; 32],
    }
}

fn transcript(session: &PartyMpcSession, crossing: &Crossing) -> DistributedTranscript {
    simulate_public_transcript(crossing, session, &mut StdRng::seed_from_u64(0xDBA2_0001))
        .expect("shape-correct reveal-only transcript")
}

#[test]
fn private_proof_and_quorum_are_one_claim_bound_replay_protected_receipt() {
    let signing_keys = keys();
    let quorum = AuthenticatedQuorumVerifier::new(
        signing_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .expect("strict 2-of-3 roster");
    let policy = PrivateAttestedClearingPolicy::new(16, 65_537).expect("exact fhEgg rule policy");
    let verifier = PrivateAttestedClearingVerifier::new(quorum.clone(), policy);

    let proof_session = 0xDBA2;
    let session_nonce =
        private_claim_session_nonce(proof_session).expect("canonical injective fixed-family nonce");
    let session = PartyMpcSession::new(
        session_nonce,
        3,
        dark_bazaar_private::PRICE_COUNT,
        16,
        65_537,
        Duration::from_secs(1),
    )
    .expect("fixed-family fhEgg session");
    let witness = PrivateBookWitness::try_from_orders_with_blinding(
        &[
            PrivateOrder::bid(10, 2),
            PrivateOrder::bid(6, 1),
            PrivateOrder::ask(5, 0),
            PrivateOrder::ask(8, 1),
        ],
        core::array::from_fn(|lane| 900 + lane as u32),
    )
    .expect("canonical private book");
    assert_eq!(
        private_claim_session_felt(session.nonce()),
        Some(proof_session)
    );
    let (proof, statement) =
        dark_bazaar_private::prove_zk(proof_session, &witness).expect("hidden private-book proof");
    assert_eq!((statement.p_star, statement.v_star), (1, 13));

    let ordered_inputs = vec![
        InputDigest::ciphertext_bytes(b"canonical-private-demand-row"),
        InputDigest::ciphertext_bytes(b"canonical-private-supply-row"),
        InputDigest::commitment(private_order_root_commitment(statement.order_root)),
    ];
    let crossing = Crossing {
        p_star: Some(statement.p_star as usize),
        v_star: statement.v_star as u64,
    };
    let public_transcript = transcript(&session, &crossing);
    let bfv = bfv();
    let expected = ExpectedClearingContext {
        session: &session,
        ordered_roster: quorum.ordered_roster(),
        bfv: &bfv,
        ordered_inputs: &ordered_inputs,
        transcript: &public_transcript,
        crossing: &crossing,
    };
    let mut receipt = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical claim");
    let signatures = [
        quorum
            .sign_claim(&receipt.claim_digest(), 0, &signing_keys[0])
            .expect("signer zero"),
        quorum
            .sign_claim(&receipt.claim_digest(), 2, &signing_keys[2])
            .expect("signer two"),
    ];
    receipt.computation_integrity = verifier
        .assemble_evidence(&receipt.claim, &signatures, &proof, statement)
        .expect("both components verify before assembly");

    let mut replay = InMemoryReplayGuard::default();
    receipt
        .verify_full(&expected, &verifier, &mut replay)
        .expect("authenticated private computation verifies once");
    assert_eq!(
        receipt.verify_full(&expected, &verifier, &mut replay),
        Err(AttestationError::ReplayDetected)
    );

    // A plain quorum envelope cannot masquerade as the composite even when its
    // outer verifier id is rewritten to the composite policy id.
    let quorum_only = quorum
        .assemble_evidence(&receipt.claim_digest(), &signatures)
        .expect("valid quorum evidence");
    let quorum_bytes = match quorum_only {
        ComputationIntegrityEvidence::External { evidence, .. } => evidence,
        ComputationIntegrityEvidence::BindingOnly(_) => unreachable!(),
    };
    let mut missing_private_proof = receipt.clone();
    missing_private_proof.computation_integrity = ComputationIntegrityEvidence::External {
        verifier_id: verifier.verifier_id(),
        evidence: quorum_bytes,
    };
    assert_eq!(
        missing_private_proof.verify_full(
            &expected,
            &verifier,
            &mut InMemoryReplayGuard::default()
        ),
        Err(AttestationError::InvalidComputationIntegrityEvidence)
    );

    // Wire corruption is refused before either expensive component can be
    // interpreted as a different canonical envelope.
    let mut corrupt = receipt.clone();
    match &mut corrupt.computation_integrity {
        ComputationIntegrityEvidence::External { evidence, .. } => evidence[12] ^= 1,
        ComputationIntegrityEvidence::BindingOnly(_) => unreachable!(),
    }
    assert_eq!(
        corrupt.verify_full(&expected, &verifier, &mut InMemoryReplayGuard::default()),
        Err(AttestationError::InvalidComputationIntegrityEvidence)
    );

    // Even a freshly re-signed claim cannot rebind the proof's session, result,
    // or independently pinned root.
    for mutation in 0..4 {
        let mut rebound = receipt.claim.clone();
        match mutation {
            0 => rebound.session_nonce[0] ^= 1,
            1 => rebound.outcome.v_star += 1,
            2 => {
                *rebound.ordered_inputs.last_mut().expect("root input") =
                    InputDigest::commitment([0xA5; 32]);
            }
            3 => rebound.rule.value_bits += 1,
            _ => unreachable!(),
        }
        let rebound_signatures = [
            quorum
                .sign_claim(&rebound.digest(), 0, &signing_keys[0])
                .expect("re-signed mutation zero"),
            quorum
                .sign_claim(&rebound.digest(), 2, &signing_keys[2])
                .expect("re-signed mutation two"),
        ];
        assert!(matches!(
            verifier.assemble_evidence(&rebound, &rebound_signatures, &proof, statement),
            Err(PrivateAttestedEvidenceError::ClaimMismatch(_))
        ));
    }
}
