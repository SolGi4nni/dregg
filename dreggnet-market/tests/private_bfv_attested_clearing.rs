//! Heavy hostile gate for the complete private Dark Bazaar integrity adapter.
//!
//! The fixed n=4096 Bulletproof belongs in nextest's release-only heavy set.

#![cfg(feature = "private-attested-clearing")]

use std::time::Duration;

use dregg_circuit_prove::dark_bazaar_private::{
    self, PrivateBookWitness, PrivateOrder, PublicStatement,
};
use dreggnet_market::private_attested_clearing::{
    PrivateAttestedClearingPolicy, private_order_root_commitment,
};
use dreggnet_market::private_bfv_attested_clearing::{
    PrivateBfvAttestedClearingVerifier, PrivateBfvAttestedEvidenceError,
    PrivateBfvAttestedVerifierConfigError, PrivateBfvAuthorityError, PrivateBfvQuorumSecurity,
};
use ed25519_dalek::SigningKey;
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
    ClearingClaim, ComputationIntegrityEvidence, ComputationIntegrityResidual,
    ComputationIntegrityVerifier, ExpectedClearingContext, InMemoryReplayGuard, InputDigest,
    PartyClaimSignature,
};
use fhegg_fhe::bfv_lean::FOLD_MODULI;
use fhegg_fhe::mpc::Crossing;
use fhegg_fhe::mpc_party::{DistributedTranscript, PartyMpcSession, simulate_public_transcript};
use fhegg_fhe::private_book_bfv_zk::{PrivateBookBfvZkProof, prove_private_book_bfv_zk};
use fhegg_fhe::private_book_relation::{
    PrivateBookCiphertexts, PrivateBookEncryptionOpening, encrypt_private_book,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};
use rand::{SeedableRng, rngs::StdRng};

fn signing_keys() -> Vec<SigningKey> {
    [[0x31; 32], [0x32; 32], [0x33; 32]]
        .into_iter()
        .map(|seed| SigningKey::from_bytes(&seed))
        .collect()
}

fn quorum(keys: &[SigningKey]) -> AuthenticatedQuorumVerifier {
    AuthenticatedQuorumVerifier::new(
        keys.iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .expect("strict 2-of-3 roster")
}

fn signatures(
    quorum: &AuthenticatedQuorumVerifier,
    keys: &[SigningKey],
    claim: &ClearingClaim,
) -> [PartyClaimSignature; 2] {
    [
        quorum
            .sign_claim(&claim.digest(), 0, &keys[0])
            .expect("signer zero"),
        quorum
            .sign_claim(&claim.digest(), 2, &keys[2])
            .expect("signer two"),
    ]
}

fn collective_keygen(
    session: &KeygenSession,
    params: &BfvParams,
) -> (Vec<ThresholdParty>, CollectivePublicKey) {
    let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
    let mut parties = Vec::with_capacity(session.n_parties());
    for party in 0..session.n_parties() {
        let (state, contribution) =
            ThresholdParty::join(session, party, params).expect("party keygen");
        coordinator
            .accept(contribution)
            .expect("ordered contribution");
        parties.push(state);
    }
    (parties, coordinator.finish().expect("collective key"))
}

fn private_fixture() -> (PrivateBookWitness, PrivateBookEncryptionOpening) {
    let witness = PrivateBookWitness::try_from_orders_with_blinding(
        &[
            PrivateOrder::bid(10, 2),
            PrivateOrder::bid(6, 1),
            PrivateOrder::ask(5, 0),
            PrivateOrder::ask(8, 1),
        ],
        core::array::from_fn(|lane| 19_000 + lane as u32),
    )
    .expect("private book");
    let opening =
        PrivateBookEncryptionOpening::from_seeds([[0x51; 32], [0x52; 32], [0x53; 32], [0x54; 32]]);
    (witness, opening)
}

fn transcript(session: &PartyMpcSession, crossing: &Crossing) -> DistributedTranscript {
    simulate_public_transcript(crossing, session, &mut StdRng::seed_from_u64(0xDBA2_BF01))
        .expect("shape-correct reveal-only transcript")
}

fn external_bytes(evidence: &ComputationIntegrityEvidence) -> Vec<u8> {
    match evidence {
        ComputationIntegrityEvidence::External { evidence, .. } => evidence.clone(),
        ComputationIntegrityEvidence::BindingOnly(_) => panic!("expected external evidence"),
    }
}

/// One proof plus hostile verifier reconstructions is minutes-class even in
/// release. The whole target must remain outside nextest's default profile.
#[test]
fn receipt_requires_quorum_hidingfri_and_exact_bfv_root_proof() {
    let keys = signing_keys();
    let quorum = quorum(&keys);
    let params = BfvParams::fold_set();
    let key_session = KeygenSession::from_seed(3, [0x61; 32]).expect("key session");
    let (_parties, public_key) = collective_keygen(&key_session, &params);
    let bfv = BfvPublicIdentity::from_public(&params, &key_session, &public_key);
    let policy = PrivateAttestedClearingPolicy::new(16, bfv.clone()).expect("fixed policy");

    let (witness, opening) = private_fixture();
    let (clearing_proof, statement) =
        dark_bazaar_private::prove_zk(0xDBA2, &witness).expect("private clearing proof");
    assert_eq!((statement.p_star, statement.v_star), (1, 13));
    let ciphertexts =
        encrypt_private_book(&witness, &opening, &params, &public_key).expect("private BFV rows");
    let bfv_proof = prove_private_book_bfv_zk(
        statement,
        &witness,
        &ciphertexts,
        &opening,
        &params,
        &public_key,
    )
    .expect("transferable same-opening proof");
    let bfv_proof =
        PrivateBookBfvZkProof::from_bytes(&bfv_proof.to_bytes()).expect("canonical proof wire");

    // The private proof prefix is exact. A source-bound settlement may append
    // its separate message/ciphertext pairs and live-board commitment; those
    // suffix items remain covered by the exact quorum-signed claim.
    let mut ordered_inputs = ciphertexts
        .rows()
        .iter()
        .map(InputDigest::ciphertext)
        .collect::<Vec<_>>();
    ordered_inputs.push(InputDigest::commitment(private_order_root_commitment(
        statement.order_root,
    )));
    ordered_inputs.extend([
        InputDigest::commitment([0x71; 32]),
        InputDigest::ciphertext_bytes(b"separately-certified-live-source-row"),
        InputDigest::commitment([0x72; 32]),
    ]);

    let claim_nonce = [0x73; 32];
    let mpc_session = PartyMpcSession::new(
        claim_nonce,
        3,
        dark_bazaar_private::PRICE_COUNT,
        16,
        params.plaintext_modulus(),
        Duration::from_secs(1),
    )
    .expect("fixed-family fhEgg session");
    let crossing = Crossing {
        p_star: Some(statement.p_star as usize),
        v_star: statement.v_star as u64,
    };
    let public_transcript = transcript(&mpc_session, &crossing);
    let expected = ExpectedClearingContext {
        session: &mpc_session,
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
    let adapter = PrivateBfvAttestedClearingVerifier::new(
        quorum.clone(),
        policy.clone(),
        claim_nonce,
        statement,
        params.clone(),
        public_key.clone(),
        ciphertexts.clone(),
    )
    .expect("exact verifier context");
    receipt.computation_integrity = adapter
        .assemble_evidence(
            &receipt.claim,
            &signatures(&quorum, &keys, &receipt.claim),
            &clearing_proof,
            &bfv_proof,
        )
        .expect("all three components verify before assembly");

    let authority = adapter
        .verify_authority(&receipt, &expected)
        .expect("complete composite verifies and mints the exact private game authority");
    assert_eq!(authority.verifier_id(), adapter.verifier_id());
    assert_eq!(authority.claim_digest(), receipt.claim_digest());
    assert_eq!(authority.certificate_digest(), receipt.envelope_digest());
    assert_eq!(authority.claim_session_nonce(), claim_nonce);
    assert_eq!(authority.private_session(), statement.session);
    assert_eq!(authority.relation(), statement.rule);
    assert_eq!(authority.private_root(), statement.order_root);
    assert_eq!(
        authority.quorum_security(),
        PrivateBfvQuorumSecurity::ClassicalCompatibility
    );
    assert_eq!(authority.roster_len(), quorum.ordered_roster().len() as u64);
    assert_eq!(
        (authority.price(), authority.volume()),
        (statement.p_star, statement.v_star)
    );
    assert_ne!(authority.private_root_commitment(), [0; 32]);
    assert_ne!(authority.roster_commitment(), [0; 32]);
    assert_ne!(authority.authority_digest(), [0; 32]);
    assert!(authority.binding_verifies());

    let mut corrupted_certificate = receipt.clone();
    let ComputationIntegrityEvidence::External { evidence, .. } =
        &mut corrupted_certificate.computation_integrity
    else {
        unreachable!("fixture installed external composite evidence")
    };
    let last = evidence.last_mut().expect("nonempty composite evidence");
    *last ^= 1;
    assert_eq!(
        adapter.verify_authority(&corrupted_certificate, &expected),
        Err(PrivateBfvAuthorityError::InvalidCompositeEvidence)
    );

    let mut substituted_roster = expected.ordered_roster.to_vec();
    substituted_roster.swap(0, 1);
    let mut wrong_roster_receipt = receipt.clone();
    wrong_roster_receipt.claim.ordered_roster = substituted_roster.clone();
    let wrong_roster_expected = ExpectedClearingContext {
        session: expected.session,
        ordered_roster: &substituted_roster,
        bfv: expected.bfv,
        ordered_inputs: expected.ordered_inputs,
        transcript: expected.transcript,
        crossing: expected.crossing,
    };
    assert_eq!(
        adapter.verify_authority(&wrong_roster_receipt, &wrong_roster_expected),
        Err(PrivateBfvAuthorityError::InvalidCompositeEvidence)
    );

    let mut substituted_root_inputs = expected.ordered_inputs.to_vec();
    substituted_root_inputs[dark_bazaar_private::ORDER_COUNT].digest[0] ^= 1;
    let mut wrong_root_receipt = receipt.clone();
    wrong_root_receipt.claim.ordered_inputs = substituted_root_inputs.clone();
    let wrong_root_expected = ExpectedClearingContext {
        session: expected.session,
        ordered_roster: expected.ordered_roster,
        bfv: expected.bfv,
        ordered_inputs: &substituted_root_inputs,
        transcript: expected.transcript,
        crossing: expected.crossing,
    };
    assert_eq!(
        adapter.verify_authority(&wrong_root_receipt, &wrong_root_expected),
        Err(PrivateBfvAuthorityError::InvalidCompositeEvidence)
    );
    let composite_bytes = external_bytes(&receipt.computation_integrity);

    // Neither authenticated agreement nor a floating same-opening proof is a
    // valid encoding of the required three-component evidence body.
    let quorum_only = quorum
        .assemble_evidence(
            &receipt.claim_digest(),
            &signatures(&quorum, &keys, &receipt.claim),
        )
        .expect("valid quorum envelope");
    for incomplete in [
        external_bytes(&quorum_only),
        clearing_proof.to_postcard().expect("clearing proof wire"),
        bfv_proof.to_bytes(),
    ] {
        let mut missing_component = receipt.clone();
        missing_component.computation_integrity = ComputationIntegrityEvidence::External {
            verifier_id: adapter.verifier_id(),
            evidence: incomplete,
        };
        assert_eq!(
            missing_component.verify_full(&expected, &adapter, &mut InMemoryReplayGuard::default()),
            Err(AttestationError::InvalidComputationIntegrityEvidence)
        );
    }

    // A policy that merely copies the visible degree/plaintext modulus but
    // substitutes the parameter-set digest is refused at verifier install.
    let mut wrong_param_identity = bfv.clone();
    wrong_param_identity.moduli_digest[0] ^= 1;
    let wrong_param_policy = PrivateAttestedClearingPolicy::new(16, wrong_param_identity)
        .expect("shape-valid substituted parameter identity");
    assert!(matches!(
        PrivateBfvAttestedClearingVerifier::new(
            quorum.clone(),
            wrong_param_policy,
            claim_nonce,
            statement,
            params.clone(),
            public_key.clone(),
            ciphertexts.clone(),
        ),
        Err(PrivateBfvAttestedVerifierConfigError::BfvIdentityMismatch)
    ));

    let mut wrong_private_rule = statement;
    wrong_private_rule.rule += 1;
    assert!(matches!(
        PrivateBfvAttestedClearingVerifier::new(
            quorum.clone(),
            policy.clone(),
            claim_nonce,
            wrong_private_rule,
            params.clone(),
            public_key.clone(),
            ciphertexts.clone(),
        ),
        Err(PrivateBfvAttestedVerifierConfigError::InvalidStatement)
    ));

    // Even freshly re-signed claim mutations cannot substitute a proof row,
    // root, full claim session, rule, or public output.
    for mutation in 0..6 {
        let mut rebound = receipt.claim.clone();
        match mutation {
            0 => rebound.ordered_inputs[0] = rebound.ordered_inputs[1],
            1 => {
                rebound.ordered_inputs[dark_bazaar_private::ORDER_COUNT] =
                    InputDigest::commitment([0x81; 32])
            }
            2 => rebound.session_nonce[0] ^= 1,
            3 => rebound.rule.value_bits += 1,
            4 => rebound.outcome.v_star += 1,
            5 => rebound.outcome.p_star = Some(u64::from(statement.p_star) + 1),
            _ => unreachable!(),
        }
        assert!(matches!(
            adapter.assemble_evidence(
                &rebound,
                &signatures(&quorum, &keys, &rebound),
                &clearing_proof,
                &bfv_proof,
            ),
            Err(PrivateBfvAttestedEvidenceError::ClaimMismatch(_))
        ));
    }

    // Configure the verifier and freshly signed claim around a substituted BFV
    // key. Cheap public joins all agree, but the transferable proof itself was
    // made for the original key and must fail.
    let other_key_session = KeygenSession::from_seed(3, [0x62; 32]).expect("other key session");
    let (_other_parties, other_key) = collective_keygen(&other_key_session, &params);
    let other_bfv = BfvPublicIdentity::from_public(&params, &other_key_session, &other_key);
    let other_policy =
        PrivateAttestedClearingPolicy::new(16, other_bfv.clone()).expect("other policy");
    let other_adapter = PrivateBfvAttestedClearingVerifier::new(
        quorum.clone(),
        other_policy,
        claim_nonce,
        statement,
        params.clone(),
        other_key,
        ciphertexts.clone(),
    )
    .expect("shape-valid substituted-key verifier");
    let mut other_claim = receipt.claim.clone();
    other_claim.bfv = other_bfv;
    assert!(matches!(
        other_adapter.assemble_evidence(
            &other_claim,
            &signatures(&quorum, &keys, &other_claim),
            &clearing_proof,
            &bfv_proof,
        ),
        Err(PrivateBfvAttestedEvidenceError::BfvProof(_))
    ));

    // The same attack with one altered canonical row also reaches the proof
    // verifier (after the claim is made internally consistent) and is refused.
    let mut wrong_rows = ciphertexts.rows().clone();
    wrong_rows[0].polys[0].rows[0][0] = (wrong_rows[0].polys[0].rows[0][0] + 1) % FOLD_MODULI[0];
    let wrong_ciphertexts = PrivateBookCiphertexts::from_rows(wrong_rows);
    let wrong_row_adapter = PrivateBfvAttestedClearingVerifier::new(
        quorum.clone(),
        policy.clone(),
        claim_nonce,
        statement,
        params.clone(),
        public_key.clone(),
        wrong_ciphertexts.clone(),
    )
    .expect("shape-valid substituted-row verifier");
    let mut wrong_row_claim = receipt.claim.clone();
    wrong_row_claim.ordered_inputs[0] = InputDigest::ciphertext(&wrong_ciphertexts.rows()[0]);
    assert!(matches!(
        wrong_row_adapter.assemble_evidence(
            &wrong_row_claim,
            &signatures(&quorum, &keys, &wrong_row_claim),
            &clearing_proof,
            &bfv_proof,
        ),
        Err(PrivateBfvAttestedEvidenceError::BfvProof(_))
    ));

    // A complete evidence body is not portable to a verifier whose configured
    // private proof session/root/output differs, even if the outer claim stays
    // byte-identical.
    for mutation in 0..3 {
        let mut other_statement: PublicStatement = statement;
        match mutation {
            0 => other_statement.session += 1,
            1 => other_statement.order_root[0] ^= 1,
            2 => other_statement.v_star += 1,
            _ => unreachable!(),
        }
        let substituted = PrivateBfvAttestedClearingVerifier::new(
            quorum.clone(),
            policy.clone(),
            claim_nonce,
            other_statement,
            params.clone(),
            public_key.clone(),
            ciphertexts.clone(),
        )
        .expect("shape-valid substituted statement verifier");
        assert!(!substituted.verify_claim(&receipt.claim, &composite_bytes));
    }
}
