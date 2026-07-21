//! Mutation/replay teeth for the canonical clearing attestation envelope.

use std::time::Duration;

use ed25519_dalek::SigningKey;
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, BfvPublicIdentity,
    ClassicalCompatibilityQuorumVerifier, ComputationIntegrityEvidence,
    ComputationIntegrityResidual, ComputationIntegrityVerifier, Digest32, ExpectedClearingContext,
    InMemoryReplayGuard, InputDigest, PartyIdentity, QuorumVerifierError,
};
use fhegg_fhe::mpc::Crossing;
use fhegg_fhe::mpc_party::{simulate_public_transcript, DistributedTranscript, PartyMpcSession};
use rand::rngs::StdRng;
use rand::SeedableRng;

const VERIFIER_ID: Digest32 = [0xa5; 32];
const EVIDENCE: &[u8] = b"test-integrity-evidence-bound-out-of-band";

struct ExactTestVerifier {
    claim: Digest32,
}

impl ComputationIntegrityVerifier for ExactTestVerifier {
    fn verifier_id(&self) -> Digest32 {
        VERIFIER_ID
    }

    fn verify(&self, claim_digest: &Digest32, evidence: &[u8]) -> bool {
        claim_digest == &self.claim && evidence == EVIDENCE
    }
}

fn mpc_session(nonce: u8) -> PartyMpcSession {
    PartyMpcSession::new([nonce; 32], 3, 5, 8, 257, Duration::from_secs(1))
        .expect("valid public session")
}

fn roster() -> Vec<PartyIdentity> {
    [b"alice".as_slice(), b"bob".as_slice(), b"carol".as_slice()]
        .into_iter()
        .map(PartyIdentity::from_public_identity_bytes)
        .collect()
}

fn bfv() -> BfvPublicIdentity {
    BfvPublicIdentity {
        n_parties: 3,
        opening_threshold: 3,
        degree: 4096,
        moduli_digest: [0x31; 32],
        plaintext_modulus: 257,
        crp_seed: [0x42; 32],
        collective_public_key_digest: [0x53; 32],
    }
}

fn inputs() -> Vec<InputDigest> {
    vec![
        InputDigest::ciphertext_bytes(b"canonical-demand-ciphertext"),
        InputDigest::ciphertext_bytes(b"canonical-supply-ciphertext"),
        InputDigest::commitment([0x64; 32]),
    ]
}

fn transcript(session: &PartyMpcSession, crossing: &Crossing) -> DistributedTranscript {
    let mut rng = StdRng::seed_from_u64(0xacc3_57ed);
    simulate_public_transcript(crossing, session, &mut rng).expect("strict public transcript")
}

fn context<'a>(
    session: &'a PartyMpcSession,
    roster: &'a [PartyIdentity],
    bfv: &'a BfvPublicIdentity,
    inputs: &'a [InputDigest],
    transcript: &'a DistributedTranscript,
    crossing: &'a Crossing,
) -> ExpectedClearingContext<'a> {
    ExpectedClearingContext {
        session,
        ordered_roster: roster,
        bfv,
        ordered_inputs: inputs,
        transcript,
        crossing,
    }
}

fn quorum_keys() -> Vec<SigningKey> {
    [[0x71; 32], [0x72; 32], [0x73; 32]]
        .into_iter()
        .map(|seed| SigningKey::from_bytes(&seed))
        .collect()
}

fn quorum_verifier(keys: &[SigningKey], threshold: usize) -> ClassicalCompatibilityQuorumVerifier {
    ClassicalCompatibilityQuorumVerifier::new_classical_compatibility(
        keys.iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        threshold,
    )
    .expect("valid strict Ed25519 quorum")
}

#[test]
fn authenticated_quorum_endorses_the_exact_claim_once() {
    let keys = quorum_keys();
    let verifier = quorum_verifier(&keys, 2);
    let session = mpc_session(0x41);
    let roster = verifier.ordered_roster().to_vec();
    let bfv = bfv();
    let inputs = inputs();
    let crossing = Crossing {
        p_star: Some(2),
        v_star: 7,
    };
    let transcript = transcript(&session, &crossing);
    let expected = context(&session, &roster, &bfv, &inputs, &transcript, &crossing);
    let mut receipt = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical claim issues");

    let claim_digest = receipt.claim_digest();
    let signatures = [
        verifier
            .sign_claim(&claim_digest, 0, &keys[0])
            .expect("party 0 endorses"),
        verifier
            .sign_claim(&claim_digest, 2, &keys[2])
            .expect("party 2 endorses"),
    ];
    receipt.computation_integrity = verifier
        .assemble_evidence(&claim_digest, &signatures)
        .expect("2-of-3 evidence is canonical and valid");

    let mut replay = InMemoryReplayGuard::default();
    receipt
        .verify_full(&expected, &verifier, &mut replay)
        .expect("authenticated 2-of-3 claim passes once");
    assert_eq!(
        receipt.verify_full(&expected, &verifier, &mut replay),
        Err(AttestationError::ReplayDetected)
    );

    let reordered = ClassicalCompatibilityQuorumVerifier::new_classical_compatibility(
        [keys[1].clone(), keys[0].clone(), keys[2].clone()]
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .expect("same keys in a different declared order form another policy");
    assert_eq!(
        receipt.verify_full(&expected, &reordered, &mut InMemoryReplayGuard::default()),
        Err(AttestationError::IntegrityVerifierMismatch),
        "a reordered public-key roster is a different verifier and must reject"
    );
}

#[test]
fn authenticated_quorum_rejects_missing_duplicate_unknown_reordered_and_forged_signers() {
    let keys = quorum_keys();
    let verifier = quorum_verifier(&keys, 2);
    let session = mpc_session(0x42);
    let roster = verifier.ordered_roster().to_vec();
    let bfv = bfv();
    let inputs = inputs();
    let crossing = Crossing {
        p_star: Some(2),
        v_star: 7,
    };
    let transcript = transcript(&session, &crossing);
    let expected = context(&session, &roster, &bfv, &inputs, &transcript, &crossing);
    let binding = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical claim");
    let digest = binding.claim_digest();
    let sig0 = verifier.sign_claim(&digest, 0, &keys[0]).expect("party 0");
    let sig1 = verifier.sign_claim(&digest, 1, &keys[1]).expect("party 1");

    assert_eq!(
        verifier.assemble_evidence(&digest, std::slice::from_ref(&sig0)),
        Err(QuorumVerifierError::InsufficientSignatures { have: 1, need: 2 })
    );
    assert_eq!(
        verifier.assemble_evidence(&digest, &[sig0.clone(), sig0.clone()]),
        Err(QuorumVerifierError::DuplicateSigner { index: 0 })
    );
    assert_eq!(
        verifier.assemble_evidence(&digest, &[sig1.clone(), sig0.clone()]),
        Err(QuorumVerifierError::NonCanonicalSignerOrder)
    );
    assert_eq!(
        verifier.sign_claim(&digest, 1, &keys[0]),
        Err(QuorumVerifierError::SignerKeyMismatch { index: 1 })
    );

    let mut receipt = binding;
    receipt.computation_integrity = verifier
        .assemble_evidence(&digest, &[sig0, sig1])
        .expect("honest evidence");
    let ComputationIntegrityEvidence::External { evidence, .. } = &receipt.computation_integrity
    else {
        panic!("quorum assembly returns external evidence")
    };

    // Wire header is version(1) + roster digest(32) + threshold(4) + count(4),
    // then fixed 68-byte signer-index/signature records.
    const HEADER: usize = 41;
    const RECORD: usize = 68;
    let refuses = |mut bad_evidence: Vec<u8>| {
        let mut bad = receipt.clone();
        if let ComputationIntegrityEvidence::External { evidence, .. } =
            &mut bad.computation_integrity
        {
            std::mem::swap(evidence, &mut bad_evidence);
        }
        assert_eq!(
            bad.verify_full(&expected, &verifier, &mut InMemoryReplayGuard::default()),
            Err(AttestationError::InvalidComputationIntegrityEvidence)
        );
    };

    let mut unknown = evidence.clone();
    unknown[HEADER..HEADER + 4].copy_from_slice(&9u32.to_be_bytes());
    refuses(unknown);

    let mut duplicate = evidence.clone();
    duplicate[HEADER + RECORD..HEADER + RECORD + 4].copy_from_slice(&0u32.to_be_bytes());
    refuses(duplicate);

    let mut reordered = evidence.clone();
    let (left, right) = reordered[HEADER..HEADER + 2 * RECORD].split_at_mut(RECORD);
    left.swap_with_slice(right);
    refuses(reordered);

    let mut forged = evidence.clone();
    forged[HEADER + 4] ^= 1;
    refuses(forged);

    let mut missing = evidence[..HEADER + RECORD].to_vec();
    missing[37..41].copy_from_slice(&1u32.to_be_bytes());
    refuses(missing);
}

#[test]
fn authenticated_quorum_configuration_fails_closed() {
    let keys = quorum_keys();
    let public: Vec<_> = keys
        .iter()
        .map(|key| key.verifying_key().to_bytes())
        .collect();
    assert_eq!(
        ClassicalCompatibilityQuorumVerifier::new_classical_compatibility(Vec::new(), 1)
            .unwrap_err(),
        QuorumVerifierError::EmptyRoster
    );
    assert_eq!(
        ClassicalCompatibilityQuorumVerifier::new_classical_compatibility(public.clone(), 0)
            .unwrap_err(),
        QuorumVerifierError::InvalidThreshold {
            threshold: 0,
            roster_len: 3,
        }
    );
    assert_eq!(
        ClassicalCompatibilityQuorumVerifier::new_classical_compatibility(public.clone(), 4)
            .unwrap_err(),
        QuorumVerifierError::InvalidThreshold {
            threshold: 4,
            roster_len: 3,
        }
    );
    assert_eq!(
        ClassicalCompatibilityQuorumVerifier::new_classical_compatibility(
            vec![public[0], public[0]],
            1,
        )
        .unwrap_err(),
        QuorumVerifierError::DuplicatePublicKey { index: 1 }
    );
    assert_eq!(
        ClassicalCompatibilityQuorumVerifier::new_classical_compatibility(
            vec![[
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0
            ]],
            1
        )
        .unwrap_err(),
        QuorumVerifierError::InvalidPublicKey { index: 0 },
        "a canonical small-order/weak key is not an authorized identity"
    );
}

#[test]
fn full_attestation_requires_independent_integrity_evidence_and_rejects_replay() {
    let session = mpc_session(0x11);
    let roster = roster();
    let bfv = bfv();
    let inputs = inputs();
    let crossing = Crossing {
        p_star: Some(2),
        v_star: 7,
    };
    let transcript = transcript(&session, &crossing);
    let expected = context(&session, &roster, &bfv, &inputs, &transcript, &crossing);

    let binding_only = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical binding issues");
    binding_only
        .verify_binding(&expected)
        .expect("binding-only receipt binds exactly");
    let verifier = ExactTestVerifier {
        claim: binding_only.claim_digest(),
    };
    assert_eq!(
        binding_only.verify_full(&expected, &verifier, &mut InMemoryReplayGuard::default()),
        Err(AttestationError::ComputationIntegrityResidual(
            ComputationIntegrityResidual::OutputOnlySelfAssertion
        ))
    );

    let mut full = binding_only;
    full.computation_integrity = ComputationIntegrityEvidence::External {
        verifier_id: VERIFIER_ID,
        evidence: EVIDENCE.to_vec(),
    };
    let mut replay = InMemoryReplayGuard::default();
    full.verify_full(&expected, &verifier, &mut replay)
        .expect("independently accepted evidence passes once");
    assert_eq!(
        full.verify_full(&expected, &verifier, &mut replay),
        Err(AttestationError::ReplayDetected)
    );

    let mut bad_evidence = full.clone();
    if let ComputationIntegrityEvidence::External { evidence, .. } =
        &mut bad_evidence.computation_integrity
    {
        evidence.push(0);
    }
    assert_eq!(
        bad_evidence.verify_full(&expected, &verifier, &mut InMemoryReplayGuard::default()),
        Err(AttestationError::InvalidComputationIntegrityEvidence)
    );
}

#[test]
fn receipt_and_expected_context_mutations_fail_closed() {
    let session = mpc_session(0x22);
    let roster = roster();
    let bfv = bfv();
    let inputs = inputs();
    let crossing = Crossing {
        p_star: Some(2),
        v_star: 7,
    };
    let transcript = transcript(&session, &crossing);
    let expected = context(&session, &roster, &bfv, &inputs, &transcript, &crossing);
    let receipt = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical receipt");

    let mut mutated = receipt.clone();
    mutated.claim.session_nonce[0] ^= 1;
    assert_eq!(
        mutated.verify_binding(&expected),
        Err(AttestationError::BindingMismatch)
    );

    let mut mutated = receipt.clone();
    mutated.claim.ordered_roster.swap(0, 1);
    assert_eq!(
        mutated.verify_binding(&expected),
        Err(AttestationError::BindingMismatch)
    );

    let mut mutated = receipt.clone();
    mutated.claim.bfv.collective_public_key_digest[0] ^= 1;
    assert_eq!(
        mutated.verify_binding(&expected),
        Err(AttestationError::BindingMismatch)
    );

    let mut mutated = receipt.clone();
    mutated.claim.ordered_inputs.swap(0, 1);
    assert_eq!(
        mutated.verify_binding(&expected),
        Err(AttestationError::BindingMismatch)
    );

    let mut mutated = receipt.clone();
    mutated.claim.rule.version += 1;
    assert_eq!(
        mutated.verify_binding(&expected),
        Err(AttestationError::BindingMismatch)
    );

    let mut mutated = receipt.clone();
    mutated.claim.transcript_digest[0] ^= 1;
    assert_eq!(
        mutated.verify_binding(&expected),
        Err(AttestationError::BindingMismatch)
    );

    let mut mutated = receipt.clone();
    mutated.claim.outcome.v_star += 1;
    assert_eq!(
        mutated.verify_binding(&expected),
        Err(AttestationError::BindingMismatch)
    );

    let mut reordered_roster = roster.clone();
    reordered_roster.swap(0, 1);
    assert_eq!(
        receipt.verify_binding(&context(
            &session,
            &reordered_roster,
            &bfv,
            &inputs,
            &transcript,
            &crossing
        )),
        Err(AttestationError::BindingMismatch)
    );

    let wrong_session = mpc_session(0x23);
    assert_eq!(
        receipt.verify_binding(&context(
            &wrong_session,
            &roster,
            &bfv,
            &inputs,
            &transcript,
            &crossing
        )),
        Err(AttestationError::BindingMismatch)
    );

    let mut wrong_inputs = inputs.clone();
    wrong_inputs[0] = InputDigest::ciphertext_bytes(b"wrong-demand-ciphertext");
    assert_eq!(
        receipt.verify_binding(&context(
            &session,
            &roster,
            &bfv,
            &wrong_inputs,
            &transcript,
            &crossing
        )),
        Err(AttestationError::BindingMismatch)
    );

    let mut different_valid_transcript = transcript.clone();
    different_valid_transcript.masked[0].d ^= 1;
    assert!(different_valid_transcript.is_reveal_only(&session));
    assert_eq!(
        receipt.verify_binding(&context(
            &session,
            &roster,
            &bfv,
            &inputs,
            &different_valid_transcript,
            &crossing
        )),
        Err(AttestationError::BindingMismatch)
    );

    let mut non_reveal_only = transcript.clone();
    non_reveal_only.revealed_vstar.push(0);
    assert_eq!(
        receipt.verify_binding(&context(
            &session,
            &roster,
            &bfv,
            &inputs,
            &non_reveal_only,
            &crossing
        )),
        Err(AttestationError::TranscriptNotRevealOnly)
    );

    let wrong_output = Crossing {
        p_star: Some(2),
        v_star: 6,
    };
    assert_eq!(
        receipt.verify_binding(&context(
            &session,
            &roster,
            &bfv,
            &inputs,
            &transcript,
            &wrong_output
        )),
        Err(AttestationError::TranscriptOutputMismatch)
    );
}

#[test]
fn malformed_contexts_are_refused_before_receipt_issuance() {
    let session = mpc_session(0x33);
    let mut duplicate_roster = roster();
    let bfv = bfv();
    let inputs = inputs();
    let crossing = Crossing {
        p_star: Some(2),
        v_star: 7,
    };
    let transcript = transcript(&session, &crossing);

    duplicate_roster[1] = duplicate_roster[0];
    assert_eq!(
        AttestedClearingReceipt::issue(
            &context(
                &session,
                &duplicate_roster,
                &bfv,
                &inputs,
                &transcript,
                &crossing,
            ),
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion
            )
        ),
        Err(AttestationError::InvalidRoster)
    );

    let mut wrong_bfv = bfv.clone();
    wrong_bfv.plaintext_modulus = 263;
    let good_roster = roster();
    assert_eq!(
        AttestedClearingReceipt::issue(
            &context(
                &session,
                &good_roster,
                &wrong_bfv,
                &inputs,
                &transcript,
                &crossing
            ),
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion
            )
        ),
        Err(AttestationError::BfvSessionMismatch)
    );
}
