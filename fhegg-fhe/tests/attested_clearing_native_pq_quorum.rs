//! Hostile teeth for the enrolled Ed25519 + ML-DSA clearing quorum.
//!
//! `dregg-pq` deliberately aborts when a process reaches its unaudited Rust
//! fallback without an explicit opt-in.  This test therefore re-executes only
//! itself in a marked child with that test-only opt-in; normal fhEgg test
//! processes retain the production fail-closed default.

use std::process::Command;
use std::time::Duration;

use dregg_pq::MlDsaKey;
use ed25519_dalek::{Signer, SigningKey};
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, BfvPublicIdentity,
    ClassicalCompatibilityQuorumVerifier, ComputationIntegrityEvidence,
    ComputationIntegrityResidual, ComputationIntegrityVerifier, ExpectedClearingContext,
    InMemoryReplayGuard, InputDigest, NativePqAuthenticatedQuorumVerifier,
    NativePqPartyClaimSignature, NativePqPartyPublicKey, QuorumVerifierError,
    NATIVE_PQ_CLEARING_ML_DSA_CONTEXT,
};
use fhegg_fhe::mpc::Crossing;
use fhegg_fhe::mpc_party::{simulate_public_transcript, DistributedTranscript, PartyMpcSession};
use rand::rngs::StdRng;
use rand::SeedableRng;

const CHILD_MARKER: &str = "FHEGG_NATIVE_PQ_QUORUM_TEST_CHILD";
const TEST_NAME: &str = "native_pq_quorum_requires_paired_enrolled_signatures";

fn mpc_session() -> PartyMpcSession {
    PartyMpcSession::new([0xc1; 32], 3, 5, 8, 257, Duration::from_secs(1))
        .expect("valid public session")
}

fn bfv() -> BfvPublicIdentity {
    BfvPublicIdentity {
        n_parties: 3,
        opening_threshold: 3,
        degree: 4096,
        moduli_digest: [0xc2; 32],
        plaintext_modulus: 257,
        crp_seed: [0xc3; 32],
        collective_public_key_digest: [0xc4; 32],
    }
}

fn inputs() -> Vec<InputDigest> {
    vec![
        InputDigest::ciphertext_bytes(b"native-pq-demand-ciphertext"),
        InputDigest::ciphertext_bytes(b"native-pq-supply-ciphertext"),
        InputDigest::commitment([0xc5; 32]),
    ]
}

fn transcript(session: &PartyMpcSession, crossing: &Crossing) -> DistributedTranscript {
    let mut rng = StdRng::seed_from_u64(0xc6c6_c6c6);
    simulate_public_transcript(crossing, session, &mut rng).expect("strict public transcript")
}

fn signing_material() -> (Vec<SigningKey>, Vec<MlDsaKey>) {
    let seeds = [[0xd1; 32], [0xd2; 32], [0xd3; 32]];
    (
        seeds.iter().map(SigningKey::from_bytes).collect(),
        seeds.iter().map(MlDsaKey::from_ed25519_seed).collect(),
    )
}

fn public_roster(ed25519: &[SigningKey], ml_dsa: &[MlDsaKey]) -> Vec<NativePqPartyPublicKey> {
    ed25519
        .iter()
        .zip(ml_dsa)
        .map(|(ed25519, ml_dsa)| {
            NativePqPartyPublicKey::new(ed25519.verifying_key().to_bytes(), ml_dsa.public_bytes())
        })
        .collect()
}

fn run_hostile_matrix() {
    let (ed25519, ml_dsa) = signing_material();
    let enrolled = public_roster(&ed25519, &ml_dsa);
    let verifier = NativePqAuthenticatedQuorumVerifier::new(enrolled.clone(), 2)
        .expect("valid enrolled native-PQ roster");

    assert_eq!(
        NativePqAuthenticatedQuorumVerifier::new(Vec::new(), 1).unwrap_err(),
        QuorumVerifierError::EmptyRoster
    );
    assert_eq!(
        NativePqAuthenticatedQuorumVerifier::new(enrolled.clone(), 0).unwrap_err(),
        QuorumVerifierError::InvalidThreshold {
            threshold: 0,
            roster_len: 3,
        }
    );
    let mut malformed = enrolled.clone();
    malformed[1] = NativePqPartyPublicKey::new(*malformed[1].ed25519(), vec![7; 31]);
    assert_eq!(
        NativePqAuthenticatedQuorumVerifier::new(malformed, 2).unwrap_err(),
        QuorumVerifierError::InvalidPostQuantumPublicKey {
            index: 1,
            actual_len: 31,
        }
    );
    let mut duplicate_pq = enrolled.clone();
    duplicate_pq[1] = NativePqPartyPublicKey::new(
        *duplicate_pq[1].ed25519(),
        duplicate_pq[0].ml_dsa().to_vec(),
    );
    assert_eq!(
        NativePqAuthenticatedQuorumVerifier::new(duplicate_pq, 2).unwrap_err(),
        QuorumVerifierError::DuplicatePostQuantumPublicKey { index: 1 }
    );

    let session = mpc_session();
    let bfv = bfv();
    let inputs = inputs();
    let crossing = Crossing {
        p_star: Some(3),
        v_star: 11,
    };
    let transcript = transcript(&session, &crossing);
    let expected = ExpectedClearingContext {
        session: &session,
        ordered_roster: verifier.ordered_roster(),
        bfv: &bfv,
        ordered_inputs: &inputs,
        transcript: &transcript,
        crossing: &crossing,
    };
    let mut receipt = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical hybrid-roster claim");
    let claim_digest = receipt.claim_digest();
    let authority_message = verifier.signing_message(&receipt.claim);
    assert_eq!(
        authority_message.len(),
        64,
        "native-PQ authority is a full-width SHA-512 transcript"
    );

    let sig0 = verifier
        .sign_claim(&receipt.claim, 0, &ed25519[0], &ml_dsa[0])
        .expect("slot zero signs with both enrolled keys");
    let sig2 = verifier
        .sign_claim(&receipt.claim, 2, &ed25519[2], &ml_dsa[2])
        .expect("slot two signs with both enrolled keys");

    assert_eq!(
        verifier.assemble_evidence(&receipt.claim, std::slice::from_ref(&sig0)),
        Err(QuorumVerifierError::InsufficientSignatures { have: 1, need: 2 })
    );
    assert_eq!(
        verifier.assemble_evidence(&receipt.claim, &[sig0.clone(), sig0.clone()]),
        Err(QuorumVerifierError::DuplicateSigner { index: 0 })
    );
    assert_eq!(
        verifier.assemble_evidence(&receipt.claim, &[sig2.clone(), sig0.clone()]),
        Err(QuorumVerifierError::NonCanonicalSignerOrder)
    );

    let attacker_ed25519 = SigningKey::from_bytes(&[0xee; 32]);
    let attacker_ml_dsa = MlDsaKey::from_ed25519_seed(&[0xef; 32]);
    assert_eq!(
        verifier.sign_claim(&receipt.claim, 0, &attacker_ed25519, &ml_dsa[0]),
        Err(QuorumVerifierError::SignerKeyMismatch { index: 0 })
    );
    assert_eq!(
        verifier.sign_claim(&receipt.claim, 0, &ed25519[0], &attacker_ml_dsa),
        Err(QuorumVerifierError::PostQuantumSignerKeyMismatch { index: 0 })
    );

    // Two valid classical signatures are still sub-threshold in native-PQ
    // terms when one PQ half comes from an attacker-controlled, non-enrolled key.
    let message = verifier.signing_message(&receipt.claim);
    let independently_valid_but_unenrolled = NativePqPartyClaimSignature {
        signer_index: 0,
        ed25519_signature: ed25519[0].sign(&message).to_bytes(),
        ml_dsa_signature: attacker_ml_dsa.sign(NATIVE_PQ_CLEARING_ML_DSA_CONTEXT, &message),
    };
    assert_eq!(
        verifier.assemble_evidence(
            &receipt.claim,
            &[independently_valid_but_unenrolled, sig2.clone()],
        ),
        Err(QuorumVerifierError::InvalidPostQuantumSignature { index: 0 })
    );

    let evidence = verifier
        .assemble_evidence(&receipt.claim, &[sig0, sig2])
        .expect("2-of-3 paired evidence");
    let evidence_bytes = match &evidence {
        ComputationIntegrityEvidence::External { evidence, .. } => evidence.clone(),
        ComputationIntegrityEvidence::BindingOnly(_) => unreachable!("paired evidence is external"),
    };
    assert!(verifier.verify_claim(&receipt.claim, &evidence_bytes));
    assert!(
        !verifier.verify(&claim_digest, &evidence_bytes),
        "native-PQ verification refuses the legacy digest-only trait path"
    );
    let mut different_claim = receipt.claim.clone();
    different_claim.outcome.v_star ^= 1;
    assert!(!verifier.verify_claim(&different_claim, &evidence_bytes));
    assert_ne!(
        verifier.signing_message(&receipt.claim),
        verifier.signing_message(&different_claim),
        "a canonical claim mutation changes the full-width authority transcript"
    );

    // The evidence parser refuses a missing PQ half, a forged length, or any
    // byte corruption instead of treating the Ed25519 half as sufficient.
    assert!(!verifier.verify_claim(&receipt.claim, &evidence_bytes[..evidence_bytes.len() - 1]));
    let mut forged_pq_len = evidence_bytes.clone();
    const HEADER_LEN: usize = 1 + 32 + 4 + 4;
    const PQ_LEN_OFFSET_IN_RECORD: usize = 4 + 64;
    forged_pq_len[HEADER_LEN + PQ_LEN_OFFSET_IN_RECORD..HEADER_LEN + PQ_LEN_OFFSET_IN_RECORD + 8]
        .copy_from_slice(&1u64.to_be_bytes());
    assert!(!verifier.verify_claim(&receipt.claim, &forged_pq_len));
    let mut corrupted_pq = evidence_bytes.clone();
    corrupted_pq[HEADER_LEN + PQ_LEN_OFFSET_IN_RECORD + 8] ^= 1;
    assert!(!verifier.verify_claim(&receipt.claim, &corrupted_pq));

    receipt.computation_integrity = evidence;
    let mut replay = InMemoryReplayGuard::default();
    receipt
        .verify_full(&expected, &verifier, &mut replay)
        .expect("exact paired quorum accepts once");
    assert_eq!(
        receipt.verify_full(&expected, &verifier, &mut replay),
        Err(AttestationError::ReplayDetected)
    );

    // A verifier that substitutes only the PQ key for slot zero is a different
    // enrolled policy and cannot validate the original receipt or claim roster.
    let mut substituted_roster = enrolled.clone();
    substituted_roster[0] = NativePqPartyPublicKey::new(
        *substituted_roster[0].ed25519(),
        attacker_ml_dsa.public_bytes(),
    );
    let substituted = NativePqAuthenticatedQuorumVerifier::new(substituted_roster, 2)
        .expect("well-formed but hostile alternate policy");
    assert_eq!(
        receipt.verify_full(&expected, &substituted, &mut InMemoryReplayGuard::default(),),
        Err(AttestationError::IntegrityVerifierMismatch)
    );

    // The old Ed25519-only envelope remains explicitly available for interop,
    // but its verifier id and roster identities cannot be confused with native-PQ.
    let classical = ClassicalCompatibilityQuorumVerifier::new_classical_compatibility(
        ed25519
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .expect("explicit classical compatibility profile");
    assert_eq!(
        receipt.verify_full(&expected, &classical, &mut InMemoryReplayGuard::default(),),
        Err(AttestationError::IntegrityVerifierMismatch)
    );
}

#[test]
fn native_pq_quorum_requires_paired_enrolled_signatures() {
    if std::env::var_os(CHILD_MARKER).is_some() {
        run_hostile_matrix();
        return;
    }

    let status = Command::new(std::env::current_exe().expect("current test binary"))
        .args(["--exact", TEST_NAME, "--nocapture"])
        .env(CHILD_MARKER, "1")
        .env("DREGG_ALLOW_UNAUDITED_PQ", "1")
        .status()
        .expect("spawn isolated PQ fallback test child");
    assert!(status.success(), "native-PQ hostile matrix child failed");
}
