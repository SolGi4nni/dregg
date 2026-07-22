//! Hostile gate for authority-certified PartyMPC preprocessing.
//!
//! The underlying authority remains a trusted Beaver dealer.  This gate proves
//! a narrower property with live protocol consequences: after that authority
//! checks every global GF(2) relation and signs the ordered row commitments, a
//! router or custody peer cannot mutate, relabel, replay across a context, or
//! equivocate one row into another certified session before the MPC output is
//! formed.

use std::process::Command;
use std::time::Duration;

use dregg_pq::{
    install_verified_mldsa_keygen_core_real, install_verified_mldsa_sign_core_real,
    install_verified_mldsa_verify_core, MlDsaKey, MlDsaKeygenCoreRealInstall,
    MlDsaSignCoreRealInstall, MlDsaVerifyCoreInstall, ML_DSA_PK_LEN,
};
use ed25519_dalek::SigningKey;
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, BfvPublicIdentity, ComputationIntegrityEvidence,
    ComputationIntegrityVerifier, ExpectedClearingContext, InMemoryReplayGuard, InputDigest,
    PartyIdentity,
};
use fhegg_fhe::mpc::Crossing;
use fhegg_fhe::mpc_party::transport::{
    EqualityCoordinatorMachine, EqualityPartyMachine, EqualityTransportError,
    EqualityTransportRoster,
};
use fhegg_fhe::mpc_party::{
    certified_dealer_triples, local_channels, run_party_equality, simulate_public_transcript,
    trusted_dealer_triples, PartyEqualityInput, PartyMpcError, PartyMpcSession,
    PreprocessingPqOperation, TripleFormationCertificate, TripleMaterial,
};
use rand::rngs::StdRng;
use rand::SeedableRng;

const N: usize = 3;
const MODULUS: u64 = 257;
const TEST_ROSTER_DIGEST: [u8; 64] = [0x5a; 64];

struct AcceptExactEvidence([u8; 32]);

impl ComputationIntegrityVerifier for AcceptExactEvidence {
    fn verifier_id(&self) -> [u8; 32] {
        self.0
    }

    fn verify(&self, _claim_digest: &[u8; 32], evidence: &[u8]) -> bool {
        evidence == b"exact-certified-preprocessing"
    }
}

fn in_verified_pq_child(test_name: &str, child_marker: &str, body: impl FnOnce()) {
    if std::env::var_os(child_marker).is_some() {
        assert!(
            std::env::var_os("DREGG_ALLOW_UNAUDITED_PQ").is_none(),
            "hybrid certificate tests must use the verified runtime"
        );
        assert!(matches!(
            install_verified_mldsa_keygen_core_real(
                dregg_lean_ffi::mldsa_keygen_real_core_available,
                |wire| dregg_lean_ffi::shadow_mldsa_keygen_real(wire).ok(),
            ),
            MlDsaKeygenCoreRealInstall::Installed | MlDsaKeygenCoreRealInstall::AlreadyInstalled
        ));
        assert!(matches!(
            install_verified_mldsa_sign_core_real(
                dregg_lean_ffi::fips204_sign_real_core_available,
                |wire| dregg_lean_ffi::shadow_fips204_sign_real(wire).ok(),
            ),
            MlDsaSignCoreRealInstall::Installed | MlDsaSignCoreRealInstall::AlreadyInstalled
        ));
        assert!(matches!(
            install_verified_mldsa_verify_core(
                dregg_lean_ffi::fips204_verify_real_core_available,
                |wire| dregg_lean_ffi::shadow_fips204_verify_real(wire).ok(),
            ),
            MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled
        ));
        body();
        return;
    }
    let status = Command::new(std::env::current_exe().expect("current test binary"))
        .args(["--exact", test_name, "--nocapture"])
        .env(child_marker, "1")
        .env_remove("DREGG_ALLOW_UNAUDITED_PQ")
        .status()
        .expect("spawn isolated hybrid-certificate test child");
    assert!(status.success(), "hybrid-certificate test child failed");
}

fn base_session(tag: u8) -> PartyMpcSession {
    PartyMpcSession::equality([tag; 32], N, 8, MODULUS, Duration::from_secs(2)).unwrap()
}

fn certified_batch(
    base: &PartyMpcSession,
    seed: u64,
) -> fhegg_fhe::mpc_party::CertifiedTripleBatch {
    certified_batch_for_roster(base, seed, TEST_ROSTER_DIGEST)
}

fn certified_batch_for_roster(
    base: &PartyMpcSession,
    seed: u64,
    roster_digest: [u8; 64],
) -> fhegg_fhe::mpc_party::CertifiedTripleBatch {
    let authority = SigningKey::from_bytes(&[0x41; 32]);
    let ml_dsa_authority = MlDsaKey::from_ed25519_seed(&authority.to_bytes());
    certified_dealer_triples(
        base,
        roster_digest,
        &mut StdRng::seed_from_u64(seed),
        &authority,
        &ml_dsa_authority,
    )
    .unwrap()
}

#[test]
fn certified_rows_bind_the_exact_batch_and_raw_execution_refuses() {
    in_verified_pq_child(
        "certified_rows_bind_the_exact_batch_and_raw_execution_refuses",
        "FHEGG_CERTIFIED_PREPROCESSING_HONEST_CHILD",
        certified_rows_bind_the_exact_batch_and_raw_execution_refuses_body,
    );
}

fn certified_rows_bind_the_exact_batch_and_raw_execution_refuses_body() {
    let base = base_session(0x71);
    let batch = certified_batch(&base, 0x7172);
    let (session, certificate, materials) = batch.into_parts();
    session.require_certified_preprocessing().unwrap();
    assert_eq!(certificate.n_parties(), N);
    assert_eq!(certificate.gates(), session.exact_and_gates());
    assert_eq!(certificate.row_commitments().len(), N);
    assert_eq!(
        session.preprocessing_binding().unwrap().batch_digest(),
        certificate.digest()
    );
    let certificate_bytes = certificate.canonical_bytes();
    let decoded_certificate =
        TripleFormationCertificate::from_canonical_bytes(&certificate_bytes).unwrap();
    assert_eq!(
        &decoded_certificate,
        session.preprocessing_certificate().unwrap()
    );
    assert_eq!(
        base.clone()
            .with_public_preprocessing_certificate(decoded_certificate)
            .unwrap(),
        session,
        "restart reconstruction must preserve the exact FHTRI004 session domain",
    );
    let mut mutated_certificate = certificate_bytes;
    *mutated_certificate.last_mut().unwrap() ^= 1;
    assert!(TripleFormationCertificate::from_canonical_bytes(&mutated_certificate).is_err());

    let certificate_bytes = certificate.canonical_bytes();
    let mut downgraded_certificate = certificate_bytes.clone();
    downgraded_certificate[..8].copy_from_slice(b"FHTFC003");
    assert!(TripleFormationCertificate::from_canonical_bytes(&downgraded_certificate).is_err());
    assert!(TripleFormationCertificate::from_canonical_bytes(
        &certificate_bytes[..certificate_bytes.len() - 1]
    )
    .is_err());
    let mut trailing_certificate = certificate_bytes.clone();
    trailing_certificate.push(0);
    assert!(TripleFormationCertificate::from_canonical_bytes(&trailing_certificate).is_err());
    let n_parties_offset = 8 + 32 + 64 + 32 + ML_DSA_PK_LEN;
    let mut hostile_count = certificate_bytes.clone();
    hostile_count[n_parties_offset..n_parties_offset + 8].copy_from_slice(&u64::MAX.to_be_bytes());
    assert!(TripleFormationCertificate::from_canonical_bytes(&hostile_count).is_err());
    let receipt_offset = n_parties_offset + 8 + 8;
    let mut crossed_receipt_roster = certificate_bytes;
    crossed_receipt_roster[receipt_offset + 9 + 32] ^= 1;
    assert!(TripleFormationCertificate::from_canonical_bytes(&crossed_receipt_roster).is_err());

    assert!(matches!(
        trusted_dealer_triples(&session, &mut StdRng::seed_from_u64(0x7173)),
        Err(PartyMpcError::MissingCertifiedPreprocessing)
    ));

    // Exercise the protected-custody parser, not only in-memory dealer output.
    let wires = materials
        .iter()
        .map(|material| material.to_wire_bytes().unwrap())
        .collect::<Vec<_>>();
    let materials = wires
        .iter()
        .enumerate()
        .map(|(party, wire)| TripleMaterial::from_wire_bytes(&session, party, wire).unwrap())
        .collect::<Vec<_>>();

    // Equal modulo t: 20+30+27 = 10+11+56 = 77.
    let left = [20, 30, 27];
    let right = [10, 11, 56];
    let inputs = (0..N)
        .map(|party| {
            PartyEqualityInput::new(
                &session,
                party,
                left[party],
                right[party],
                &mut StdRng::seed_from_u64(0x7200 + party as u64),
            )
            .unwrap()
        })
        .collect::<Vec<_>>();
    let (_coordinator, endpoints) = local_channels(&session);
    for ((input, triples), endpoint) in inputs.into_iter().zip(materials).zip(endpoints) {
        assert!(matches!(
            run_party_equality(input, triples, endpoint),
            Err(PartyMpcError::CertifiedPreprocessingRequiresDurableCustody)
        ));
    }
}

#[test]
fn malformed_relabelled_replayed_and_equivocated_rows_refuse_before_a_gate() {
    in_verified_pq_child(
        "malformed_relabelled_replayed_and_equivocated_rows_refuse_before_a_gate",
        "FHEGG_CERTIFIED_PREPROCESSING_HOSTILE_CHILD",
        malformed_relabelled_replayed_and_equivocated_rows_refuse_before_a_gate_body,
    );
}

fn malformed_relabelled_replayed_and_equivocated_rows_refuse_before_a_gate_body() {
    let base_a = base_session(0x81);
    let batch_a = certified_batch(&base_a, 0x8182);
    let (session_a, certificate_a, materials_a) = batch_a.into_parts();
    let wires_a = materials_a
        .iter()
        .map(|material| material.to_wire_bytes().unwrap())
        .collect::<Vec<_>>();

    // The last byte is the c-share of the final AND gate.  This is the exact
    // mutation that flips the equality decision on the legacy path while all
    // bits and framing remain canonical.  The signed row commitment rejects it
    // before the material can enter a party machine.
    let mut malformed_relation = wires_a[0].clone();
    *malformed_relation.last_mut().unwrap() ^= 1;
    assert!(matches!(
        TripleMaterial::from_wire_bytes(&session_a, 0, &malformed_relation),
        Err(PartyMpcError::InvalidTripleFormationCertificate)
    ));

    // Both authority signatures are mandatory and checked independently of
    // the row hash. There is no Ed-only downgrade for a v4 custody wire.
    let ed25519_signature_offset = 8
        + 32
        + 64
        + 32
        + ML_DSA_PK_LEN
        + 8
        + 8
        + fhegg_fhe::mpc_party::authenticated_preprocessing::AUTHENTICATED_SACRIFICE_RECEIPT_BYTES
        + N * 32
        + 32;
    let mut forged_certificate = wires_a[0].clone();
    forged_certificate[ed25519_signature_offset] ^= 1;
    assert!(matches!(
        TripleMaterial::from_wire_bytes(&session_a, 0, &forged_certificate),
        Err(PartyMpcError::InvalidTripleFormationCertificate)
    ));
    let mut missing_pq_half = wires_a[0].clone();
    missing_pq_half[ed25519_signature_offset + 64] ^= 1;
    assert!(matches!(
        TripleMaterial::from_wire_bytes(&session_a, 0, &missing_pq_half),
        Err(PartyMpcError::InvalidTripleFormationCertificate)
    ));
    let mut tampered_roster = wires_a[0].clone();
    tampered_roster[8 + 32] ^= 1;
    assert!(matches!(
        TripleMaterial::from_wire_bytes(&session_a, 0, &tampered_roster),
        Err(PartyMpcError::SessionMismatch)
    ));
    let receipt_offset = 8 + 32 + 64 + 32 + ML_DSA_PK_LEN + 8 + 8;
    let mut tampered_transcript = wires_a[0].clone();
    tampered_transcript[receipt_offset + 200] ^= 1;
    assert!(matches!(
        TripleMaterial::from_wire_bytes(&session_a, 0, &tampered_transcript),
        Err(PartyMpcError::InvalidAuthenticatedPreprocessing) | Err(PartyMpcError::SessionMismatch)
    ));
    let mut downgraded_v3 = wires_a[0].clone();
    downgraded_v3[..8].copy_from_slice(b"FHTRI003");
    assert!(matches!(
        TripleMaterial::from_wire_bytes(&session_a, 0, &downgraded_v3),
        Err(PartyMpcError::InvalidTripleFormationCertificate)
    ));

    assert!(matches!(
        TripleMaterial::from_wire_bytes(&session_a, 1, &wires_a[0]),
        Err(PartyMpcError::SessionMismatch)
    ));

    let base_b = base_session(0x82);
    let batch_b = certified_batch(&base_b, 0x8283);
    let (session_b, certificate_b, mut materials_b) = batch_b.into_parts();
    assert_ne!(certificate_a.digest(), certificate_b.digest());
    assert!(matches!(
        TripleMaterial::from_wire_bytes(&session_b, 0, &wires_a[0]),
        Err(PartyMpcError::SessionMismatch)
    ));

    // Even under the same public base session, a fresh batch has a distinct
    // session identity. Mixing its valid party-0 row into batch A fails before
    // input ingress or the first Beaver opening.
    let same_context_batch = certified_batch(&base_a, 0x8384);
    let (same_context_session, _, mut same_context_materials) = same_context_batch.into_parts();
    assert_ne!(
        session_a.preprocessing_binding(),
        same_context_session.preprocessing_binding()
    );

    // The exact same random row stream signed by a different paired authority
    // is a different session. A valid attacker certificate cannot substitute
    // for the relying party's pinned hybrid authority.
    let attacker_ed25519 = SigningKey::from_bytes(&[0x42; 32]);
    let attacker_ml_dsa = MlDsaKey::from_ed25519_seed(&attacker_ed25519.to_bytes());
    let attacker_batch = certified_dealer_triples(
        &base_a,
        TEST_ROSTER_DIGEST,
        &mut StdRng::seed_from_u64(0x8182),
        &attacker_ed25519,
        &attacker_ml_dsa,
    )
    .unwrap();
    let (attacker_session, _, mut attacker_materials) = attacker_batch.into_parts();
    assert_ne!(
        session_a.preprocessing_binding(),
        attacker_session.preprocessing_binding()
    );
    let attacker_wire = attacker_materials.remove(0).to_wire_bytes().unwrap();
    assert!(matches!(
        TripleMaterial::from_wire_bytes(&session_a, 0, &attacker_wire),
        Err(PartyMpcError::SessionMismatch)
    ));
    let input_a =
        PartyEqualityInput::new(&session_a, 0, 20, 10, &mut StdRng::seed_from_u64(0x8485)).unwrap();
    let (_coordinator, mut endpoints) = local_channels(&session_a);
    let error = run_party_equality(
        input_a,
        same_context_materials.remove(0),
        endpoints.remove(0),
    )
    .unwrap_err();
    assert_eq!(
        error,
        PartyMpcError::CertifiedPreprocessingRequiresDurableCustody
    );

    // Positive control: the other context's own certified row still parses;
    // refusals above did not poison unrelated material.
    let wire_b = materials_b.remove(0).to_wire_bytes().unwrap();
    TripleMaterial::from_wire_bytes(&session_b, 0, &wire_b).unwrap();
}

#[test]
fn transport_machines_refuse_uncustodied_certified_rows() {
    in_verified_pq_child(
        "transport_machines_refuse_uncustodied_certified_rows",
        "FHEGG_CERTIFIED_PREPROCESSING_TRANSPORT_CHILD",
        transport_machines_refuse_uncustodied_certified_rows_body,
    );
}

fn transport_machines_refuse_uncustodied_certified_rows_body() {
    let base = base_session(0x91);
    let keys = [
        SigningKey::from_bytes(&[0x51; 32]),
        SigningKey::from_bytes(&[0x52; 32]),
        SigningKey::from_bytes(&[0x53; 32]),
    ];
    let coordinator = SigningKey::from_bytes(&[0x54; 32]);
    let roster = EqualityTransportRoster::new(
        keys.iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        coordinator.verifying_key().to_bytes(),
    )
    .unwrap();
    let roster_digest = roster.preprocessing_roster_digest();
    let (session_a, _, mut materials_a) =
        certified_batch_for_roster(&base, 0x9192, roster_digest).into_parts();
    let (session_b, _, mut materials_b) =
        certified_batch_for_roster(&base, 0x9293, roster_digest).into_parts();
    assert_ne!(
        session_a.preprocessing_binding(),
        session_b.preprocessing_binding()
    );
    let substituted_coordinator = SigningKey::from_bytes(&[0x55; 32]);
    let substituted_roster = EqualityTransportRoster::new(
        keys.iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        substituted_coordinator.verifying_key().to_bytes(),
    )
    .unwrap();
    assert!(matches!(
        EqualityCoordinatorMachine::new(
            session_a.clone(),
            substituted_roster,
            substituted_coordinator,
        ),
        Err(EqualityTransportError::InvalidConfiguration(_))
    ));
    let input_a =
        PartyEqualityInput::new(&session_a, 0, 20, 10, &mut StdRng::seed_from_u64(0x9394)).unwrap();
    let input_b =
        PartyEqualityInput::new(&session_b, 1, 30, 11, &mut StdRng::seed_from_u64(0x9495)).unwrap();
    assert!(matches!(
        EqualityPartyMachine::new(
            session_a,
            roster.clone(),
            0,
            keys[0].clone(),
            input_a,
            materials_a.remove(0),
        ),
        Err(EqualityTransportError::InvalidConfiguration(
            "certified preprocessing requires a durable-custody party machine"
        ))
    ));
    assert!(matches!(
        EqualityPartyMachine::new(
            session_b,
            roster,
            1,
            keys[1].clone(),
            input_b,
            materials_b.remove(1),
        ),
        Err(EqualityTransportError::InvalidConfiguration(
            "certified preprocessing requires a durable-custody party machine"
        ))
    ));
}

#[test]
fn receipt_claim_refuses_authority_or_batch_substitution_and_replay() {
    in_verified_pq_child(
        "receipt_claim_refuses_authority_or_batch_substitution_and_replay",
        "FHEGG_CERTIFIED_PREPROCESSING_RECEIPT_CHILD",
        receipt_claim_refuses_authority_or_batch_substitution_and_replay_body,
    );
}

fn receipt_claim_refuses_authority_or_batch_substitution_and_replay_body() {
    let base = PartyMpcSession::new([0xb1; 32], N, 2, 8, MODULUS, Duration::from_secs(2)).unwrap();
    let (session_a, _, _) = certified_batch(&base, 0xb2b3).into_parts();
    let (session_b, _, _) = certified_batch(&base, 0xb3b4).into_parts();
    let crossing = Crossing {
        p_star: Some(1),
        v_star: 3,
    };
    let transcript_a =
        simulate_public_transcript(&crossing, &session_a, &mut StdRng::seed_from_u64(0xb4b5))
            .unwrap();
    let transcript_b =
        simulate_public_transcript(&crossing, &session_b, &mut StdRng::seed_from_u64(0xb4b5))
            .unwrap();
    let roster = (0..N)
        .map(|party| PartyIdentity::from_public_identity_bytes(&[0xc0 + party as u8; 32]))
        .collect::<Vec<_>>();
    let bfv = BfvPublicIdentity {
        n_parties: N as u64,
        opening_threshold: N as u64,
        degree: 8,
        moduli_digest: [0xc4; 32],
        plaintext_modulus: MODULUS,
        crp_seed: [0xc5; 32],
        collective_public_key_digest: [0xc6; 32],
    };
    let inputs = vec![InputDigest::commitment([0xc7; 32])];
    let context_a = ExpectedClearingContext {
        session: &session_a,
        ordered_roster: &roster,
        bfv: &bfv,
        ordered_inputs: &inputs,
        transcript: &transcript_a,
        crossing: &crossing,
    };
    let context_b = ExpectedClearingContext {
        session: &session_b,
        ordered_roster: &roster,
        bfv: &bfv,
        ordered_inputs: &inputs,
        transcript: &transcript_b,
        crossing: &crossing,
    };
    let verifier = AcceptExactEvidence([0xc8; 32]);
    let receipt = AttestedClearingReceipt::issue(
        &context_a,
        ComputationIntegrityEvidence::External {
            verifier_id: verifier.verifier_id(),
            evidence: b"exact-certified-preprocessing".to_vec(),
        },
    )
    .unwrap();
    assert_eq!(
        receipt.claim.preprocessing.as_ref(),
        session_a.preprocessing_binding()
    );
    assert_eq!(
        receipt.verify_binding(&context_b),
        Err(AttestationError::BindingMismatch),
        "a fresh certified batch under the same nonce must alter the canonical claim"
    );

    let attacker_ed25519 = SigningKey::from_bytes(&[0xc9; 32]);
    let attacker_ml_dsa = MlDsaKey::from_ed25519_seed(&attacker_ed25519.to_bytes());
    let (attacker_session, _, _) = certified_dealer_triples(
        &base,
        TEST_ROSTER_DIGEST,
        &mut StdRng::seed_from_u64(0xb2b3),
        &attacker_ed25519,
        &attacker_ml_dsa,
    )
    .unwrap()
    .into_parts();
    let attacker_transcript = simulate_public_transcript(
        &crossing,
        &attacker_session,
        &mut StdRng::seed_from_u64(0xb4b5),
    )
    .unwrap();
    let attacker_context = ExpectedClearingContext {
        session: &attacker_session,
        ordered_roster: &roster,
        bfv: &bfv,
        ordered_inputs: &inputs,
        transcript: &attacker_transcript,
        crossing: &crossing,
    };
    assert_eq!(
        receipt.verify_binding(&attacker_context),
        Err(AttestationError::BindingMismatch),
        "a valid certificate from an unpinned authority must alter the canonical claim"
    );

    let mut replay = InMemoryReplayGuard::default();
    receipt
        .verify_full(&context_a, &verifier, &mut replay)
        .unwrap();
    assert_eq!(
        receipt.verify_full(&context_a, &verifier, &mut replay),
        Err(AttestationError::ReplayDetected)
    );
}

#[test]
fn certified_generator_refuses_the_explicit_unaudited_pq_escape_hatch() {
    const MARKER: &str = "FHEGG_CERTIFIED_PREPROCESSING_NO_CORE_CHILD";
    const TEST: &str = "certified_generator_refuses_the_explicit_unaudited_pq_escape_hatch";
    if std::env::var_os(MARKER).is_some() {
        assert!(std::env::var_os("DREGG_ALLOW_UNAUDITED_PQ").is_some());
        let base = base_session(0xa1);
        let ed25519 = SigningKey::from_bytes(&[0xa2; 32]);
        // The explicit test escape hatch permits construction of the fallback
        // key, but the protocol authority must still refuse before signing.
        let ml_dsa = MlDsaKey::from_ed25519_seed(&ed25519.to_bytes());
        assert!(matches!(
            certified_dealer_triples(
                &base,
                TEST_ROSTER_DIGEST,
                &mut StdRng::seed_from_u64(0xa3a4),
                &ed25519,
                &ml_dsa,
            ),
            Err(PartyMpcError::VerifiedPostQuantumRuntimeUnavailable {
                operation: PreprocessingPqOperation::Keygen,
            })
        ));
        return;
    }
    let status = Command::new(std::env::current_exe().expect("current test binary"))
        .args(["--exact", TEST, "--nocapture"])
        .env(MARKER, "1")
        .env("DREGG_ALLOW_UNAUDITED_PQ", "1")
        .status()
        .expect("spawn isolated no-core refusal child");
    assert!(status.success(), "no-core refusal child failed");
}
