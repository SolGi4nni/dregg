//! Hostile tests for the Cert-F receipt boundary.
//!
//! Cert-F remains a useful translation checker, but full receipt acceptance is
//! possible only through a relying-party semantic binder.  These tests pin the
//! attacks which a copied claim digest cannot prevent.

use std::time::Duration;

use ed25519_dalek::SigningKey;
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
    ClearingClaim, ComputationIntegrityEvidence, ComputationIntegrityResidual,
    ComputationIntegrityVerifier, Digest32, ExpectedClearingContext, InMemoryReplayGuard,
    InputDigest, PartyIdentity,
};
use fhegg_fhe::certf_integrity::{
    assemble_evidence, AllOfIntegrityVerifier, CertFClearingVerifier, CertFProgramBinder,
    CertFTranslationChecker, CertFVerifierPolicy, MAX_EXACT_F64_INTEGER,
};
use fhegg_fhe::mpc::Crossing;
use fhegg_fhe::mpc_party::{simulate_public_transcript, DistributedTranscript, PartyMpcSession};
use fhegg_solver::cert::CertF;
use fhegg_solver::pdhg::{cycle_lp, solve_cpu_exact};
use rand::rngs::StdRng;
use rand::SeedableRng;

const V_STAR: u64 = 8;

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

fn certificate_for_committed_volume() -> CertF {
    let lp = cycle_lp(4, &[2.0, 6.0, 4.0, 8.0], &[1.0; 4]);
    let (exact, _) = solve_cpu_exact(&lp, 10_000);
    let cert = CertF::from_solution(&lp, &exact.f, &exact.y, 0.1);
    assert!(cert.check_with(1e-6).valid);
    cert
}

/// A distinct public program with the same exact objective 8.
fn alternate_same_volume_program() -> CertF {
    let lp = cycle_lp(2, &[4.0, 9.0], &[1.0; 2]);
    let (exact, _) = solve_cpu_exact(&lp, 10_000);
    let cert = CertF::from_solution(&lp, &exact.f, &exact.y, 0.1);
    assert!(cert.check_with(1e-6).valid);
    cert
}

fn vec_bits(values: &[f64]) -> Vec<u64> {
    values.iter().map(|value| value.to_bits()).collect()
}

/// Test-only image of the production binder contract: the expected claim
/// sources/output and every public program field are independently configured.
#[derive(Clone, Debug)]
struct FixtureSemanticBinder {
    id: Digest32,
    ordered_inputs: Vec<InputDigest>,
    p_star: Option<u64>,
    n_nodes: usize,
    m_edges: usize,
    edges: Vec<(u32, u32)>,
    w: Vec<u64>,
    c: Vec<u64>,
    epsilon: u64,
}

impl FixtureSemanticBinder {
    fn new(id: u8, ordered_inputs: Vec<InputDigest>, p_star: Option<u64>, cert: &CertF) -> Self {
        Self {
            id: [id; 32],
            ordered_inputs,
            p_star,
            n_nodes: cert.n_nodes,
            m_edges: cert.m_edges,
            edges: cert.edges.clone(),
            w: vec_bits(&cert.w),
            c: vec_bits(&cert.c),
            epsilon: cert.epsilon.to_bits(),
        }
    }
}

impl CertFProgramBinder for FixtureSemanticBinder {
    fn binding_id(&self) -> Digest32 {
        self.id
    }

    fn binds(&self, claim: &ClearingClaim, cert: &CertF) -> bool {
        claim.ordered_inputs == self.ordered_inputs
            && claim.outcome.p_star == self.p_star
            && cert.n_nodes == self.n_nodes
            && cert.m_edges == self.m_edges
            && cert.edges == self.edges
            && vec_bits(&cert.w) == self.w
            && vec_bits(&cert.c) == self.c
            && cert.epsilon.to_bits() == self.epsilon
    }
}

fn verifier_for(
    cert: &CertF,
    expected_inputs: Vec<InputDigest>,
    p_star: Option<u64>,
) -> CertFClearingVerifier<FixtureSemanticBinder> {
    CertFClearingVerifier::new(
        FixtureSemanticBinder::new(0x41, expected_inputs, p_star, cert),
        CertFVerifierPolicy::reveal_boundary(),
    )
    .expect("valid policy")
}

fn receipt_with<B: CertFProgramBinder>(
    expected: &ExpectedClearingContext<'_>,
    cert: &CertF,
    verifier: &CertFClearingVerifier<B>,
) -> AttestedClearingReceipt {
    let mut receipt = AttestedClearingReceipt::issue(
        expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical claim issues");
    receipt.computation_integrity = ComputationIntegrityEvidence::External {
        verifier_id: verifier.verifier_id(),
        evidence: assemble_evidence(&receipt.claim_digest(), cert),
    };
    receipt
}

#[test]
fn explicitly_bound_translation_certificate_is_accepted() {
    let session = mpc_session(0x11);
    let roster = roster();
    let bfv = bfv();
    let inputs = inputs();
    let crossing = Crossing {
        p_star: Some(2),
        v_star: V_STAR,
    };
    let transcript = transcript(&session, &crossing);
    let expected = context(&session, &roster, &bfv, &inputs, &transcript, &crossing);
    let cert = certificate_for_committed_volume();
    let verifier = verifier_for(&cert, inputs.clone(), Some(2));
    let receipt = receipt_with(&expected, &cert, &verifier);

    receipt
        .verify_full(&expected, &verifier, &mut InMemoryReplayGuard::default())
        .expect("translation check plus explicit semantic binder accepts");
    assert!(
        !verifier.verify(
            &receipt.claim_digest(),
            match &receipt.computation_integrity {
                ComputationIntegrityEvidence::External { evidence, .. } => evidence,
                _ => unreachable!(),
            }
        ),
        "the digest-only verifier entry point must fail closed"
    );
}

#[test]
fn translation_check_alone_is_useful_but_not_semantic_binding() {
    let session = mpc_session(0x12);
    let roster = roster();
    let bfv = bfv();
    let inputs = inputs();
    let crossing = Crossing {
        p_star: Some(2),
        v_star: V_STAR,
    };
    let transcript = transcript(&session, &crossing);
    let expected = context(&session, &roster, &bfv, &inputs, &transcript, &crossing);
    let claim = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .unwrap()
    .claim;
    let cert = certificate_for_committed_volume();
    let evidence = assemble_evidence(&claim.digest(), &cert);
    let checker = CertFTranslationChecker::new(CertFVerifierPolicy::reveal_boundary()).unwrap();
    assert!(checker.check_claim(&claim, &evidence).is_some());
    // `CertFTranslationChecker` deliberately has no ComputationIntegrityVerifier impl.
}

#[test]
fn freshly_rebound_certificate_rejects_substituted_inputs() {
    let session = mpc_session(0x21);
    let roster = roster();
    let bfv = bfv();
    let honest_inputs = inputs();
    let mut substituted_inputs = honest_inputs.clone();
    substituted_inputs.swap(0, 1);
    let crossing = Crossing {
        p_star: Some(2),
        v_star: V_STAR,
    };
    let transcript = transcript(&session, &crossing);
    let substituted = context(
        &session,
        &roster,
        &bfv,
        &substituted_inputs,
        &transcript,
        &crossing,
    );
    let cert = certificate_for_committed_volume();
    let verifier = verifier_for(&cert, honest_inputs, Some(2));
    // The malicious producer gets a fresh matching digest; only the semantic
    // binder, not stale-digest detection, can reject this.
    let receipt = receipt_with(&substituted, &cert, &verifier);
    assert_eq!(
        receipt.verify_full(&substituted, &verifier, &mut InMemoryReplayGuard::default(),),
        Err(AttestationError::InvalidComputationIntegrityEvidence)
    );
}

#[test]
fn same_volume_different_public_program_is_rejected() {
    let session = mpc_session(0x22);
    let roster = roster();
    let bfv = bfv();
    let inputs = inputs();
    let crossing = Crossing {
        p_star: Some(2),
        v_star: V_STAR,
    };
    let transcript = transcript(&session, &crossing);
    let expected = context(&session, &roster, &bfv, &inputs, &transcript, &crossing);
    let expected_cert = certificate_for_committed_volume();
    let substituted = alternate_same_volume_program();
    let checker = CertFTranslationChecker::new(CertFVerifierPolicy::reveal_boundary()).unwrap();
    let verifier = verifier_for(&expected_cert, inputs.clone(), Some(2));
    let receipt = receipt_with(&expected, &substituted, &verifier);
    let evidence = match &receipt.computation_integrity {
        ComputationIntegrityEvidence::External { evidence, .. } => evidence,
        _ => unreachable!(),
    };
    assert!(
        checker.check_claim(&receipt.claim, evidence).is_some(),
        "both programs have the same V*: translation validation alone cannot distinguish them"
    );
    assert_eq!(
        receipt.verify_full(&expected, &verifier, &mut InMemoryReplayGuard::default(),),
        Err(AttestationError::InvalidComputationIntegrityEvidence)
    );
}

#[test]
fn freshly_rebound_certificate_rejects_wrong_pstar() {
    let session = mpc_session(0x23);
    let roster = roster();
    let bfv = bfv();
    let inputs = inputs();
    let wrong_crossing = Crossing {
        p_star: Some(4),
        v_star: V_STAR,
    };
    let wrong_transcript = transcript(&session, &wrong_crossing);
    let wrong = context(
        &session,
        &roster,
        &bfv,
        &inputs,
        &wrong_transcript,
        &wrong_crossing,
    );
    let cert = certificate_for_committed_volume();
    let verifier = verifier_for(&cert, inputs.clone(), Some(2));
    let receipt = receipt_with(&wrong, &cert, &verifier);
    assert_eq!(
        receipt.verify_full(&wrong, &verifier, &mut InMemoryReplayGuard::default()),
        Err(AttestationError::InvalidComputationIntegrityEvidence)
    );
}

fn wide_gap_certificate() -> CertF {
    // True optimum 100, but the zero flow and its dual only bracket [0,100].
    CertF {
        n_nodes: 2,
        m_edges: 2,
        edges: vec![(0, 1), (1, 0)],
        w: vec![1.0, 0.0],
        c: vec![100.0, 100.0],
        f: vec![0.0, 0.0],
        pi: vec![0.0, 0.0],
        s: vec![1.0, 0.0],
        epsilon: 100.0,
        primal_obj: 0.0,
        dual_obj: 100.0,
        duality_gap: 100.0,
        feas_residual: 0.0,
    }
}

#[test]
fn evidence_chosen_unbounded_epsilon_cannot_certify_an_interior_vstar() {
    let session = mpc_session(0x31);
    let roster = roster();
    let bfv = bfv();
    let inputs = inputs();
    let crossing = Crossing {
        p_star: Some(2),
        v_star: V_STAR,
    };
    let transcript = transcript(&session, &crossing);
    let expected = context(&session, &roster, &bfv, &inputs, &transcript, &crossing);
    let cert = wide_gap_certificate();
    assert!(
        cert.check().valid,
        "the attack is a self-valid Cert-F carrier"
    );
    let verifier = CertFClearingVerifier::new(
        FixtureSemanticBinder::new(0x42, inputs.clone(), Some(2), &cert),
        CertFVerifierPolicy::reveal_boundary(),
    )
    .unwrap();
    let receipt = receipt_with(&expected, &cert, &verifier);
    assert_eq!(
        receipt.verify_full(&expected, &verifier, &mut InMemoryReplayGuard::default(),),
        Err(AttestationError::InvalidComputationIntegrityEvidence)
    );
}

fn tight_self_loop(objective: f64) -> CertF {
    CertF {
        n_nodes: 1,
        m_edges: 1,
        edges: vec![(0, 0)],
        w: vec![1.0],
        c: vec![objective],
        f: vec![objective],
        pi: vec![0.0],
        s: vec![1.0],
        epsilon: 0.0,
        primal_obj: objective,
        dual_obj: objective,
        duality_gap: 0.0,
        feas_residual: 0.0,
    }
}

#[test]
fn adjacent_u64_values_above_two_pow_53_do_not_alias() {
    let session = mpc_session(0x32);
    let roster = roster();
    let bfv = bfv();
    let inputs = inputs();
    let crossing = Crossing {
        p_star: Some(2),
        v_star: V_STAR,
    };
    let transcript = transcript(&session, &crossing);
    let expected = context(&session, &roster, &bfv, &inputs, &transcript, &crossing);
    let mut claim = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .unwrap()
    .claim;
    claim.outcome.v_star = MAX_EXACT_F64_INTEGER + 1;
    assert_eq!(
        claim.outcome.v_star as f64, MAX_EXACT_F64_INTEGER as f64,
        "this is the alias the explicit integer bound must catch"
    );
    let cert = tight_self_loop(MAX_EXACT_F64_INTEGER as f64);
    assert!(cert.check_with(1e-6).valid);
    let mut policy = CertFVerifierPolicy::reveal_boundary();
    policy.max_capacity = MAX_EXACT_F64_INTEGER as f64;
    let verifier = CertFClearingVerifier::new(
        FixtureSemanticBinder::new(0x43, inputs, Some(2), &cert),
        policy,
    )
    .unwrap();
    let evidence = assemble_evidence(&claim.digest(), &cert);
    assert!(!verifier.verify_claim(&claim, &evidence));
}

fn scaled_tolerance_attack() -> CertF {
    // Default CertF tolerance is 1e-3*max(c)=2, so a whole unit of broken
    // conservation is (incorrectly for this receipt policy) admitted.
    CertF {
        n_nodes: 2,
        m_edges: 1,
        edges: vec![(0, 1)],
        w: vec![0.0],
        c: vec![2_000.0],
        f: vec![1.0],
        pi: vec![0.0, 0.0],
        s: vec![0.0],
        epsilon: 0.0,
        primal_obj: 0.0,
        dual_obj: 0.0,
        duality_gap: 0.0,
        feas_residual: 1.0,
    }
}

#[test]
fn capacity_scaled_default_tolerance_cannot_admit_unit_nonconservation() {
    let session = mpc_session(0x33);
    let roster = roster();
    let bfv = bfv();
    let inputs = inputs();
    let crossing = Crossing {
        p_star: None,
        v_star: 0,
    };
    let transcript = transcript(&session, &crossing);
    let expected = context(&session, &roster, &bfv, &inputs, &transcript, &crossing);
    let cert = scaled_tolerance_attack();
    assert!(
        cert.check().valid,
        "the legacy scale-derived tolerance admits it"
    );
    assert!(
        !cert.check_with(1e-6).valid,
        "the relying party's fixed tolerance rejects it"
    );
    let verifier = CertFClearingVerifier::new(
        FixtureSemanticBinder::new(0x44, inputs.clone(), None, &cert),
        CertFVerifierPolicy::reveal_boundary(),
    )
    .unwrap();
    let receipt = receipt_with(&expected, &cert, &verifier);
    assert_eq!(
        receipt.verify_full(&expected, &verifier, &mut InMemoryReplayGuard::default(),),
        Err(AttestationError::InvalidComputationIntegrityEvidence)
    );
}

#[test]
fn source_program_and_authenticated_quorum_are_both_required() {
    let keys: Vec<_> = [[0x71; 32], [0x72; 32], [0x73; 32]]
        .into_iter()
        .map(|seed| SigningKey::from_bytes(&seed))
        .collect();
    let quorum = AuthenticatedQuorumVerifier::new(
        keys.iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .expect("valid 2-of-3 quorum");
    let session = mpc_session(0x41);
    let roster = quorum.ordered_roster().to_vec();
    let bfv = bfv();
    let inputs = inputs();
    let crossing = Crossing {
        p_star: Some(2),
        v_star: V_STAR,
    };
    let transcript = transcript(&session, &crossing);
    let expected = context(&session, &roster, &bfv, &inputs, &transcript, &crossing);
    let cert = certificate_for_committed_volume();
    let semantic = FixtureSemanticBinder::new(0x45, inputs.clone(), Some(2), &cert);
    let certf =
        CertFClearingVerifier::new(semantic, CertFVerifierPolicy::reveal_boundary()).unwrap();
    let mut receipt = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .unwrap();
    let digest = receipt.claim_digest();
    let certf_evidence = assemble_evidence(&digest, &cert);
    let signatures = [
        quorum
            .sign_claim(&digest, 0, &keys[0])
            .expect("party 0 signs"),
        quorum
            .sign_claim(&digest, 2, &keys[2])
            .expect("party 2 signs"),
    ];
    let quorum_envelope = quorum
        .assemble_evidence(&digest, &signatures)
        .expect("2-of-3 quorum evidence");
    let ComputationIntegrityEvidence::External {
        evidence: quorum_evidence,
        ..
    } = quorum_envelope
    else {
        unreachable!()
    };
    let verifier = AllOfIntegrityVerifier::new(certf, quorum);
    receipt.computation_integrity = verifier
        .assemble_evidence(&certf_evidence, &quorum_evidence)
        .unwrap();
    receipt
        .verify_full(&expected, &verifier, &mut InMemoryReplayGuard::default())
        .expect("source/program binding and real authenticated quorum both accept");

    for (first, second) in [
        (&[][..], quorum_evidence.as_slice()),
        (certf_evidence.as_slice(), &[][..]),
    ] {
        let mut missing_leg = receipt.clone();
        missing_leg.computation_integrity = verifier.assemble_evidence(first, second).unwrap();
        assert_eq!(
            missing_leg.verify_full(&expected, &verifier, &mut InMemoryReplayGuard::default(),),
            Err(AttestationError::InvalidComputationIntegrityEvidence),
            "neither the Cert-F/source leg nor the quorum leg may replace the other"
        );
    }
}
