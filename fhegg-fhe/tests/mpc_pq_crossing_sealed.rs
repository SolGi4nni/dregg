//! End-to-end teeth for the v5 native-PQ sealed crossing transport.
//!
//! Run with verified dregg-pq cores installed, or under the explicit
//! `DREGG_ALLOW_UNAUDITED_PQ=1` test override on an isolated build worker.

use std::thread;
use std::time::{Duration, Instant};

use ed25519_dalek::SigningKey;
use fhegg_fhe::attestation::{
    AttestedClearingReceipt, BfvPublicIdentity, ComputationIntegrityEvidence,
    ComputationIntegrityResidual, ExpectedClearingContext, InputDigest,
    NativePqAuthenticatedQuorumVerifier, NativePqPartyPublicKey,
};
use fhegg_fhe::mpc_party::transport::{
    is_native_post_quantum_crossing_control_frame,
    is_native_post_quantum_crossing_public_evidence_frame,
    verify_native_post_quantum_public_crossing_transcript, CrossingCoordinatorMachine,
    CrossingPartyMachine, CrossingTransportRoster, NativePqCrossingEndpointSeal,
    NativePqTransportIdentity, TransportSecurityProfile,
};
use fhegg_fhe::mpc_party::{
    trusted_dealer_triples, DistributedRun, PartyArithmeticInput, PartyMpcSession,
};
use rand::rngs::StdRng;
use rand::SeedableRng;

// See `mpc_pq_transport.rs` — the native-PQ party identities abort the process with no verified
// core installed, and this binary asserted nothing. Installed at process start.
dregg_pq_testkit::install_at_process_start!();

const N: usize = 2;

fn identities() -> (Vec<NativePqTransportIdentity>, NativePqTransportIdentity) {
    let parties = [[0x41; 32], [0x42; 32]]
        .into_iter()
        .map(|seed| NativePqTransportIdentity::generate(SigningKey::from_bytes(&seed)))
        .collect();
    let coordinator = NativePqTransportIdentity::generate(SigningKey::from_bytes(&[0x43; 32]));
    (parties, coordinator)
}

fn drive(
    session: &PartyMpcSession,
    roster: &CrossingTransportRoster,
    party_ids: &[NativePqTransportIdentity],
    coordinator_id: &NativePqTransportIdentity,
) -> (
    DistributedRun,
    Vec<Vec<u8>>,
    Vec<NativePqCrossingEndpointSeal>,
) {
    let mut dealer = StdRng::seed_from_u64(0x5001);
    let triples = trusted_dealer_triples(session, &mut dealer).unwrap();
    let rows = [([2u64], [0u64]), ([0u64], [1u64])];
    let mut parties = rows
        .into_iter()
        .zip(triples)
        .enumerate()
        .map(|(party, ((demand, supply), preprocessing))| {
            let input = PartyArithmeticInput::new(
                session,
                party,
                &demand,
                &supply,
                &mut StdRng::seed_from_u64(0x5100 + party as u64),
            )
            .unwrap();
            CrossingPartyMachine::new_native_post_quantum_sealed(
                session.clone(),
                roster.clone(),
                party,
                party_ids[party].clone(),
                input,
                preprocessing,
            )
            .unwrap()
        })
        .collect::<Vec<_>>();
    let mut coordinator = CrossingCoordinatorMachine::new_native_post_quantum_sealed(
        session.clone(),
        roster.clone(),
        coordinator_id.clone(),
    )
    .unwrap();
    let mut public_frames = Vec::new();
    let mut party_done = vec![false; N];
    let mut party_seals: Vec<Option<NativePqCrossingEndpointSeal>> = (0..N).map(|_| None).collect();
    let mut coordinator_seal = None;
    let mut run = None;
    let deadline = Instant::now() + Duration::from_secs(120);
    while run.is_none() || party_seals.iter().any(Option::is_none) || coordinator_seal.is_none() {
        assert!(Instant::now() < deadline, "sealed v5 crossing stalled");
        let mut progressed = false;
        for sender in 0..N {
            while let Some(frame) = parties[sender].try_next_frame().unwrap() {
                progressed = true;
                let recipient = frame.recipient();
                let bytes = frame.into_bytes();
                if is_native_post_quantum_crossing_control_frame(&bytes) {
                    assert!(!is_native_post_quantum_crossing_public_evidence_frame(
                        &bytes
                    ));
                } else {
                    assert!(is_native_post_quantum_crossing_public_evidence_frame(
                        &bytes
                    ));
                    if recipient == roster.coordinator() {
                        public_frames.push(bytes.clone());
                    }
                }
                if recipient == roster.coordinator() {
                    coordinator.accept_frame(&bytes).unwrap();
                } else {
                    parties[recipient].accept_frame(&bytes).unwrap();
                }
            }
        }
        while let Some(frame) = coordinator.try_next_frame().unwrap() {
            progressed = true;
            let recipient = frame.recipient();
            let bytes = frame.into_bytes();
            if is_native_post_quantum_crossing_control_frame(&bytes) {
                assert!(!is_native_post_quantum_crossing_public_evidence_frame(
                    &bytes
                ));
            } else {
                assert!(is_native_post_quantum_crossing_public_evidence_frame(
                    &bytes
                ));
                public_frames.push(bytes.clone());
            }
            parties[recipient].accept_frame(&bytes).unwrap();
        }
        for party in 0..N {
            if !party_done[party] && parties[party].try_result().unwrap().is_some() {
                party_done[party] = true;
                progressed = true;
            }
            if party_done[party] && party_seals[party].is_none() {
                if let Some(seal) = parties[party].try_terminal_seal().unwrap() {
                    assert_eq!(seal.endpoint(), party);
                    party_seals[party] = Some(seal);
                    progressed = true;
                }
            }
        }
        if run.is_none() {
            if let Some(result) = coordinator.try_result().unwrap() {
                run = Some(result);
                progressed = true;
            }
        }
        if run.is_some() && coordinator_seal.is_none() {
            if let Some(seal) = coordinator.try_terminal_seal().unwrap() {
                assert_eq!(seal.endpoint(), roster.coordinator());
                coordinator_seal = Some(seal);
                progressed = true;
            }
        }
        if !progressed {
            thread::yield_now();
        }
    }
    let mut seals = party_seals
        .into_iter()
        .map(Option::unwrap)
        .collect::<Vec<_>>();
    seals.push(coordinator_seal.unwrap());
    (run.unwrap(), public_frames, seals)
}

#[test]
fn sealed_native_pq_crossing_issues_only_the_exact_claim_bound_capability() {
    let session = PartyMpcSession::new([0x61; 32], N, 1, 8, 257, Duration::from_secs(90)).unwrap();
    let (party_ids, coordinator_id) = identities();
    let roster = CrossingTransportRoster::new_native_post_quantum_sealed_crossing(
        party_ids
            .iter()
            .map(NativePqTransportIdentity::public_identity)
            .collect(),
        coordinator_id.public_identity(),
    )
    .unwrap();
    assert_eq!(
        roster.security_profile(),
        TransportSecurityProfile::NativePostQuantumSealedCrossing
    );
    let quorum_keys = party_ids
        .iter()
        .map(|identity| {
            let public = identity.public_identity();
            NativePqPartyPublicKey::new(public.ed25519(), public.ml_dsa().to_vec())
        })
        .collect::<Vec<_>>();
    let quorum = NativePqAuthenticatedQuorumVerifier::new(quorum_keys, N).unwrap();
    let (run, mut frames, mut seals) = drive(&session, &roster, &party_ids, &coordinator_id);
    assert_eq!(run.crossing.p_star, Some(0));
    assert_eq!(run.crossing.v_star, 1);

    let bfv = BfvPublicIdentity {
        n_parties: N as u64,
        opening_threshold: N as u64,
        degree: 8,
        moduli_digest: [0x71; 32],
        plaintext_modulus: session.plaintext_modulus(),
        crp_seed: [0x72; 32],
        collective_public_key_digest: [0x73; 32],
    };
    let inputs = vec![InputDigest::commitment([0x74; 32])];
    let context = ExpectedClearingContext {
        session: &session,
        ordered_roster: quorum.ordered_roster(),
        bfv: &bfv,
        ordered_inputs: &inputs,
        transcript: &run.transcript,
        crossing: &run.crossing,
    };
    let receipt = AttestedClearingReceipt::issue(
        &context,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .unwrap();
    let token = verify_native_post_quantum_public_crossing_transcript(
        &session,
        &roster,
        &frames,
        &seals,
        &run.crossing,
        &run.transcript,
        &receipt.claim,
    )
    .unwrap();
    quorum
        .sign_verified_crossing_claim(
            &receipt.claim,
            &context,
            &token,
            0,
            &SigningKey::from_bytes(&[0x41; 32]),
            party_ids[0].ml_dsa_signing_key(),
        )
        .expect("exact verified crossing token unlocks one exact claim signature");

    let mut substituted_bfv = bfv.clone();
    substituted_bfv.collective_public_key_digest[0] ^= 1;
    let substituted_context = ExpectedClearingContext {
        session: &session,
        ordered_roster: quorum.ordered_roster(),
        bfv: &substituted_bfv,
        ordered_inputs: &inputs,
        transcript: &run.transcript,
        crossing: &run.crossing,
    };
    let substituted_receipt = AttestedClearingReceipt::issue(
        &substituted_context,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .unwrap();
    assert!(
        quorum
            .sign_verified_crossing_claim(
                &substituted_receipt.claim,
                &substituted_context,
                &token,
                0,
                &SigningKey::from_bytes(&[0x41; 32]),
                party_ids[0].ml_dsa_signing_key(),
            )
            .is_err(),
        "an old transport token cannot authorize a self-consistent substituted BFV claim"
    );

    assert!(
        verify_native_post_quantum_public_crossing_transcript(
            &session,
            &roster,
            &frames,
            &seals[..seals.len() - 1],
            &run.crossing,
            &run.transcript,
            &receipt.claim,
        )
        .is_err(),
        "missing one endpoint seal must fail closed"
    );
    seals.swap(0, 1);
    assert!(
        verify_native_post_quantum_public_crossing_transcript(
            &session,
            &roster,
            &frames,
            &seals,
            &run.crossing,
            &run.transcript,
            &receipt.claim,
        )
        .is_err(),
        "reordered endpoint seals must fail closed"
    );
    seals.swap(0, 1);

    let frame_index = frames.iter().position(|frame| frame.len() > 120).unwrap();
    let byte = frames[frame_index].len() - 33;
    frames[frame_index][byte] ^= 1;
    assert!(
        verify_native_post_quantum_public_crossing_transcript(
            &session,
            &roster,
            &frames,
            &seals,
            &run.crossing,
            &run.transcript,
            &receipt.claim,
        )
        .is_err(),
        "substituted public frame must break its sealed route root"
    );
}
