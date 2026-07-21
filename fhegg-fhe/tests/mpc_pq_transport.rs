//! Native-PQ PartyMPC transport teeth.
//!
//! Run this target in a process with either the verified ML-DSA/ML-KEM cores
//! installed or the explicit test-only `DREGG_ALLOW_UNAUDITED_PQ=1` override.

use std::thread;
use std::time::{Duration, Instant};

use ed25519_dalek::SigningKey;
use fhegg_fhe::mpc_party::transport::{
    AuthenticatedEqualityFrame, EqualityCoordinatorMachine, EqualityPartyMachine,
    EqualityTransportError, EqualityTransportRoster, NativePqTransportIdentity,
    NativePqTransportPublicIdentity, TransportSecurityProfile,
};
use fhegg_fhe::mpc_party::{
    trusted_dealer_triples, DistributedDecisionRun, PartyEqualityInput, PartyMpcSession,
};
use rand::rngs::StdRng;
use rand::SeedableRng;

const N: usize = 2;

fn native_identities() -> (Vec<NativePqTransportIdentity>, NativePqTransportIdentity) {
    let parties = [[0x81; 32], [0x82; 32]]
        .into_iter()
        .map(|seed| NativePqTransportIdentity::generate(SigningKey::from_bytes(&seed)))
        .collect();
    let coordinator = NativePqTransportIdentity::generate(SigningKey::from_bytes(&[0x91; 32]));
    (parties, coordinator)
}

fn native_roster(
    parties: &[NativePqTransportIdentity],
    coordinator: &NativePqTransportIdentity,
) -> EqualityTransportRoster {
    EqualityTransportRoster::new_native_post_quantum(
        parties
            .iter()
            .map(|identity| identity.public_identity())
            .collect(),
        coordinator.public_identity(),
    )
    .unwrap()
}

fn build_native_parties(
    session: &PartyMpcSession,
    roster: &EqualityTransportRoster,
    identities: &[NativePqTransportIdentity],
    dealer_seed: u64,
) -> Vec<EqualityPartyMachine> {
    let mut dealer = StdRng::seed_from_u64(dealer_seed);
    let triples = trusted_dealer_triples(session, &mut dealer).unwrap();
    triples
        .into_iter()
        .enumerate()
        .map(|(party, preprocessing)| {
            let mut ingress_rng = StdRng::seed_from_u64(dealer_seed ^ 0x9000 ^ party as u64);
            let input = PartyEqualityInput::new(
                session,
                party,
                [1, 0][party],
                [0, 1][party],
                &mut ingress_rng,
            )
            .unwrap();
            EqualityPartyMachine::new_native_post_quantum(
                session.clone(),
                roster.clone(),
                party,
                identities[party].clone(),
                input,
                preprocessing,
            )
            .unwrap()
        })
        .collect()
}

fn build_classical_party(
    session: &PartyMpcSession,
    roster: &EqualityTransportRoster,
    party: usize,
    seed: [u8; 32],
    dealer_seed: u64,
) -> EqualityPartyMachine {
    let mut dealer = StdRng::seed_from_u64(dealer_seed);
    let mut triples = trusted_dealer_triples(session, &mut dealer).unwrap();
    let preprocessing = triples.swap_remove(party);
    let mut ingress_rng = StdRng::seed_from_u64(dealer_seed ^ 0xa000 ^ party as u64);
    let input = PartyEqualityInput::new(
        session,
        party,
        [1, 0][party],
        [0, 1][party],
        &mut ingress_rng,
    )
    .unwrap();
    EqualityPartyMachine::new(
        session.clone(),
        roster.clone(),
        party,
        SigningKey::from_bytes(&seed),
        input,
        preprocessing,
    )
    .unwrap()
}

fn next_frame_to(
    machine: &mut EqualityPartyMachine,
    recipient: usize,
) -> (AuthenticatedEqualityFrame, Vec<AuthenticatedEqualityFrame>) {
    let deadline = Instant::now() + Duration::from_secs(30);
    let mut prior = Vec::new();
    loop {
        if let Some(frame) = machine.try_next_frame().unwrap() {
            if frame.recipient() == recipient && frame.sequence() == 0 {
                return (frame, prior);
            }
            prior.push(frame);
        }
        assert!(
            Instant::now() < deadline,
            "PartyMPC frame production stalled"
        );
        thread::yield_now();
    }
}

fn drive(
    mut parties: Vec<EqualityPartyMachine>,
    mut coordinator: EqualityCoordinatorMachine,
    roster: &EqualityTransportRoster,
) -> DistributedDecisionRun {
    let deadline = Instant::now() + Duration::from_secs(90);
    loop {
        let mut outbound = Vec::new();
        for party in &mut parties {
            while let Some(frame) = party.try_next_frame().unwrap() {
                outbound.push(frame);
            }
        }
        for frame in outbound {
            if frame.recipient() == roster.coordinator() {
                coordinator.accept_frame(frame.as_bytes()).unwrap();
            } else {
                parties[frame.recipient()]
                    .accept_frame(frame.as_bytes())
                    .unwrap();
            }
        }
        let mut outbound = Vec::new();
        while let Some(frame) = coordinator.try_next_frame().unwrap() {
            outbound.push(frame);
        }
        for frame in outbound {
            parties[frame.recipient()]
                .accept_frame(frame.as_bytes())
                .unwrap();
        }
        if let Some(decision) = coordinator.try_result().unwrap() {
            return decision;
        }
        assert!(
            Instant::now() < deadline,
            "native-PQ PartyMPC transport stalled"
        );
        thread::yield_now();
    }
}

#[test]
fn native_pq_transport_is_end_to_end_and_rejects_replay_downgrade_and_key_swap() {
    let session = PartyMpcSession::equality([0xa1; 32], N, 1, 2, Duration::from_secs(30)).unwrap();
    let (identities, coordinator_identity) = native_identities();
    let roster = native_roster(&identities, &coordinator_identity);
    assert_eq!(
        roster.security_profile(),
        TransportSecurityProfile::NativePostQuantum
    );
    let mut parties = build_native_parties(&session, &roster, &identities, 0xa101);
    let coordinator = EqualityCoordinatorMachine::new_native_post_quantum(
        session.clone(),
        roster.clone(),
        coordinator_identity.clone(),
    )
    .unwrap();

    // One genuine native-PQ peer frame is accepted exactly once. The replay is
    // rejected before it can deliver a second Boolean ingress message.
    let (native_frame, prior) = next_frame_to(&mut parties[1], 0);
    parties[0].accept_frame(native_frame.as_bytes()).unwrap();
    assert!(matches!(
        parties[0].accept_frame(native_frame.as_bytes()),
        Err(EqualityTransportError::SequenceMismatch {
            sender: 1,
            have: 0,
            need: 1
        })
    ));

    // The same Ed25519 roster in the named classical-compatibility profile
    // cannot consume a native frame: profile is part of both wire and session.
    let party_seeds = [[0x81; 32], [0x82; 32]];
    let classical_roster = EqualityTransportRoster::new_classical_compatibility(
        party_seeds
            .iter()
            .map(|seed| SigningKey::from_bytes(seed).verifying_key().to_bytes())
            .collect(),
        SigningKey::from_bytes(&[0x91; 32])
            .verifying_key()
            .to_bytes(),
    )
    .unwrap();
    let mut classical_party_zero =
        build_classical_party(&session, &classical_roster, 0, party_seeds[0], 0xb101);
    assert!(classical_party_zero
        .accept_frame(native_frame.as_bytes())
        .is_err());
    let mut classical_party_one =
        build_classical_party(&session, &classical_roster, 1, party_seeds[1], 0xb102);
    let (classical_frame, _) = next_frame_to(&mut classical_party_one, 0);
    assert!(parties[0].accept_frame(classical_frame.as_bytes()).is_err());

    // Swap only the enrolled ML-DSA keys of party 1 and the coordinator while
    // keeping every Ed25519 and ML-KEM key in its original slot. The roster is
    // structurally valid but names a different session; an unchanged party-0
    // frame from that roster cannot cross into the original native session.
    let public_zero = identities[0].public_identity();
    let public_one = identities[1].public_identity();
    let public_coordinator = coordinator_identity.public_identity();
    let changed_one = NativePqTransportPublicIdentity::from_parts(
        public_one.ed25519(),
        public_coordinator.ml_dsa().to_vec(),
        public_one.ml_kem_encapsulation_key().to_vec(),
    )
    .unwrap();
    let changed_coordinator = NativePqTransportPublicIdentity::from_parts(
        public_coordinator.ed25519(),
        public_one.ml_dsa().to_vec(),
        public_coordinator.ml_kem_encapsulation_key().to_vec(),
    )
    .unwrap();
    let changed_roster = EqualityTransportRoster::new_native_post_quantum(
        vec![public_zero, changed_one],
        changed_coordinator,
    )
    .unwrap();
    let mut changed_dealer = StdRng::seed_from_u64(0xc101);
    let changed_preprocessing = trusted_dealer_triples(&session, &mut changed_dealer)
        .unwrap()
        .remove(0);
    let mut changed_ingress = StdRng::seed_from_u64(0xc102);
    let changed_input = PartyEqualityInput::new(&session, 0, 1, 0, &mut changed_ingress).unwrap();
    let mut changed_party_zero = EqualityPartyMachine::new_native_post_quantum(
        session.clone(),
        changed_roster,
        0,
        identities[0].clone(),
        changed_input,
        changed_preprocessing,
    )
    .unwrap();
    let (changed_frame, _) = next_frame_to(&mut changed_party_zero, 1);
    assert!(matches!(
        parties[1].accept_frame(changed_frame.as_bytes()),
        Err(EqualityTransportError::SessionMismatch)
    ));

    // Continue the original execution after the hostile probes; the only
    // public result is the expected equality bit.
    for frame in prior {
        parties[frame.recipient()]
            .accept_frame(frame.as_bytes())
            .unwrap();
    }
    let decision = drive(parties, coordinator, &roster);
    assert!(decision.is_equal());
    assert!(decision.transcript.is_reveal_only(&session));
}
