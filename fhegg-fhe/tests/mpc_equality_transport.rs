use std::thread;
use std::time::{Duration, Instant};

use ed25519_dalek::SigningKey;
use fhegg_fhe::mpc_party::transport::{
    AuthenticatedEqualityFrame, EqualityCoordinatorMachine, EqualityPartyMachine,
    EqualityTransportError, EqualityTransportRoster,
};
use fhegg_fhe::mpc_party::{
    trusted_dealer_triples, DistributedDecisionRun, PartyEqualityInput, PartyMpcSession,
};
use rand::rngs::StdRng;
use rand::SeedableRng;

const N: usize = 3;
const VALUE_BITS: usize = 8;
const MODULUS: u64 = 65_537;

fn transport_keys() -> (Vec<[u8; 32]>, [u8; 32], EqualityTransportRoster) {
    let party_seeds = vec![[0x31; 32], [0x32; 32], [0x33; 32]];
    let coordinator_seed = [0x41; 32];
    let party_public = party_seeds
        .iter()
        .map(|seed| SigningKey::from_bytes(seed).verifying_key().to_bytes())
        .collect();
    let coordinator_public = SigningKey::from_bytes(&coordinator_seed)
        .verifying_key()
        .to_bytes();
    let roster = EqualityTransportRoster::new(party_public, coordinator_public).unwrap();
    (party_seeds, coordinator_seed, roster)
}

fn build_parties(
    session: &PartyMpcSession,
    roster: &EqualityTransportRoster,
    party_seeds: &[[u8; 32]],
    dealer_seed: u64,
    left: [u64; N],
    right: [u64; N],
) -> Vec<EqualityPartyMachine> {
    let mut dealer = StdRng::seed_from_u64(dealer_seed);
    let triples = trusted_dealer_triples(session, &mut dealer).unwrap();
    triples
        .into_iter()
        .enumerate()
        .map(|(party, preprocessing)| {
            let mut ingress_rng = StdRng::seed_from_u64(dealer_seed ^ 0x5100 ^ party as u64);
            let input = PartyEqualityInput::new(
                session,
                party,
                left[party],
                right[party],
                &mut ingress_rng,
            )
            .unwrap();
            EqualityPartyMachine::new(
                session.clone(),
                roster.clone(),
                party,
                SigningKey::from_bytes(&party_seeds[party]),
                input,
                preprocessing,
            )
            .unwrap()
        })
        .collect()
}

fn drive_transport(
    mut parties: Vec<EqualityPartyMachine>,
    mut coordinator: EqualityCoordinatorMachine,
    roster: &EqualityTransportRoster,
) -> DistributedDecisionRun {
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        let mut outbound = Vec::new();
        for machine in &mut parties {
            while let Some(frame) = machine.try_next_frame().unwrap() {
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

        let mut broadcasts = Vec::new();
        while let Some(frame) = coordinator.try_next_frame().unwrap() {
            broadcasts.push(frame);
        }
        for frame in broadcasts {
            parties[frame.recipient()]
                .accept_frame(frame.as_bytes())
                .unwrap();
        }

        if let Some(decision) = coordinator.try_result().unwrap() {
            return decision;
        }
        assert!(
            Instant::now() < deadline,
            "authenticated equality transport timed out"
        );
        thread::yield_now();
    }
}

fn next_frame(machine: &mut EqualityPartyMachine) -> AuthenticatedEqualityFrame {
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        if let Some(frame) = machine.try_next_frame().unwrap() {
            return frame;
        }
        assert!(
            Instant::now() < deadline,
            "party transport did not emit a frame"
        );
        thread::yield_now();
    }
}

#[test]
fn authenticated_equality_transport_is_reveal_only_and_fail_closed() {
    let session =
        PartyMpcSession::equality([0x51; 32], N, VALUE_BITS, MODULUS, Duration::from_secs(5))
            .unwrap();
    let (party_seeds, coordinator_seed, roster) = transport_keys();
    let mut parties = build_parties(
        &session,
        &roster,
        &party_seeds,
        0x5152,
        [20, 30, 27],
        [10, 11, 56],
    );
    let mut coordinator = EqualityCoordinatorMachine::new(
        session.clone(),
        roster.clone(),
        SigningKey::from_bytes(&coordinator_seed),
    )
    .unwrap();

    // Pull party 1's complete ingress burst. Every recipient gets demand
    // sequence 0 followed by supply sequence 1. Reordering is refused without
    // consuming the expected sequence; canonical delivery can then continue.
    let mut buffered = Vec::new();
    let reordered_index = loop {
        let frame = next_frame(&mut parties[1]);
        let is_target = frame.recipient() == 0 && frame.sequence() == 1;
        buffered.push(frame);
        if is_target {
            break buffered.len() - 1;
        }
    };
    assert!(matches!(
        parties[0].accept_frame(buffered[reordered_index].as_bytes()),
        Err(EqualityTransportError::SequenceMismatch {
            sender: 1,
            have: 1,
            need: 0
        })
    ));

    // A valid frame advances exactly once; exact replay is a duplicate and is
    // refused before a second internal peer message can be delivered.
    let first_to_zero = buffered
        .iter()
        .position(|frame| frame.recipient() == 0 && frame.sequence() == 0)
        .unwrap();
    parties[0]
        .accept_frame(buffered[first_to_zero].as_bytes())
        .unwrap();
    assert!(matches!(
        parties[0].accept_frame(buffered[first_to_zero].as_bytes()),
        Err(EqualityTransportError::SequenceMismatch {
            sender: 1,
            have: 0,
            need: 1
        })
    ));

    // Corruption and misrouting fail before sequence state changes.
    let mut corrupt = buffered[reordered_index].as_bytes().to_vec();
    corrupt[60] ^= 1;
    assert!(matches!(
        parties[0].accept_frame(&corrupt),
        Err(EqualityTransportError::MalformedFrame(
            "frame checksum mismatch"
        ))
    ));
    assert!(matches!(
        coordinator.accept_frame(buffered[reordered_index].as_bytes()),
        Err(EqualityTransportError::RecipientMismatch)
    ));

    // A correctly signed frame under the same roster but another public
    // equality nonce is still rejected as cross-session traffic.
    let other_session =
        PartyMpcSession::equality([0x52; 32], N, VALUE_BITS, MODULUS, Duration::from_secs(5))
            .unwrap();
    let mut other_parties = build_parties(
        &other_session,
        &roster,
        &party_seeds,
        0x5253,
        [20, 30, 27],
        [10, 11, 56],
    );
    let cross = next_frame(&mut other_parties[0]);
    assert!(matches!(
        parties[cross.recipient()].accept_frame(cross.as_bytes()),
        Err(EqualityTransportError::SessionMismatch)
    ));

    // Timeout is part of the exact authenticated session, not merely a local
    // process preference: a same-nonce frame from a differently timed session
    // cannot cross the boundary.
    let different_timeout = PartyMpcSession::equality(
        session.nonce(),
        N,
        VALUE_BITS,
        MODULUS,
        Duration::from_secs(6),
    )
    .unwrap();
    let mut differently_timed_parties = build_parties(
        &different_timeout,
        &roster,
        &party_seeds,
        0x5254,
        [20, 30, 27],
        [10, 11, 56],
    );
    let timed_cross = next_frame(&mut differently_timed_parties[0]);
    assert!(matches!(
        parties[timed_cross.recipient()].accept_frame(timed_cross.as_bytes()),
        Err(EqualityTransportError::SessionMismatch)
    ));

    // The ordered transport roster is part of the session identity. Even a
    // frame from an unchanged sender key cannot cross into a session whose
    // other participant key differs.
    let mut changed_party_seeds = party_seeds.clone();
    changed_party_seeds[2] = [0x34; 32];
    let changed_party_public = changed_party_seeds
        .iter()
        .map(|seed| SigningKey::from_bytes(seed).verifying_key().to_bytes())
        .collect();
    let changed_roster = EqualityTransportRoster::new(
        changed_party_public,
        SigningKey::from_bytes(&coordinator_seed)
            .verifying_key()
            .to_bytes(),
    )
    .unwrap();
    let mut changed_roster_parties = build_parties(
        &session,
        &changed_roster,
        &changed_party_seeds,
        0x5354,
        [20, 30, 27],
        [10, 11, 56],
    );
    let changed_roster_frame = next_frame(&mut changed_roster_parties[0]);
    assert!(matches!(
        parties[changed_roster_frame.recipient()].accept_frame(changed_roster_frame.as_bytes()),
        Err(EqualityTransportError::SessionMismatch)
    ));

    // Deliver the buffered burst in canonical order, skipping the one frame
    // already accepted above.
    for (index, frame) in buffered.into_iter().enumerate() {
        if index != first_to_zero {
            parties[frame.recipient()]
                .accept_frame(frame.as_bytes())
                .unwrap();
        }
    }

    let decision = drive_transport(parties, coordinator, &roster);
    assert!(decision.is_equal());
    assert_eq!(decision.session_nonce(), session.nonce());
    assert!(decision.transcript.is_reveal_only(&session));
    assert_eq!(decision.transcript.revealed_equal, 1);
}

#[test]
fn authenticated_equality_transport_reveals_unequal_as_zero() {
    let session =
        PartyMpcSession::equality([0x61; 32], N, VALUE_BITS, MODULUS, Duration::from_secs(5))
            .unwrap();
    let (party_seeds, coordinator_seed, roster) = transport_keys();
    let parties = build_parties(
        &session,
        &roster,
        &party_seeds,
        0x6162,
        [20, 30, 27],
        [10, 11, 57],
    );
    let coordinator = EqualityCoordinatorMachine::new(
        session.clone(),
        roster.clone(),
        SigningKey::from_bytes(&coordinator_seed),
    )
    .unwrap();

    let decision = drive_transport(parties, coordinator, &roster);
    assert!(!decision.is_equal());
    assert_eq!(decision.session_nonce(), session.nonce());
    assert!(decision.transcript.is_reveal_only(&session));
    assert_eq!(decision.transcript.revealed_equal, 0);
}
