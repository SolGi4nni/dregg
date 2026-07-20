//! Party-owned scalar equality: mod-t shares in, one decision bit out.
//!
//! This is the decision organ used by privacy boundaries that must distinguish
//! `secret == public_target` without opening the secret on the refusal path.

use std::thread;
use std::time::Duration;

use fhegg_fhe::mpc_party::{
    local_channels, run_party_equality, simulate_decision_transcript, trusted_dealer_triples,
    DistributedDecisionRun, PartyArithmeticInput, PartyEqualityInput, PartyMpcError,
    PartyMpcSession,
};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

const N: usize = 3;
const T: u64 = 65_537;
const BITS: usize = 16;

fn share_mod_t(value: u64, rng: &mut StdRng) -> Vec<u64> {
    let mut shares = (0..N - 1).map(|_| rng.gen_range(0..T)).collect::<Vec<_>>();
    let partial = shares.iter().fold(0u64, |acc, &share| (acc + share) % T);
    shares.push((value + T - partial) % T);
    shares
}

fn decide(left: u64, right: u64, seed: u64) -> DistributedDecisionRun {
    assert!(left < 1 << BITS && right < 1 << BITS);
    let session = PartyMpcSession::equality([seed as u8; 32], N, BITS, T, Duration::from_secs(2))
        .expect("valid scalar-decision session");
    let mut rng = StdRng::seed_from_u64(seed);
    let left_shares = share_mod_t(left, &mut rng);
    let right_shares = share_mod_t(right, &mut rng);
    let inputs = (0..N)
        .map(|party| {
            let mut party_rng = StdRng::seed_from_u64(seed ^ 0x5000_0000 ^ party as u64);
            PartyEqualityInput::new(
                &session,
                party,
                left_shares[party],
                right_shares[party],
                &mut party_rng,
            )
            .expect("one party owns only its two local residue shares")
        })
        .collect::<Vec<_>>();
    let preprocessing = trusted_dealer_triples(&session, &mut rng)
        .expect("trusted preprocessing sees public shape only");
    let (coordinator, endpoints) = local_channels(&session);
    let parties = inputs
        .into_iter()
        .zip(preprocessing)
        .zip(endpoints)
        .map(|((input, triples), endpoint)| {
            thread::spawn(move || run_party_equality(input, triples, endpoint))
        })
        .collect::<Vec<_>>();
    let run = coordinator
        .coordinate_equality(&session)
        .expect("full equality quorum");
    assert!(run.transcript.is_reveal_only(&session));
    for party in parties {
        party
            .join()
            .expect("party thread exits")
            .expect("party circuit completes");
    }
    run
}

#[test]
fn equality_reveals_one_bit_and_refuses_a_wrong_value() {
    let equal = decide(42_424, 42_424, 0xe011_a11a);
    assert!(equal.is_equal());
    assert_eq!(equal.transcript.revealed_equal, 1);

    let unequal = decide(42_423, 42_424, 0xe011_a11b);
    assert!(!unequal.is_equal());
    assert_eq!(unequal.transcript.revealed_equal, 0);

    // The public transcript schema is simulatable from the one intended bit
    // and public shape; it has no operand/residue field to inspect.
    let session =
        PartyMpcSession::equality([0x51; 32], N, BITS, T, Duration::from_secs(1)).expect("session");
    let mut rng = StdRng::seed_from_u64(0x5151);
    let simulated = simulate_decision_transcript(false, &session, &mut rng).expect("simulator");
    assert!(simulated.is_reveal_only(&session));
    assert_eq!(simulated.masked.len(), unequal.transcript.masked.len());
}

#[test]
fn crossing_and_equality_inputs_cannot_be_confused() {
    let equality = PartyMpcSession::equality([0x52; 32], N, BITS, T, Duration::from_secs(1))
        .expect("equality session");
    let crossing = PartyMpcSession::new([0x53; 32], N, 1, BITS, T, Duration::from_secs(1))
        .expect("crossing session");
    let mut rng = StdRng::seed_from_u64(0x5253);
    assert!(matches!(
        PartyArithmeticInput::new(&equality, 0, &[1], &[1], &mut rng),
        Err(PartyMpcError::SessionMismatch)
    ));
    assert!(matches!(
        PartyEqualityInput::new(&crossing, 0, 1, 1, &mut rng),
        Err(PartyMpcError::SessionMismatch)
    ));
}

#[test]
fn reveal_only_decision_transcript_has_a_strict_bounded_wire() {
    let session =
        PartyMpcSession::equality([0x54; 32], N, BITS, T, Duration::from_secs(1)).expect("session");
    let mut rng = StdRng::seed_from_u64(0x5454);
    let transcript =
        simulate_decision_transcript(true, &session, &mut rng).expect("public simulator");
    let wire = transcript
        .to_wire_bytes()
        .expect("canonical transcript wire");
    assert_eq!(&wire[..8], b"FHDTR001");
    let decoded = fhegg_fhe::mpc_party::DecisionTranscript::from_wire_bytes(&wire)
        .expect("strict transcript decode");
    assert_eq!(decoded, transcript);
    assert!(decoded.is_reveal_only(&session));

    let mut retired = wire.clone();
    retired[..8].copy_from_slice(b"FHDTR000");
    assert!(matches!(
        fhegg_fhe::mpc_party::DecisionTranscript::from_wire_bytes(&retired),
        Err(PartyMpcError::MalformedTranscriptWire)
    ));

    let mut non_bit = wire.clone();
    // magic + count + first opening's gate index => its d bit
    non_bit[8 + 8 + 8] = 2;
    assert!(matches!(
        fhegg_fhe::mpc_party::DecisionTranscript::from_wire_bytes(&non_bit),
        Err(PartyMpcError::MalformedTranscriptWire)
    ));

    let mut allocation_attack = wire.clone();
    allocation_attack[8..16].copy_from_slice(&u64::MAX.to_be_bytes());
    assert!(matches!(
        fhegg_fhe::mpc_party::DecisionTranscript::from_wire_bytes(&allocation_attack),
        Err(PartyMpcError::MalformedTranscriptWire | PartyMpcError::ArithmeticOverflow)
    ));

    let mut trailing = wire.clone();
    trailing.push(0);
    assert!(matches!(
        fhegg_fhe::mpc_party::DecisionTranscript::from_wire_bytes(&trailing),
        Err(PartyMpcError::MalformedTranscriptWire)
    ));

    let mut inconsistent = transcript;
    inconsistent.and_gates += 1;
    assert!(matches!(
        inconsistent.to_wire_bytes(),
        Err(PartyMpcError::MalformedTranscriptWire)
    ));
}
