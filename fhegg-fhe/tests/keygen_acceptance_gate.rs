//! Build 5 Tier-0 (roadmap FHEGG-MALICE-ROADMAP-2026-07-25): the collective-key acceptance gate.
//!
//! `KeygenCoordinator::finish` aggregates party contributions but verifies only `c1==CRP` + `level==0`, NOT
//! the well-formedness of each `c0_i`. A malformed/biased contribution therefore silently corrupts the
//! collective key (surfaces only as garbage at encrypt-time, unattributably). `collective_key_acceptance_gate`
//! catches that fail-closed: fresh random trial values must encrypt-then-threshold-decrypt back to themselves,
//! or the key is refused. Honest-coordinator DETECTION (not attribution — that is Build 5's per-share ZK
//! proof); the keygen analog of the relin acceptance gate.

use fhegg_fhe::threshold::{
    collective_key_acceptance_gate, BfvParams, CollectivePublicKey, KeygenCoordinator,
    KeygenSession, ThresholdError, ThresholdParty,
};

fn collective_keygen(n: usize, params: &BfvParams) -> (CollectivePublicKey, Vec<ThresholdParty>) {
    let session = KeygenSession::random(n).expect("keygen session");
    let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
    let parties = (0..n)
        .map(|p| {
            let (party, contribution) =
                ThresholdParty::join(&session, p, params).expect("party keygen");
            coordinator
                .accept(contribution)
                .expect("public contribution");
            party
        })
        .collect::<Vec<_>>();
    (
        coordinator.finish().expect("collective public key"),
        parties,
    )
}

/// The gate ACCEPTS an honest collective key: every fresh trial value encrypts then decrypts back to itself
/// under the full quorum.
#[test]
fn acceptance_gate_accepts_an_honest_collective_key() {
    const N: usize = 3;
    let params = BfvParams::fold_set();
    let (collective, parties) = collective_keygen(N, &params);
    collective_key_acceptance_gate(&collective, &params, &parties, 4)
        .expect("an honest collective key must pass the acceptance gate");
}

/// THE GATE BITES: a collective key that does NOT match its quorum (a stand-in for a corrupt/malformed-share
/// key) is REFUSED with `AcceptanceFailed`. Here the key is from keygen A but gated against keygen B's parties
/// — the trial values encrypt to A's key but B's shares cannot decrypt them, so the round-trip mismatches and
/// the key fails closed. A key whose quorum cannot decrypt what it encrypts is rejected, not silently used.
#[test]
fn acceptance_gate_rejects_a_key_that_does_not_match_its_quorum() {
    const N: usize = 3;
    let params = BfvParams::fold_set();
    let (collective_a, parties_a) = collective_keygen(N, &params);
    let (_collective_b, parties_b) = collective_keygen(N, &params);

    // Sanity: A's key passes against its OWN quorum.
    collective_key_acceptance_gate(&collective_a, &params, &parties_a, 4)
        .expect("collective_a passes against its own quorum");

    // Against B's quorum, A's ciphertexts cannot round-trip.
    let verdict = collective_key_acceptance_gate(&collective_a, &params, &parties_b, 4);
    assert!(
        matches!(verdict, Err(ThresholdError::AcceptanceFailed { .. })),
        "a collective key mismatched to its quorum must be refused with AcceptanceFailed, got {verdict:?}"
    );
}
