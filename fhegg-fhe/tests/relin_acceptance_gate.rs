//! Build 4 (roadmap FHEGG-MALICE-ROADMAP-2026-07-25): the mandatory relin acceptance gate.
//!
//! Aggregation of the n-of-n relin shares checks no well-formedness proof, so a malformed party contribution
//! can silently corrupt the collective relin key (the fault surfaces only as garbage at multiply-time,
//! unattributably). `relin_acceptance_gate` catches that fail-closed: fresh random trial products must decrypt
//! to the exact plaintext product under the full quorum, or the key is refused. Honest-coordinator DETECTION
//! (not attribution — that is Build 6's decrypt-share certificate); a real Tier-0 malicious-security stopgap.

use std::time::Duration;

use fhegg_fhe::threshold::relin::{
    generate_relinearization_key, generate_relinearization_key_verified, relin_acceptance_gate,
    RelinError, RelinKeySession,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};

fn collective_keygen(
    n: usize,
    params: &BfvParams,
) -> (KeygenSession, CollectivePublicKey, Vec<ThresholdParty>) {
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
        session,
        coordinator.finish().expect("collective public key"),
        parties,
    )
}

fn relin_for(
    seed: [u8; 32],
    params: &BfvParams,
    keygen: &KeygenSession,
    collective: &CollectivePublicKey,
    parties: &[ThresholdParty],
) -> fhe::bfv::RelinearizationKey {
    let session =
        RelinKeySession::from_public_entropy(keygen, collective, seed, Duration::from_secs(90))
            .expect("relin session");
    generate_relinearization_key(&session, params, collective, parties).expect("relin ceremony")
}

/// The gate ACCEPTS an honest relin key: every fresh trial product decrypts to the exact plaintext product
/// under the quorum. And `_verified` returns the key.
#[test]
fn acceptance_gate_accepts_an_honest_relin_key() {
    const N: usize = 3;
    let params = BfvParams::fold_set();
    let (keygen, collective, parties) = collective_keygen(N, &params);
    let relin = relin_for([0xa1; 32], &params, &keygen, &collective, &parties);

    relin_acceptance_gate(&relin, &params, &collective, &parties, 8)
        .expect("honest relin key must pass the acceptance gate");

    let session = RelinKeySession::from_public_entropy(
        &keygen,
        &collective,
        [0xa2; 32],
        Duration::from_secs(90),
    )
    .expect("relin session");
    generate_relinearization_key_verified(&session, &params, &collective, &parties)
        .expect("generate + gate must succeed on an honest ceremony");
}

/// THE GATE BITES: a relin key that does NOT match its quorum (a stand-in for a corrupt/malformed-share key)
/// is REFUSED with `AcceptanceFailed`. Here the key is generated for collective A but gated against a
/// different collective B's quorum — the trial products decrypt to garbage, so the key fails closed and is
/// never cached. This is the malicious-corruption analog: a key that cannot correctly multiply-and-decrypt
/// under the quorum it claims is rejected, not silently used.
#[test]
fn acceptance_gate_rejects_a_key_that_does_not_match_its_quorum() {
    const N: usize = 3;
    let params = BfvParams::fold_set();
    let (keygen_a, collective_a, parties_a) = collective_keygen(N, &params);
    let (keygen_b, collective_b, parties_b) = collective_keygen(N, &params);

    // A real, honest relin key for collective A.
    let relin_a = relin_for([0xb1; 32], &params, &keygen_a, &collective_a, &parties_a);
    // Sanity: it passes against its OWN quorum.
    relin_acceptance_gate(&relin_a, &params, &collective_a, &parties_a, 8)
        .expect("relin_a passes against its own quorum");

    // But against collective B's quorum, the trial products cannot decrypt to the plaintext product.
    let verdict = relin_acceptance_gate(&relin_a, &params, &collective_b, &parties_b, 8);
    assert!(
        matches!(verdict, Err(RelinError::AcceptanceFailed { .. })),
        "a relin key mismatched to its quorum must be refused with AcceptanceFailed, got {verdict:?}"
    );
    let _ = keygen_b;
}
