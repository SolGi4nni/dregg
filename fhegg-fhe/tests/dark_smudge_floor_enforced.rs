//! THE SMUDGE FLOOR IS ENFORCED — no party can create a leaky (under-smudged) decrypt share.
//!
//! The no-single-viewer halls' hiding rests on SMUDGING: each partial decrypt adds noise `eᵢ ∈ [−2^b, 2^b]`
//! with `b ≥ MIN_SMUDGE_BITS`, so an `n−1` coalition learns nothing (`metatheory/Bfv/Smudging.lean`, the
//! Lean-pinned floor, instantiated by `DarkBazaarCollectiveOpening`). This is the RUNNING witness that the
//! floor is enforced at share CREATION: a malicious/broken party that tries to under-smudge (which would leak
//! the secret) is REFUSED by `partial_decrypt`, and one that over-smudges (which would break decryption) is
//! refused too. The security parameter cannot be silently weakened.

use std::time::Duration;

use fhe::bfv::{Encoding, Plaintext};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize};

use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdError,
    ThresholdParty, MIN_SMUDGE_BITS,
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

fn collective_ct(pk: &CollectivePublicKey, params: &BfvParams, v: u64) -> LeanCiphertext {
    let pt = Plaintext::try_encode(&[v], Encoding::simd(), params.arc()).expect("encode");
    let mut rng = rand_09::rng();
    let ct = pk
        .pk
        .try_encrypt(&pt, &mut rng)
        .expect("collective encrypt");
    LeanCiphertext::from_fhe_bytes(&ct.to_bytes(), params.moduli(), params.degree(), v)
        .expect("parse")
}

/// THE LOAD-BEARING TOOTH: the Lean-pinned smudge floor is enforced at share creation. An under-smudged share
/// (which would leak the collective secret to an n−1 coalition) is REFUSED; a valid one succeeds; an
/// over-smudged one (which would break the combined decrypt) is refused. The hiding parameter is not
/// silently weakenable — the running witness of `Bfv.Smudging`'s floor.
#[test]
fn smudge_floor_is_enforced_at_share_creation() {
    const N: usize = 3;
    let params = BfvParams::fold_set();
    let (collective, parties) = collective_keygen(N, &params);
    let ct = collective_ct(&collective, &params, 42);
    let party = &parties[0];

    // UNDER-SMUDGE (leaky) is REFUSED: one bit below the floor cannot make a share.
    let under = party.partial_decrypt(&ct, MIN_SMUDGE_BITS - 1);
    assert!(
        matches!(under, Err(ThresholdError::SmudgeTooSmall)),
        "an under-smudged (leaky) share was allowed — the hiding floor is not enforced: {under:?}"
    );

    // A VALID share at exactly the floor succeeds.
    assert!(
        party.partial_decrypt(&ct, MIN_SMUDGE_BITS).is_ok(),
        "a floor-smudged share was refused — the valid path broke"
    );

    // OVER-SMUDGE (would swamp the message) is REFUSED too — the budget is two-sided.
    let over = party.partial_decrypt(&ct, MIN_SMUDGE_BITS + 200);
    assert!(
        matches!(over, Err(ThresholdError::SmudgeTooLarge)),
        "an over-smudged share was allowed — the decrypt-budget ceiling is not enforced: {over:?}"
    );
}
