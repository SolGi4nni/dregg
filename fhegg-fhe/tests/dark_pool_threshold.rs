//! THE DARK POOL at TIER-0 — the constant-product invariant verified under a COLLECTIVE KEY, no single viewer.
//!
//! `dark_pool_invariant` verifies swaps under a single key. This is the house-blind form: the reserves are
//! encrypted to an n-of-n COLLECTIVE key, the swap invariant `(x+dx)(y−dy) = x·y` is checked HOMOMORPHICALLY
//! under a collective RELIN key, and the "invariant holds?" bit is revealed ONLY by a THRESHOLD combine of all
//! n parties. No single party — nor any n−1 coalition — can open the reserves or even the invariant result;
//! yet an unfair swap is still provably caught. Provably-fair AND provably-blind liquidity, running.
//!
//! Uses the FROZEN threshold + threshold::relin APIs (the `threshold_relin` ceremony); a minimal standalone
//! witness complementing codex's full `dark_amm_dkg`.

use std::time::Duration;

use fhe::bfv::{Encoding, Plaintext};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize};

use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::bfv_mul::{BoundedCiphertext, MulEngine};
use fhegg_fhe::threshold::relin::{generate_relinearization_key, RelinKeySession};
use fhegg_fhe::threshold::{
    combine, BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
    MIN_SMUDGE_BITS,
};

fn collective_keygen(
    n: usize,
    params: &BfvParams,
) -> (KeygenSession, CollectivePublicKey, Vec<ThresholdParty>) {
    let session = KeygenSession::random(n).expect("keygen session");
    let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
    let mut parties = Vec::with_capacity(n);
    for party_index in 0..n {
        let (party, contribution) =
            ThresholdParty::join(&session, party_index, params).expect("party keygen");
        coordinator
            .accept(contribution)
            .expect("public contribution");
        parties.push(party);
    }
    let collective = coordinator.finish().expect("collective public key");
    (session, collective, parties)
}

fn enc(pk: &CollectivePublicKey, params: &BfvParams, v: u64) -> fhe::bfv::Ciphertext {
    let pt = Plaintext::try_encode(&[v], Encoding::simd(), params.arc()).expect("encode");
    let mut rng = rand_09::rng();
    pk.pk
        .try_encrypt(&pt, &mut rng)
        .expect("collective encrypt")
}

fn pt(params: &BfvParams, v: u64) -> Plaintext {
    Plaintext::try_encode(&[v], Encoding::simd(), params.arc()).expect("pt encode")
}

/// The threshold-opened invariant residue `(x+dx)(y−dy) − x·y`, computed under the collective key and revealed
/// only by the full quorum. Returns the decrypted difference (0 iff the swap preserves the constant product).
/// Also asserts the no-single-viewer tooth: an n−1 share set is refused.
fn dark_invariant_diff(
    n: usize,
    params: &BfvParams,
    collective: &CollectivePublicKey,
    parties: &[ThresholdParty],
    engine: &MulEngine,
    x: u64,
    y: u64,
    dx: u64,
    dy: u64,
) -> u64 {
    let cx = enc(collective, params, x);
    let cy = enc(collective, params, y);
    let old = engine
        .multiply(
            &BoundedCiphertext::new(cx.clone(), x),
            &BoundedCiphertext::new(cy.clone(), y),
        )
        .expect("x*y");
    let new_x = &cx + &pt(params, dx);
    let new_y = &cy - &pt(params, dy);
    let new = engine
        .multiply(
            &BoundedCiphertext::new(new_x, x + dx),
            &BoundedCiphertext::new(new_y, y - dy),
        )
        .expect("(x+dx)(y-dy)");
    let diff = &new.ct - &old.ct; // homomorphic invariant difference; reserves never opened
    let diff_lean = LeanCiphertext::from_fhe_bytes(
        &diff.to_bytes(),
        params.moduli(),
        params.degree(),
        new.plain_bound,
    )
    .expect("diff crosses the Lean boundary");
    let shares = parties
        .iter()
        .map(|p| {
            p.partial_decrypt(&diff_lean, MIN_SMUDGE_BITS)
                .expect("share")
        })
        .collect::<Vec<_>>();
    assert!(
        combine(&shares[..n - 1], params).is_err(),
        "an n−1 coalition opened the dark invariant — no-single-viewer broke"
    );
    combine(&shares, params).expect("full-quorum invariant opening")[0]
}

/// A FAIR swap under the collective key preserves `x·y`: the threshold-opened invariant difference is 0. The
/// reserves are never opened and no single party can even see the invariant result — only the full quorum.
#[test]
fn dark_pool_fair_swap_verifies_under_collective_key() {
    const N: usize = 3;
    let params = BfvParams::fold_set();
    let (keygen, collective, parties) = collective_keygen(N, &params);
    let session = RelinKeySession::from_public_entropy(
        &keygen,
        &collective,
        [0xda; 32],
        Duration::from_secs(90),
    )
    .expect("relin session");
    let relin =
        generate_relinearization_key(&session, &params, &collective, &parties).expect("relin");
    let engine = MulEngine::new(&relin, params.arc()).expect("engine");
    // fair: x=10,y=20; dx=10 (x+dx=20), dy=10 (y-dy=10) -> (20)(10)=200=x*y.
    let diff = dark_invariant_diff(N, &params, &collective, &parties, &engine, 10, 20, 10, 10);
    assert_eq!(
        diff, 0,
        "fair swap failed the dark constant-product invariant"
    );
}

/// An UNFAIR swap is CAUGHT even house-blind: the threshold-opened invariant difference is nonzero, so the
/// pool can refuse the skim without ever opening the reserves or letting any single party see the result.
#[test]
fn dark_pool_unfair_swap_caught_under_collective_key() {
    const N: usize = 3;
    let params = BfvParams::fold_set();
    let (keygen, collective, parties) = collective_keygen(N, &params);
    let session = RelinKeySession::from_public_entropy(
        &keygen,
        &collective,
        [0xba; 32],
        Duration::from_secs(90),
    )
    .expect("relin session");
    let relin =
        generate_relinearization_key(&session, &params, &collective, &parties).expect("relin");
    let engine = MulEngine::new(&relin, params.arc()).expect("engine");
    // unfair: dy=9 instead of 10 -> (20)(11)=220 != 200.
    let diff = dark_invariant_diff(N, &params, &collective, &parties, &engine, 10, 20, 10, 9);
    assert_ne!(
        diff, 0,
        "an unfair swap passed the dark invariant (the guard did not bite house-blind)"
    );
}
