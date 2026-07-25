//! SHARE BINDING — a decrypt share for a DIFFERENT ciphertext cannot open the target.
//!
//! The third load-bearing tooth of the no-single-viewer decrypt (alongside n−1 refusal and the smudge floor):
//! a partial-decrypt share binds the SPECIFIC ciphertext it was made for. A malicious/broken party that
//! substitutes a share made for a different ciphertext cannot make the quorum open the target to the intended
//! value — the substitution is rejected or yields the wrong result, never the honest one. This is the running
//! witness of `metatheory/Market/DarkBazaarShareValidity.unvalidated_shift_breaks_opening`: an unvalidated
//! (here: wrong-ciphertext) share moves the message, so it cannot pass as an honest opening.

use fhe::bfv::{Encoding, Plaintext};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize};

use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::threshold::{
    combine, BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
    MIN_SMUDGE_BITS,
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

/// THE LOAD-BEARING TOOTH: shares bind their ciphertext. All-honest shares for `ct_a` open to `a`; swapping in
/// one party's share made for a DIFFERENT ciphertext `ct_b` cannot open `ct_a` to `a` — the quorum either
/// refuses the mismatched set or yields a wrong value, never the honest one. A wrong-ciphertext share cannot
/// masquerade as an honest opening.
#[test]
fn a_share_for_a_different_ciphertext_cannot_open_the_target() {
    const N: usize = 3;
    let params = BfvParams::fold_set();
    let (collective, parties) = collective_keygen(N, &params);

    let (a, b) = (42u64, 99u64);
    let ct_a = collective_ct(&collective, &params, a);
    let ct_b = collective_ct(&collective, &params, b);

    // Honest baseline: all shares for ct_a open to a.
    let honest = parties
        .iter()
        .map(|p| {
            p.partial_decrypt(&ct_a, MIN_SMUDGE_BITS)
                .expect("honest share")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        combine(&honest, &params).expect("honest combine")[0],
        a,
        "honest all-ct_a quorum failed to open to a"
    );

    // Malicious substitution: party 0 submits a share made for ct_b instead of ct_a.
    let mut tampered = honest.clone();
    tampered[0] = parties[0]
        .partial_decrypt(&ct_b, MIN_SMUDGE_BITS)
        .expect("wrong-ct share");
    match combine(&tampered, &params) {
        Err(_) => { /* rejected the mismatched set — ideal */ }
        Ok(opened) => assert_ne!(
            opened[0], a,
            "a wrong-ciphertext share opened ct_a to the honest value a — share binding broke"
        ),
    }
}
