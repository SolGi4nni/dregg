//! THE DARK ORACLE PIT — a confidential quadratic prediction market under a COLLECTIVE KEY, NO SINGLE VIEWER.
//!
//! `oracle_pit_pricing` prices under a single key (one party could decrypt the price). This is the TIER-0
//! form: positions are encrypted to an n-of-n COLLECTIVE key, the quadratic cost `q₁²+q₁q₂+q₂²` is priced
//! HOMOMORPHICALLY under a collective RELIN key (the n-of-n multiparty relinearization ceremony), and the
//! price is revealed ONLY by a THRESHOLD combine of all n parties. No single party — and no `n−1` coalition —
//! can open the price or any position. The market runs house-blind, with a real ct×ct multiply under the
//! collective key (the harder case than additive netting — it needs threshold relin, which exists).
//!
//! Uses the FROZEN threshold + threshold::relin APIs (the `threshold_relin` test's exact ceremony). This is
//! `metatheory/Market/OraclePitQuadratic` + `DarkBazaarCollectiveOpening` + `DarkBazaarQuorumNecessity` made
//! to RUN together: quadratic pricing under the no-single-viewer collective decrypt.

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

fn encrypt_to_collective(
    pk: &CollectivePublicKey,
    params: &BfvParams,
    v: u64,
) -> fhe::bfv::Ciphertext {
    let pt = Plaintext::try_encode(&[v], Encoding::simd(), params.arc()).expect("encode");
    let mut rng = rand_09::rng();
    pk.pk
        .try_encrypt(&pt, &mut rng)
        .expect("collective encrypt")
}

/// THE VISION CORE: a confidential quadratic market prices hidden positions under an n-of-n collective key,
/// and the price is revealed ONLY by the full quorum — an `n−1` coalition is refused. The house sees no
/// position and no single party can open the price; only the whole committee together reveals it.
#[test]
fn dark_oracle_pit_prices_under_collective_key_no_single_viewer() {
    const N: usize = 3;
    let params = BfvParams::fold_set();
    let t = params.plaintext_modulus();

    // 1. n-of-n collective keygen + the n-of-n multiparty RELIN ceremony (needed for the ct×ct multiply).
    let (keygen, collective, parties) = collective_keygen(N, &params);
    let relin_session = RelinKeySession::from_public_entropy(
        &keygen,
        &collective,
        [0x0e; 32],
        Duration::from_secs(90),
    )
    .expect("relin session");
    let relin = generate_relinearization_key(&relin_session, &params, &collective, &parties)
        .expect("n-of-n relin ceremony");
    let engine = MulEngine::new(&relin, params.arc()).expect("collective-key mul engine");

    // 2. Encrypt the hidden positions to the collective key.
    let (q1, q2) = (7u64, 11u64);
    let cq1 = encrypt_to_collective(&collective, &params, q1);
    let cq2 = encrypt_to_collective(&collective, &params, q2);

    // 3. Price the quadratic cost q₁² + q₁·q₂ + q₂² = product_sum([q₁,q₁,q₂], [q₁,q₂,q₂]) under the collective key.
    let lhs = [
        BoundedCiphertext::new(cq1.clone(), q1),
        BoundedCiphertext::new(cq1.clone(), q1),
        BoundedCiphertext::new(cq2.clone(), q2),
    ];
    let rhs = [
        BoundedCiphertext::new(cq1.clone(), q1),
        BoundedCiphertext::new(cq2.clone(), q2),
        BoundedCiphertext::new(cq2.clone(), q2),
    ];
    let priced = engine
        .product_sum(&lhs, &rhs)
        .expect("dark quadratic price");
    let priced_lean = LeanCiphertext::from_fhe_bytes(
        &priced.ct.to_bytes(),
        params.moduli(),
        params.degree(),
        priced.plain_bound,
    )
    .expect("priced ciphertext crosses the Lean boundary");

    // 4. THRESHOLD DECRYPT — every party partial-decrypts; only the full quorum's combine reveals the price.
    let shares = parties
        .iter()
        .map(|pty| {
            pty.partial_decrypt(&priced_lean, MIN_SMUDGE_BITS)
                .expect("price share")
        })
        .collect::<Vec<_>>();
    // THE NO-SINGLE-VIEWER TOOTH: an n−1 share set cannot open the price.
    assert!(
        combine(&shares[..N - 1], &params).is_err(),
        "an n−1 coalition opened the dark price — no-single-viewer broke"
    );
    let opened = combine(&shares, &params).expect("full-quorum price opening");

    // 5. The revealed price is EXACTLY the plaintext quadratic — positions never left the ciphertext domain.
    let want = q1 * q1 + q1 * q2 + q2 * q2;
    assert!(want < t, "test setup: quadratic must stay below t");
    assert_eq!(
        opened[0], want,
        "dark Oracle Pit price != plaintext quadratic (no-single-viewer pricing)"
    );
}
