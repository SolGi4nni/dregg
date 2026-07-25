//! THE DARK NETTING VAULT — multilateral netting under a COLLECTIVE KEY, NO SINGLE VIEWER.
//!
//! The `netting_vault_running` test computes nets under a single key (one party could decrypt). This is the
//! TIER-0 form: the obligation matrix is encrypted to an n-of-n COLLECTIVE key (`s = Σ sᵢ`, never assembled),
//! each party's signed net is computed HOMOMORPHICALLY, and the net is revealed only by a THRESHOLD combine of
//! all n parties' partial decrypts. No single party — and no `n−1` coalition — can open any obligation or any
//! net; the vault is house-blind. Uses the FROZEN threshold API (`KeygenSession`/`ThresholdParty`/`combine`)
//! that the e2e private-derivative test codes against, and `convex_step`'s signed arithmetic for the net.
//!
//! This is `metatheory/Market/{NettingVault,DarkBazaarCollectiveOpening,DarkBazaarQuorumNecessity}` made to
//! RUN together: netting (conservation + compression) under the collective decrypt (sound + n-of-n necessity:
//! any `n−1` cannot open — asserted below). The Netting Vault at full Dark-Bazaar privacy.

use fhe::bfv::{Encoding, Plaintext};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize};

use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::convex_step::{signed_add, signed_neg, SignedCt};
use fhegg_fhe::threshold::{self, BfvParams, CollectivePublicKey};

const QUORUM_N: usize = 4;

fn params() -> BfvParams {
    BfvParams::fold_set()
}

/// Encrypt a single value into all SIMD slots under the COLLECTIVE public key.
fn encrypt_to_collective(pk: &CollectivePublicKey, params: &BfvParams, v: u64) -> LeanCiphertext {
    let slots = vec![v; params.degree()];
    let pt =
        Plaintext::try_encode(&slots, Encoding::simd(), params.arc()).expect("collective encode");
    let mut rng = rand_09::rng();
    let ct = pk
        .pk
        .try_encrypt(&pt, &mut rng)
        .expect("collective-key encrypt");
    LeanCiphertext::from_fhe_bytes(&ct.to_bytes(), params.moduli(), params.degree(), v)
        .expect("parse into Lean-first representation")
}

/// THE VISION CORE, RUNNING: a guild's multilateral net computed under an n-of-n collective key and revealed
/// ONLY by the full quorum. Each party's signed net is correct, conservation holds, and — the no-single-viewer
/// tooth — an `n−1` share set is REFUSED by `combine`. No obligation or net is ever openable by fewer than n.
#[test]
fn dark_netting_vault_no_single_viewer() {
    let params = params();
    let t = params.plaintext_modulus();

    // 1. n-of-n collective keygen (the collective secret `s = Σ sᵢ` is never assembled).
    let session = threshold::KeygenSession::random(QUORUM_N).expect("keygen session");
    let mut coordinator = threshold::KeygenCoordinator::new(session.clone(), params.clone());
    let parties = (0..QUORUM_N)
        .map(|p| {
            let (state, contribution) =
                threshold::ThresholdParty::join(&session, p, &params).expect("party keygen");
            coordinator
                .accept(contribution)
                .expect("public contribution");
            state
        })
        .collect::<Vec<_>>();
    let cpk = coordinator.finish().expect("collective public key");

    // 2. A hidden guild obligation matrix (g[i][j] = party i owes j; diagonal 0). Small, deterministic.
    let n = QUORUM_N;
    let max_g = 19i64;
    let g: Vec<Vec<u64>> = (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    if i == j {
                        0
                    } else {
                        ((i * 7 + j * 3 + 2) % 20) as u64
                    }
                })
                .collect()
        })
        .collect();
    let enc = |v: u64| {
        SignedCt::new(encrypt_to_collective(&cpk, &params, v), 0, max_g, t).expect("signed window")
    };

    // 3. Each party's SIGNED net = Σ owed − Σ owing, computed homomorphically under the collective key.
    let mut nets = Vec::new();
    for i in 0..n {
        let owed = (0..n)
            .filter(|&j| j != i)
            .map(|j| enc(g[i][j]))
            .reduce(|a, b| signed_add(&a, &b, t).expect("owed add"))
            .expect("owed");
        let owing_neg = (0..n)
            .filter(|&j| j != i)
            .map(|j| signed_neg(&enc(g[j][i]), t).expect("neg"))
            .reduce(|a, b| signed_add(&a, &b, t).expect("owing add"))
            .expect("owing");
        let net = signed_add(&owed, &owing_neg, t).expect("net");

        // 4. THRESHOLD DECRYPT — every party partial-decrypts; only the full quorum's combine reveals the net.
        let shares = parties
            .iter()
            .map(|pty| {
                pty.partial_decrypt(net.ciphertext(), threshold::MIN_SMUDGE_BITS)
                    .expect("share")
            })
            .collect::<Vec<_>>();
        // THE NO-SINGLE-VIEWER TOOTH: an n−1 share set is REFUSED (any coalition below n cannot open the net).
        assert!(
            threshold::combine(&shares[..n - 1], &params).is_err(),
            "an n−1 coalition decrypted the net — no-single-viewer broke"
        );
        let slots = threshold::combine(&shares, &params).expect("full-quorum combine");
        let raw = slots[0];
        let net_val = if raw > t / 2 {
            raw as i64 - t as i64
        } else {
            raw as i64
        };

        // validate vs the plaintext net (centered).
        let owed_p: i64 = (0..n).map(|j| g[i][j] as i64).sum();
        let owing_p: i64 = (0..n).map(|j| g[j][i] as i64).sum();
        assert_eq!(net_val, owed_p - owing_p, "dark net wrong for party {i}");
        nets.push(net_val);
    }

    // 5. CONSERVATION at Tier-0: the quorum-revealed nets sum to zero.
    assert_eq!(
        nets.iter().sum::<i64>(),
        0,
        "dark netting does not conserve"
    );
}
