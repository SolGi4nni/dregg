//! THE NETTING VAULT — a WORKING multilateral netting over a HIDDEN obligation matrix.
//!
//! `metatheory/Market/NettingVault.lean` PROVES netting conserves (`net_conserves`) and compresses
//! (`symmetric_obligations_net_zero`). This is the running artifact: it encrypts a bilateral obligation
//! matrix `g` (`g[i][j]` = party `i` owes `j`) with REAL fhe.rs, computes each party's NET position
//! `net_i = (Σ_j g[i][j]) − (Σ_j g[j][i])` HOMOMORPHICALLY (fhe.rs ciphertext add/sub), and decrypts ONLY the
//! net. The individual obligations are ciphertexts that are never opened — only the irreducible net crosses
//! the reveal boundary. If the netting is wrong, fhe.rs decrypts the wrong net and the test is RED.
//!
//! The Netting Vault is a FRONTIER hall in `THE-DARK-BAZAAR.md` (hidden guild obligations, revealing only the
//! final net). It is the ADDITIVE hall — pure ciphertext add/sub, no multiply, no bootstrap — so it needs no
//! GPU and runs at full speed on the deployed BFV params.

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, SecretKey};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter};
use rand_09::rngs::StdRng;
use rand_09::SeedableRng;
use std::sync::Arc;

use fhegg_fhe::additive::pick_params;

struct Fixture {
    params: Arc<BfvParameters>,
    sk: SecretKey,
    pk: PublicKey,
    rng: StdRng,
    t: u64,
}

fn fixture(seed: u64) -> Fixture {
    let params = pick_params(20);
    let t = params.plaintext();
    let mut rng = StdRng::seed_from_u64(seed);
    let sk = SecretKey::random(&params, &mut rng);
    let pk = PublicKey::new(&sk, &mut rng);
    Fixture {
        params,
        sk,
        pk,
        rng,
        t,
    }
}

fn encrypt(fx: &mut Fixture, v: u64) -> Ciphertext {
    let pt = Plaintext::try_encode(&[v], Encoding::simd(), &fx.params).expect("simd encode");
    fx.pk.try_encrypt(&pt, &mut fx.rng).expect("pk encrypt")
}

fn decrypt(fx: &Fixture, ct: &Ciphertext) -> u64 {
    let pt = fx.sk.try_decrypt(ct).expect("fhe.rs decrypt");
    Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("simd decode")[0]
}

/// The plaintext net position of party `i` over the obligation matrix, as a residue mod `t` (a negative net
/// `−x` is `t − x`, the centered BFV encoding). This is the ONLY value the vault ever reveals.
fn plaintext_net_mod_t(g: &[[i64; 3]; 3], i: usize, t: u64) -> u64 {
    let owed: i64 = (0..3).map(|j| g[i][j]).sum();
    let owing: i64 = (0..3).map(|j| g[j][i]).sum();
    let net = owed - owing;
    (((net % t as i64) + t as i64) % t as i64) as u64
}

/// THE LOAD-BEARING TOOTH: each party's net position, computed HOMOMORPHICALLY over the encrypted obligation
/// matrix, decrypts to EXACTLY the plaintext net — and the gross obligations are never opened. This is the
/// running witness of `NettingVault.net_conserves` / `net`. Also checks conservation: the nets sum to 0 mod t.
#[test]
fn netting_vault_reveals_only_the_net() {
    let mut fx = fixture(0x0_e77_0);
    let t = fx.t;
    // A hidden obligation matrix: g[i][j] = party i owes party j (diagonal 0, no self-debt).
    let g: [[i64; 3]; 3] = [[0, 50, 30], [20, 0, 40], [10, 60, 0]];

    // Encrypt the whole gross web. These ciphertexts are NEVER decrypted below.
    let mut ct = vec![vec![None::<Ciphertext>; 3]; 3];
    for i in 0..3 {
        for j in 0..3 {
            if i != j {
                ct[i][j] = Some(encrypt(&mut fx, g[i][j] as u64));
            }
        }
    }

    // Compute each party's net = (Σ_j owed) − (Σ_j owing), homomorphically, then decrypt ONLY the net.
    let mut decrypted_nets = Vec::new();
    for i in 0..3 {
        // owed = Σ_{j≠i} g[i][j]
        let owed = (0..3)
            .filter(|&j| j != i)
            .map(|j| ct[i][j].as_ref().unwrap())
            .cloned()
            .reduce(|a, b| &a + &b)
            .expect("owed sum");
        // owing = Σ_{j≠i} g[j][i]
        let owing = (0..3)
            .filter(|&j| j != i)
            .map(|j| ct[j][i].as_ref().unwrap())
            .cloned()
            .reduce(|a, b| &a + &b)
            .expect("owing sum");
        let net_ct = &owed - &owing; // homomorphic net; the gross totals never leave the ciphertext domain
        let got = decrypt(&fx, &net_ct);
        assert_eq!(
            got,
            plaintext_net_mod_t(&g, i, t),
            "Netting Vault net wrong for party {i} (the fhe.rs oracle)"
        );
        decrypted_nets.push(got);
    }

    // CONSERVATION (net_conserves, running): the revealed nets sum to 0 mod t.
    let sum_mod_t: u64 = decrypted_nets.iter().fold(0u64, |acc, &n| (acc + n) % t);
    assert_eq!(
        sum_mod_t, 0,
        "Netting Vault nets do not conserve (sum != 0 mod t)"
    );
}

/// Run the full netting over an arbitrary N-party obligation matrix `g` (`g[i][j]` = i owes j), homomorphically:
/// encrypt the whole gross web, compute every party's net on ciphertexts, decrypt ONLY the nets. Returns the
/// decrypted net residues (mod t).
fn run_netting(fx: &mut Fixture, g: &[Vec<i64>]) -> Vec<u64> {
    let n = g.len();
    let mut ct: Vec<Vec<Option<Ciphertext>>> =
        (0..n).map(|_| (0..n).map(|_| None).collect()).collect();
    for i in 0..n {
        for j in 0..n {
            if i != j {
                ct[i][j] = Some(encrypt(fx, g[i][j] as u64));
            }
        }
    }
    (0..n)
        .map(|i| {
            let owed = (0..n)
                .filter(|&j| j != i)
                .map(|j| ct[i][j].as_ref().unwrap())
                .cloned()
                .reduce(|a, b| &a + &b)
                .unwrap();
            let owing = (0..n)
                .filter(|&j| j != i)
                .map(|j| ct[j][i].as_ref().unwrap())
                .cloned()
                .reduce(|a, b| &a + &b)
                .unwrap();
            decrypt(fx, &(&owed - &owing))
        })
        .collect()
}

/// GUILD SCALE: an 8-party guild with 56 hidden bilateral obligations (8×8 minus the diagonal) nets down to
/// 8 revealed positions — the "no-viewer multilateral compression" at a real size. Every net is verified vs
/// the plaintext, conservation holds (Σ nets ≡ 0 mod t), and the gross web of 56 obligations is never opened.
/// This is the Netting Vault as a real guild settlement: 56 secret debts in, 8 net numbers out, all else dark.
#[test]
fn netting_vault_guild_scale_settlement() {
    let mut fx = fixture(0x090011D);
    let t = fx.t;
    let n = 8usize;
    // A deterministic guild obligation matrix (i owes j); diagonal 0.
    let mut g: Vec<Vec<i64>> = vec![vec![0i64; n]; n];
    for i in 0..n {
        for j in 0..n {
            if i != j {
                g[i][j] = ((i * 13 + j * 7 + 3) % 97) as i64; // small, deterministic, < t/2
            }
        }
    }
    let nets = run_netting(&mut fx, &g);
    // validate each party's net vs the plaintext net (centered mod t)
    for i in 0..n {
        let owed: i64 = (0..n).map(|j| g[i][j]).sum();
        let owing: i64 = (0..n).map(|j| g[j][i]).sum();
        let want = (((owed - owing) % t as i64 + t as i64) % t as i64) as u64;
        assert_eq!(nets[i], want, "guild net wrong for party {i}");
    }
    // conservation at guild scale: the 8 revealed nets sum to 0 mod t.
    let sum: u64 = nets.iter().fold(0u64, |acc, &x| (acc + x) % t);
    assert_eq!(sum, 0, "guild-scale netting does not conserve");
    // compression: 56 hidden obligations -> 8 net settlements (never opened the gross web).
    assert_eq!(n * (n - 1), 56, "compression count");
}

/// COMPRESSION (symmetric_obligations_net_zero, running): a SYMMETRIC obligation web (`i` owes `j` exactly
/// what `j` owes `i`) nets to zero for every party — computed homomorphically, decrypted. The mutual/gross
/// detail is fully cancelled; only zero crosses the reveal boundary.
#[test]
fn netting_vault_symmetric_web_nets_to_zero() {
    let mut fx = fixture(0x0_e77_5ee);
    // A symmetric web: g[i][j] = g[j][i].
    let g: [[i64; 3]; 3] = [[0, 42, 17], [42, 0, 99], [17, 99, 0]];

    for i in 0..3 {
        let owed = (0..3)
            .filter(|&j| j != i)
            .map(|j| encrypt(&mut fx, g[i][j] as u64))
            .reduce(|a, b| &a + &b)
            .unwrap();
        let owing = (0..3)
            .filter(|&j| j != i)
            .map(|j| encrypt(&mut fx, g[j][i] as u64))
            .reduce(|a, b| &a + &b)
            .unwrap();
        let net_ct = &owed - &owing;
        assert_eq!(
            decrypt(&fx, &net_ct),
            0,
            "symmetric web did not net to zero for party {i} (compression broke)"
        );
    }
}
