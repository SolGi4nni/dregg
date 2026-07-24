//! THE ORACLE PIT — a WORKING confidential quadratic prediction market, over ENCRYPTED positions.
//!
//! `metatheory/Market/OraclePitQuadratic.lean` PROVES the Oracle Pit's quadratic cost decrypts exactly
//! (`quadratic_form_2var_decrypts`, with the noise budget discharged). This file is the running artifact of
//! that proof: it prices `c = q₁² + q₁·q₂ + q₂²` over positions encrypted with REAL fhe.rs, using the
//! `bfv_mul` engine's `product_sum` (`Σ lhs[i]·rhs[i]`), and decrypts with REAL fhe.rs. If the pricing is
//! wrong in any way, fhe.rs decrypts the wrong price and the test is RED — agreement with a real BFV library
//! cannot be faked (the same oracle discipline as `bfv_mul_oracle`).
//!
//! The Oracle Pit is a FRONTIER hall in `THE-DARK-BAZAAR.md`: a prediction market priced by a quadratic cost
//! function (not LMSR), with positions hidden. The pricing is ONE homomorphic evaluation (three multiplies +
//! sum), so the noise budget is bounded — and each product rides the ct×ct multiply that MEASURES 3.35×/5.13×/
//! 10× on GPU (`FHEGG-GPU-ARCHITECTURE-RECONSIDERED.md`), so the batched-SIMD pass below is exactly the
//! compute-bound GPU-favorable shape.

use fhe::bfv::{
    BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, RelinearizationKey, SecretKey,
};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter};
use rand_09::rngs::StdRng;
use rand_09::SeedableRng;
use std::sync::Arc;

use fhegg_fhe::additive::pick_params;
use fhegg_fhe::bfv_lean::{FOLD_DEGREE, FOLD_MODULI};
use fhegg_fhe::bfv_mul::{BoundedCiphertext, MulEngine};

struct Fixture {
    params: Arc<BfvParameters>,
    sk: SecretKey,
    pk: PublicKey,
    rk: RelinearizationKey,
    rng: StdRng,
    t: u64,
}

fn fixture(seed: u64) -> Fixture {
    let params = pick_params(20);
    assert_eq!(params.degree(), FOLD_DEGREE, "degree drifted");
    assert_eq!(params.moduli(), &FOLD_MODULI, "RNS moduli drifted");
    let t = params.plaintext();
    assert_eq!(t, 1_032_193, "plaintext modulus drifted");
    let mut rng = StdRng::seed_from_u64(seed);
    let sk = SecretKey::random(&params, &mut rng);
    let pk = PublicKey::new(&sk, &mut rng);
    let rk = RelinearizationKey::new(&sk, &mut rng).expect("relin key");
    Fixture {
        params,
        sk,
        pk,
        rk,
        rng,
        t,
    }
}

fn encrypt(fx: &mut Fixture, slots: &[u64]) -> Ciphertext {
    let pt = Plaintext::try_encode(slots, Encoding::simd(), &fx.params).expect("simd encode");
    fx.pk.try_encrypt(&pt, &mut fx.rng).expect("pk encrypt")
}

fn decrypt_slots(fx: &Fixture, ct: &Ciphertext, k: usize) -> Vec<u64> {
    let pt = fx.sk.try_decrypt(ct).expect("fhe.rs decrypt");
    let v = Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("simd decode");
    v[..k].to_vec()
}

fn engine(fx: &Fixture) -> MulEngine {
    MulEngine::new(&fx.rk, &fx.params).expect("mul engine")
}

/// The plaintext oracle: the unit quadratic cost `q₁² + q₁·q₂ + q₂²`.
fn plaintext_quadratic(q1: u64, q2: u64) -> u64 {
    q1 * q1 + q1 * q2 + q2 * q2
}

/// Price the Oracle Pit's unit quadratic over ENCRYPTED positions:
/// `c = q₁² + q₁·q₂ + q₂² = product_sum([q₁,q₁,q₂], [q₁,q₂,q₂])`.
fn price_quadratic(
    eng: &MulEngine,
    ct1: &Ciphertext,
    q1: u64,
    ct2: &Ciphertext,
    q2: u64,
) -> BoundedCiphertext {
    let lhs = [
        BoundedCiphertext::new(ct1.clone(), q1),
        BoundedCiphertext::new(ct1.clone(), q1),
        BoundedCiphertext::new(ct2.clone(), q2),
    ];
    let rhs = [
        BoundedCiphertext::new(ct1.clone(), q1),
        BoundedCiphertext::new(ct2.clone(), q2),
        BoundedCiphertext::new(ct2.clone(), q2),
    ];
    eng.product_sum(&lhs, &rhs).expect("oracle pit price")
}

/// A public weight `w` as a single-slot plaintext (scales SIMD slot 0 by `w`).
fn weight_pt(fx: &Fixture, w: u64) -> Plaintext {
    Plaintext::try_encode(&[w], Encoding::simd(), &fx.params).expect("weight encode")
}

/// The full parametrized quadratic cost `A·q₁² + B·q₁·q₂ + C·q₂²` with PUBLIC weights, over encrypted
/// positions: three ct×ct products, each scaled by its public weight plaintext (`&ct * &pt`), then summed.
/// This is the real Oracle-Pit pricing (an arbitrary quadratic cost matrix), not the unit form.
fn price_weighted_quadratic(
    fx: &Fixture,
    eng: &MulEngine,
    ct1: &Ciphertext,
    q1: u64,
    ct2: &Ciphertext,
    q2: u64,
    a: u64,
    b: u64,
    c: u64,
) -> Ciphertext {
    let p11 = eng
        .multiply(
            &BoundedCiphertext::new(ct1.clone(), q1),
            &BoundedCiphertext::new(ct1.clone(), q1),
        )
        .expect("q1^2");
    let p12 = eng
        .multiply(
            &BoundedCiphertext::new(ct1.clone(), q1),
            &BoundedCiphertext::new(ct2.clone(), q2),
        )
        .expect("q1*q2");
    let p22 = eng
        .multiply(
            &BoundedCiphertext::new(ct2.clone(), q2),
            &BoundedCiphertext::new(ct2.clone(), q2),
        )
        .expect("q2^2");
    let t1 = &p11.ct * &weight_pt(fx, a);
    let t2 = &p12.ct * &weight_pt(fx, b);
    let t3 = &p22.ct * &weight_pt(fx, c);
    &(&t1 + &t2) + &t3
}

/// A parametrized quadratic prediction market (public cost matrix `A,B,C`) prices hidden positions and
/// decrypts to EXACTLY `A·q₁² + B·q₁·q₂ + C·q₂²` — the running witness of `quadratic_form_2var_decrypts` with
/// real public weights. This is the actual Oracle-Pit product, not the unit demo.
#[test]
fn oracle_pit_prices_weighted_quadratic() {
    let mut fx = fixture(0x0AC1E5A1);
    let eng = engine(&fx);
    let (q1, q2) = (4u64, 6u64);
    let (a, b, c) = (2u64, 3u64, 5u64);
    let ct1 = encrypt(&mut fx, &[q1]);
    let ct2 = encrypt(&mut fx, &[q2]);
    let priced = price_weighted_quadratic(&fx, &eng, &ct1, q1, &ct2, q2, a, b, c);
    let got = decrypt_slots(&fx, &priced, 1)[0];
    let want = a * q1 * q1 + b * q1 * q2 + c * q2 * q2;
    assert!(
        want < fx.t,
        "test setup: weighted quadratic must stay below t"
    );
    assert_eq!(
        got, want,
        "weighted Oracle Pit price != plaintext A·q₁²+B·q₁q₂+C·q₂² (fhe.rs oracle)"
    );
}

/// THE LOAD-BEARING TOOTH: a quadratic market priced over encrypted positions decrypts to EXACTLY the
/// plaintext quadratic — the running witness of `OraclePitQuadratic.quadratic_form_2var_decrypts`.
#[test]
fn oracle_pit_prices_unit_quadratic() {
    let mut fx = fixture(0x0AC1E010);
    let eng = engine(&fx);
    let (q1, q2) = (7u64, 11u64);
    let ct1 = encrypt(&mut fx, &[q1]);
    let ct2 = encrypt(&mut fx, &[q2]);
    let priced = price_quadratic(&eng, &ct1, q1, &ct2, q2);
    let got = decrypt_slots(&fx, &priced.ct, 1)[0];
    assert_eq!(
        got,
        plaintext_quadratic(q1, q2),
        "Oracle Pit quadratic price != plaintext quadratic (the fhe.rs oracle)"
    );
}

/// BATCHED pricing: many independent markets priced in ONE homomorphic pass via the SIMD slots — the exact
/// compute-bound, GPU-favorable shape (each slot's quadratic priced simultaneously through the shared NTT).
#[test]
fn oracle_pit_prices_batched_simd_markets() {
    let mut fx = fixture(0x0AC1E517);
    let eng = engine(&fx);
    // 8 independent prediction markets, positions packed into SIMD slots.
    let q1s: Vec<u64> = vec![3, 5, 7, 9, 11, 13, 2, 4];
    let q2s: Vec<u64> = vec![4, 6, 8, 10, 1, 3, 5, 7];
    let k = q1s.len();
    let ct1 = encrypt(&mut fx, &q1s);
    let ct2 = encrypt(&mut fx, &q2s);
    // per-slot bound: the largest position across all markets keeps every slot's product in-budget.
    let b1 = *q1s.iter().max().unwrap();
    let b2 = *q2s.iter().max().unwrap();
    let priced = price_quadratic(&eng, &ct1, b1, &ct2, b2);
    let got = decrypt_slots(&fx, &priced.ct, k);
    for i in 0..k {
        assert_eq!(
            got[i],
            plaintext_quadratic(q1s[i], q2s[i]),
            "batched Oracle Pit price wrong in market slot {i}"
        );
    }
}

/// THE WRAP GUARD BITES: a quadratic whose plaintext value could reach `t` is REFUSED at pricing (the
/// `A·m < t` guard from the Lean theorem, enforced by `bfv_mul`'s bound). So the Oracle Pit fails CLOSED on
/// a would-be wrapping price rather than returning a silently-wrong one.
#[test]
fn oracle_pit_refuses_wrapping_price() {
    let mut fx = fixture(0x0AC1EDEAD);
    let eng = engine(&fx);
    // positions large enough that q₁²+q₁q₂+q₂² would exceed t = 1_032_193.
    let (q1, q2) = (700u64, 700u64);
    assert!(
        plaintext_quadratic(q1, q2) >= fx.t,
        "test setup: pick positions whose quadratic exceeds t"
    );
    let ct1 = encrypt(&mut fx, &[q1]);
    let ct2 = encrypt(&mut fx, &[q2]);
    let lhs = [
        BoundedCiphertext::new(ct1.clone(), q1),
        BoundedCiphertext::new(ct1.clone(), q1),
        BoundedCiphertext::new(ct2.clone(), q2),
    ];
    let rhs = [
        BoundedCiphertext::new(ct1.clone(), q1),
        BoundedCiphertext::new(ct2.clone(), q2),
        BoundedCiphertext::new(ct2.clone(), q2),
    ];
    assert!(
        eng.product_sum(&lhs, &rhs).is_err(),
        "Oracle Pit priced a WRAPPING quadratic instead of refusing (the wrap guard did not bite)"
    );
}
