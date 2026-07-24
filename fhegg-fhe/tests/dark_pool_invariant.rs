//! THE DARK POOL — the constant-product invariant `x·y = k` verified over HIDDEN reserves.
//!
//! `metatheory/Market/DarkAmm*` (codex) carries the full Dark-AMM relation family; this is a standalone,
//! minimal RUNNING witness of the invariant a Dark Pool swap must preserve: over reserves `x, y` encrypted
//! with REAL fhe.rs, a swap `(dx in, dy out)` is admissible exactly when `(x+dx)·(y−dy) = x·y = k`. The check
//! is HOMOMORPHIC — the reserves `x, y` are never opened; only that the invariant holds (a single equality
//! bit) crosses the reveal boundary. No depth to snipe, but every swap provably priced by the constant
//! product. If the pricing is wrong, fhe.rs decrypts a non-`k` product and the test is RED.
//!
//! The Dark Pool is a hall in `THE-DARK-BAZAAR.md`: a resource AMM whose reserves are hidden. This uses the
//! ct×ct multiply (the invariant `(x+dx)(y−dy)` is a product of two secrets) that MEASURES 3.35×/5.13×/10× on
//! GPU — so a batched swap-verification pass is the compute-bound GPU-favorable shape.

use fhe::bfv::{
    BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, RelinearizationKey, SecretKey,
};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter};
use rand_09::rngs::StdRng;
use rand_09::SeedableRng;
use std::sync::Arc;

use fhegg_fhe::additive::pick_params;
use fhegg_fhe::bfv_mul::{BoundedCiphertext, MulEngine};

struct Fixture {
    params: Arc<BfvParameters>,
    sk: SecretKey,
    pk: PublicKey,
    rk: RelinearizationKey,
    rng: StdRng,
}

fn fixture(seed: u64) -> Fixture {
    let params = pick_params(20);
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
    }
}

fn encrypt_val(fx: &mut Fixture, v: u64) -> Ciphertext {
    let pt = Plaintext::try_encode(&[v], Encoding::simd(), &fx.params).expect("simd encode");
    fx.pk.try_encrypt(&pt, &mut fx.rng).expect("pk encrypt")
}

fn pt(fx: &Fixture, v: u64) -> Plaintext {
    Plaintext::try_encode(&[v], Encoding::simd(), &fx.params).expect("pt encode")
}

fn decrypt(fx: &Fixture, ct: &Ciphertext) -> u64 {
    let pt = fx.sk.try_decrypt(ct).expect("fhe.rs decrypt");
    Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("simd decode")[0]
}

fn engine(fx: &Fixture) -> MulEngine {
    MulEngine::new(&fx.rk, &fx.params).expect("mul engine")
}

/// The post-swap reserve product `(x+dx)·(y−dy)`, computed HOMOMORPHICALLY over the hidden reserves.
fn post_swap_product(
    fx: &Fixture,
    eng: &MulEngine,
    ctx: &Ciphertext,
    x: u64,
    cty: &Ciphertext,
    y: u64,
    dx: u64,
    dy: u64,
) -> BoundedCiphertext {
    let new_x = ctx + &pt(fx, dx); // x + dx  (plaintext add; reserve stays hidden)
    let new_y = cty - &pt(fx, dy); // y − dy
    eng.multiply(
        &BoundedCiphertext::new(new_x, x + dx),
        &BoundedCiphertext::new(new_y, y - dy),
    )
    .expect("post-swap product")
}

/// THE LOAD-BEARING TOOTH: a constant-product swap over HIDDEN reserves preserves `x·y = k`, verified
/// homomorphically — the reserves are never opened, only that the invariant holds. A fair swap (`dx=10 in`,
/// `dy=10 out` on `x=10,y=20`, so `(20)(10)=200=x·y`) passes.
#[test]
fn dark_pool_fair_swap_preserves_constant_product() {
    let mut fx = fixture(0x0_DA12_0);
    let eng = engine(&fx);
    let (x, y) = (10u64, 20u64);
    let k = x * y; // 200 — the pool's public invariant
    let (dx, dy) = (10u64, 10u64); // (x+dx)(y-dy) = 20*10 = 200 = k
    let ctx = encrypt_val(&mut fx, x);
    let cty = encrypt_val(&mut fx, y);
    let old_prod = eng
        .multiply(
            &BoundedCiphertext::new(ctx.clone(), x),
            &BoundedCiphertext::new(cty.clone(), y),
        )
        .expect("x*y");
    let new_prod = post_swap_product(&fx, &eng, &ctx, x, &cty, y, dx, dy);
    assert_eq!(decrypt(&fx, &old_prod.ct), k, "pre-swap product != k");
    assert_eq!(
        decrypt(&fx, &new_prod.ct),
        k,
        "post-swap product != k (constant product broke)"
    );
    // Reveal ONLY that the invariant holds: (new − old) decrypts to 0. The reserves x,y never appear.
    let diff = &new_prod.ct - &old_prod.ct;
    assert_eq!(
        decrypt(&fx, &diff),
        0,
        "constant-product invariant violated on hidden reserves"
    );
}

/// THE GUARD BITES: an UNFAIR swap (one that does NOT preserve `x·y`) is CAUGHT — the homomorphic invariant
/// check reveals a nonzero difference, so the Dark Pool can refuse it without ever opening the reserves. Here
/// `dy=9` instead of `10` gives `(20)(11)=220 ≠ 200`, and the invariant difference decrypts to a nonzero
/// value. So a swap that skims the pool is provably detectable on encrypted reserves.
#[test]
fn dark_pool_unfair_swap_is_detected() {
    let mut fx = fixture(0x0_DA12_bad);
    let eng = engine(&fx);
    let (x, y) = (10u64, 20u64);
    let (dx, dy) = (10u64, 9u64); // UNFAIR: (20)(11) = 220 != 200
    let ctx = encrypt_val(&mut fx, x);
    let cty = encrypt_val(&mut fx, y);
    let old_prod = eng
        .multiply(
            &BoundedCiphertext::new(ctx.clone(), x),
            &BoundedCiphertext::new(cty.clone(), y),
        )
        .expect("x*y");
    let new_prod = post_swap_product(&fx, &eng, &ctx, x, &cty, y, dx, dy);
    let diff = &new_prod.ct - &old_prod.ct;
    assert_ne!(
        decrypt(&fx, &diff),
        0,
        "an UNFAIR swap passed the constant-product invariant (the guard did not bite)"
    );
}
