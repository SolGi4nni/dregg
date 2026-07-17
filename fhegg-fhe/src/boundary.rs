//! MASKED DECRYPT-TO-SHARES — the last un-built seam of the output-boundary
//! pipeline, made real (the §8 frontier item of `docs/deos/OUTPUT-BOUNDARY-MPC.md`).
//!
//! ## The seam this closes
//!
//! The output-boundary MPC PoC (`crate::mpc`) measured the crossing at
//! milliseconds, but its input step — "the threshold-BFV partial-decrypt-INTO-
//! shares" — was MODELLED by sharing the true decrypted coefficients
//! (`share_int` on cleartext). Between the BFV-encrypted folded curves and the
//! secret-shared MPC crossing there was still one un-built protocol step.
//!
//! ## The construction: mask, THEN decrypt (one-time pad over `Z_t`)
//!
//! A dedicated "partial-decrypt-into-shares" primitive is not needed. Additive
//! homomorphism already gives it, composed from pieces the stack HAS:
//!
//!   1. Each party `i` samples a uniform mask vector `r_i ∈ Z_t^K`, encrypts it,
//!      and homomorphically adds `Enc(r_i)` to the folded curve ciphertext:
//!      `ct' = ct ⊞ Enc(r_0) ⊞ … ⊞ Enc(r_{n-1})` — n more carry-free adds on a
//!      noise budget sized for millions.
//!   2. The network decrypts `ct'` (in production: the EXISTING federation
//!      threshold-decrypt stack — `federation/src/threshold_decrypt.rs`'s
//!      t-of-n Shamir machinery pointed at the BFV key; here: the PoC keypair).
//!      What opens is `y = (m + Σ r_i) mod t` — **a one-time-padded value**,
//!      uniform on `Z_t` and EXACTLY independent of the curve `m` (proven by
//!      enumeration in `pad_is_exact_and_secret_independent`). Decrypting it in
//!      public is safe; nobody learns a curve coefficient.
//!   3. The mod-t additive shares of `m` are then LOCAL: party 0 takes
//!      `σ_0 = (y − r_0) mod t`, party `i>0` takes `σ_i = (−r_i) mod t`, so
//!      `Σ σ_i ≡ m (mod t)` — each party's share is a function of its own mask
//!      (plus the public `y`), no interaction.
//!   4. One boundary bridge (`a2b_mod_t`) converts the mod-t arithmetic shares
//!      to boolean shares — a secret-shared exact integer sum of the n shares
//!      (`secure_add`, width `w = ⌈log₂ n·t⌉`) followed by `n−1` oblivious
//!      conditional subtractions of the public `t` — and the UNCHANGED
//!      Beaver-triple crossing (`mpc_crossing`) runs and reveals only `(p*,V*)`.
//!
//! So the seam dissolves the same way the BFV→TFHE scheme-switch did (R4's
//! move): not by building the exotic adapter, but by restructuring so only
//! already-safe openings happen. The threshold-decrypt that production needs is
//! the one the federation already runs; what this module adds is the masking
//! protocol that makes its OUTPUT safe to open, plus the mod-t → boolean bridge.
//!
//! ## Honest scope (stated like the sibling PoCs)
//!
//! - **REAL:** the value channel. The mask is an exact one-time pad over `Z_t`
//!   (enumeration-proven); the opened `y` carries zero information about the
//!   curve; the mod-t share algebra and the `a2b_mod_t` bridge are real MPC on
//!   real shares; the crossing is the unchanged measured protocol; correctness
//!   is KAT-checked against direct decryption and the plaintext reference.
//! - **PoC-scoped:** the decrypt of `ct'` uses the in-process secret key (the
//!   same PoC posture as `bfv_fold`); production points the existing federation
//!   threshold-decrypt at it. The parties are simulated in one process.
//! - **NAMED, not built:** the decryption NOISE channel. A decryption's noise
//!   term can leak beyond the plaintext (the IND-CPA-D caveat); production
//!   threshold decryption adds smudging noise to the partial decryptions —
//!   standard, orthogonal to the value-channel construction here.

use std::sync::Arc;
use std::time::{Duration, Instant};

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, SecretKey};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter};
use rand::Rng;
use rand_09::rngs::StdRng as StdRng09;
use rand_09::SeedableRng as SeedableRng09;

use crate::additive::{bfv_fold_encrypted, BfvFoldedBook};
use crate::mpc::{
    const_int, geq, mpc_crossing, secure_add, select_int, share_int, triples_needed, Crossing,
    SharedInt, Transcript, TriplePool,
};
use crate::Order;

/// Bits needed to hold `x` (`⌈log₂(x+1)⌉`, min 1).
fn bits_for(x: u64) -> usize {
    (64 - x.leading_zeros() as usize).max(1)
}

/// The mod-t share vector of ONE slot: `shares[i]` is party `i`'s additive share,
/// `Σ_i shares[i] ≡ m (mod t)`.
pub type ModTShares = Vec<u64>;

/// Sample the parties' masks: `masks[i][j]` = party `i`'s uniform `Z_t` mask for
/// slot `j`. Each party samples its own row locally (the PoC uses one rng).
pub fn sample_masks<R: Rng>(n: usize, k: usize, t: u64, rng: &mut R) -> Vec<Vec<u64>> {
    (0..n)
        .map(|_| (0..k).map(|_| rng.gen_range(0..t)).collect())
        .collect()
}

/// The LOCAL share derivation of step 3: given the public masked opening `y` and
/// its own mask row, each party derives its mod-t share of the true slot values.
/// `σ_0 = (y − r_0) mod t`, `σ_i = (−r_i) mod t` for `i > 0`; `Σ σ ≡ m (mod t)`.
pub fn shares_from_masked_opening(y: &[u64], masks: &[Vec<u64>], t: u64) -> Vec<ModTShares> {
    let n = masks.len();
    (0..y.len())
        .map(|j| {
            (0..n)
                .map(|i| {
                    if i == 0 {
                        (y[j] + t - masks[0][j] % t) % t
                    } else {
                        (t - masks[i][j] % t) % t
                    }
                })
                .collect()
        })
        .collect()
}

/// The result of one masked decrypt-to-shares: the (safe-to-open) masked values
/// and each slot's mod-t shares, plus phase timings.
pub struct MaskedDecrypt {
    /// The opened masked plaintext `y[j] = (m[j] + Σ_i r_i[j]) mod t` for the K
    /// live slots — a one-time-padded value, safe to publish.
    pub y: Vec<u64>,
    /// Per-slot mod-t additive shares of the TRUE values: `sigma[j][i]`.
    pub sigma: Vec<ModTShares>,
    /// Wall time for the parties to encrypt their masks + the homomorphic adds.
    pub mask: Duration,
    /// Wall time to decrypt the masked ciphertext (production: the federation
    /// threshold decrypt — its output is exactly this safe-to-open `y`).
    pub decrypt: Duration,
}

/// Steps 1–3: mask the folded curve ciphertext, decrypt ONLY the masked value,
/// derive the local mod-t shares. No curve coefficient is ever opened.
pub fn masked_decrypt_to_shares<R: Rng>(
    ct: &Ciphertext,
    k: usize,
    n: usize,
    params: &Arc<BfvParameters>,
    pk: &PublicKey,
    sk: &SecretKey,
    rng_bfv: &mut StdRng09,
    rng: &mut R,
) -> MaskedDecrypt {
    let t = params.plaintext();

    // (1) Each party encrypts its uniform Z_t mask and adds it homomorphically.
    let t0 = Instant::now();
    let masks = sample_masks(n, k, t, rng);
    let mut ct_masked = ct.clone();
    for row in &masks {
        let pt = Plaintext::try_encode(row, Encoding::simd(), params).expect("mask encode");
        let enc: Ciphertext = pk.try_encrypt(&pt, rng_bfv).expect("mask encrypt");
        ct_masked += &enc;
    }
    let mask_dt = t0.elapsed();

    // (2) Decrypt the MASKED ciphertext. The opened value is one-time-padded —
    //     uniform on Z_t, independent of the curve — so this opening is safe.
    let t0 = Instant::now();
    let pt = sk.try_decrypt(&ct_masked).expect("masked decrypt");
    let y_full = Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("masked decode");
    let y: Vec<u64> = y_full[..k].to_vec();
    let decrypt_dt = t0.elapsed();

    // (3) LOCAL mod-t share derivation from (public y, own mask).
    let sigma = shares_from_masked_opening(&y, &masks, t);

    MaskedDecrypt {
        y,
        sigma,
        mask: mask_dt,
        decrypt: decrypt_dt,
    }
}

/// Step 4 — the mod-t ARITHMETIC → BOOLEAN bridge. The n mod-t shares of one
/// slot are summed EXACTLY (secret-shared ripple adders at width `w = ⌈log₂ n·t⌉`,
/// no wrap), then reduced `mod t` by `n−1` oblivious conditional subtractions
/// (`[acc ≥ t]` → subtract, via `geq` + `select_int`; the comparison bit is never
/// opened). The result is truncated to `b_out` bits — exact, because the true
/// value `m < 2^b_out ≤ t` and boolean sharing is bitwise. Feeds `mpc_crossing`
/// unchanged.
pub fn a2b_mod_t<R: Rng>(
    sigma: &ModTShares,
    t: u64,
    b_out: usize,
    pool: &mut TriplePool,
    tr: &mut Transcript,
    rng: &mut R,
) -> SharedInt {
    let n = sigma.len();
    let w = bits_for(n as u64 * (t - 1));
    assert!(w < 63, "share-sum width {w} out of range");
    assert!(b_out <= w);

    // Exact integer sum of the n shares (each party boolean-shares its own).
    let mut acc = share_int(sigma[0], w, n, rng);
    for &s in &sigma[1..] {
        let xi = share_int(s, w, n, rng);
        acc = secure_add(&acc, &xi, pool, tr);
    }

    // Reduce mod t: up to n−1 conditional subtractions, each oblivious.
    let t_const = const_int(t, w, n);
    let neg_t = const_int((1u64 << w) - t, w, n); // two's-complement −t at width w
    for _ in 0..n - 1 {
        let ge = geq(&acc, &t_const, pool, tr);
        let sub = secure_add(&acc, &neg_t, pool, tr);
        acc = select_int(&ge, &sub, &acc, pool, tr);
    }

    // acc now boolean-shares m < t exactly; keep the low b_out bits (bitwise
    // sharing truncates locally and exactly; the high bits are zero for m < 2^b_out).
    acc.truncate(b_out);
    acc
}

/// Beaver triples one masked-boundary clear consumes: `2K` slots × [`n−1` exact
/// adds + `n−1` × (geq + subtract-add + select)] + the crossing itself.
pub fn triples_needed_boundary(k: usize, b: usize, t: u64, n: usize) -> usize {
    let w = bits_for(n as u64 * (t - 1));
    let per_slot = (n - 1) * (w - 1) + (n - 1) * (3 * w + (w - 1) + w);
    2 * k * per_slot + triples_needed(k, b) + w
}

/// One full masked-boundary clear, with per-phase timings: BFV fold → masked
/// decrypt-to-shares → a2b_mod_t → the unchanged MPC crossing.
pub struct BoundaryRun {
    pub cross: Crossing,
    pub transcript: Transcript,
    pub fold: Duration,
    pub encrypt: Duration,
    pub mask: Duration,
    pub decrypt: Duration,
    pub a2b: Duration,
    pub crossing: Duration,
    pub triples_used: usize,
    pub a2b_and_gates: usize,
}

/// THE END-TO-END TIER-0 PIPELINE with no un-modelled value-channel step:
/// carry-free BFV fold → homomorphic masking → decrypt only the padded value →
/// local mod-t shares → a2b bridge → Beaver-triple crossing → reveal `(p*,V*)`.
pub fn masked_boundary_clear<R: Rng>(
    orders: &[Order],
    k: usize,
    b: usize,
    n: usize,
    params: &Arc<BfvParameters>,
    rng: &mut R,
) -> BoundaryRun {
    let t = params.plaintext();
    let mut rng_bfv = StdRng09::seed_from_u64(0xB0_04_DA_47);

    // (a) the carry-free additive fold (curves stay encrypted).
    let folded: BfvFoldedBook = bfv_fold_encrypted(orders, k, params);

    // (b) masked decrypt-to-shares for demand and supply.
    let d_md = masked_decrypt_to_shares(
        &folded.d_ct,
        k,
        n,
        params,
        &folded.pk,
        &folded.sk,
        &mut rng_bfv,
        rng,
    );
    let s_md = masked_decrypt_to_shares(
        &folded.s_ct,
        k,
        n,
        params,
        &folded.pk,
        &folded.sk,
        &mut rng_bfv,
        rng,
    );

    // (c) the mod-t → boolean bridge, per slot (slots are independent — the
    //     AND-depth, hence network rounds, does not grow with K).
    let mut pool = TriplePool::generate(triples_needed_boundary(k, b, t, n), n, rng);
    let mut tr = Transcript::default();
    let t0 = Instant::now();
    let d_shared: Vec<SharedInt> = d_md
        .sigma
        .iter()
        .map(|s| a2b_mod_t(s, t, b, &mut pool, &mut tr, rng))
        .collect();
    let s_shared: Vec<SharedInt> = s_md
        .sigma
        .iter()
        .map(|s| a2b_mod_t(s, t, b, &mut pool, &mut tr, rng))
        .collect();
    let a2b_dt = t0.elapsed();
    let a2b_ands = tr.and_gates;
    // Depth: ⌈log₂ n⌉ adds of width w + (n−1) sequential conditional subtracts
    // (each a w-deep geq + 1-deep select), shared across all 2K independent slots.
    let w = bits_for(n as u64 * (t - 1));
    tr.rounds += w * n.next_power_of_two().trailing_zeros().max(1) as usize + (n - 1) * (3 * w + 1);

    // (d) the unchanged Beaver-triple crossing — reveals ONLY (p*, V*).
    let t0 = Instant::now();
    let cross = mpc_crossing(&d_shared, &s_shared, &mut pool, &mut tr);
    let crossing_dt = t0.elapsed();

    BoundaryRun {
        cross,
        fold: folded.timing.fold,
        encrypt: folded.timing.encrypt,
        mask: d_md.mask + s_md.mask,
        decrypt: d_md.decrypt + s_md.decrypt,
        a2b: a2b_dt,
        crossing: crossing_dt,
        triples_used: pool.consumed(),
        a2b_and_gates: a2b_ands,
        transcript: tr,
    }
}

/// EXACT pad histogram: enumerate the FULL mask space of one slot at a toy `t`
/// and return the distribution of the opened `y` for a given secret `m`, as seen
/// by a coalition that already knows the masks of `known` parties. If the
/// histograms for two different secrets are IDENTICAL, the opening carries zero
/// information about the secret — the one-time-pad property, proven not sampled.
pub fn masked_opening_histogram(
    m: u64,
    t: u64,
    n: usize,
    known: &[usize],
) -> std::collections::BTreeMap<(Vec<u64>, u64), u64> {
    let mut hist: std::collections::BTreeMap<(Vec<u64>, u64), u64> =
        std::collections::BTreeMap::new();
    let total = (t as u128).pow(n as u32);
    for idx in 0..total {
        let mut rem = idx;
        let mut masks = vec![0u64; n];
        for s in masks.iter_mut() {
            *s = (rem % t as u128) as u64;
            rem /= t as u128;
        }
        let y = masks.iter().fold(m % t, |a, &r| (a + r) % t);
        let view: Vec<u64> = known.iter().map(|&i| masks[i]).collect();
        *hist.entry((view, y)).or_insert(0) += 1;
    }
    hist
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::additive::pick_params;
    use crate::{reference_clear, Side};
    use rand::rngs::StdRng;
    use rand::SeedableRng;

    /// The pad is EXACT: over the full mask space, the (coalition-view, opened-y)
    /// histogram is identical for two different secrets — even when all but one
    /// party's masks are known. Enumeration, not sampling.
    #[test]
    fn pad_is_exact_and_secret_independent() {
        let (t, n) = (17u64, 3usize);
        for known in [vec![], vec![0usize], vec![0, 2]] {
            let h_a = masked_opening_histogram(0, t, n, &known);
            let h_b = masked_opening_histogram(13, t, n, &known);
            assert_eq!(h_a, h_b, "masked opening depends on the secret");
        }
    }

    /// Share algebra: Σσ ≡ m (mod t) for every slot, on real masks.
    #[test]
    fn shares_reconstruct_mod_t() {
        let mut rng = StdRng::seed_from_u64(2);
        let (t, n, k) = (1_032_193u64, 4usize, 8usize);
        let m: Vec<u64> = (0..k as u64).map(|j| j * 977 % 65_536).collect();
        let masks = sample_masks(n, k, t, &mut rng);
        let y: Vec<u64> = (0..k)
            .map(|j| masks.iter().fold(m[j], |a, r| (a + r[j]) % t))
            .collect();
        let sigma = shares_from_masked_opening(&y, &masks, t);
        for j in 0..k {
            let rec = sigma[j].iter().fold(0u64, |a, &s| (a + s) % t);
            assert_eq!(rec, m[j], "slot {j} share reconstruction");
        }
    }

    /// The a2b bridge: random mod-t splits of random values open to the value.
    #[test]
    fn a2b_mod_t_roundtrips() {
        let mut rng = StdRng::seed_from_u64(3);
        let (t, n, b) = (1_032_193u64, 4usize, 16usize);
        let mut pool = TriplePool::generate(64 * triples_needed_boundary(1, b, t, n), n, &mut rng);
        let mut tr = Transcript::default();
        for &m in &[0u64, 1, 2, 65_535, 40_000, 12_345] {
            // random mod-t split of m
            let mut sigma: ModTShares = (0..n - 1).map(|_| rng.gen_range(0..t)).collect();
            let partial = sigma.iter().fold(0u64, |a, &s| (a + s) % t);
            sigma.push((m + t - partial) % t);
            let shared = a2b_mod_t(&sigma, t, b, &mut pool, &mut tr, &mut rng);
            assert_eq!(crate::mpc::open_int(&shared), m, "a2b_mod_t({m})");
        }
    }

    /// KAT vs DIRECT decryption: on real BFV-folded curves, the masked path's
    /// reconstructed shares equal what decrypting the curve directly yields —
    /// the protocol replaces the decryption without changing the value.
    #[test]
    fn masked_decrypt_matches_direct_decrypt() {
        use fhe_traits::{FheDecoder, FheDecrypter};
        let mut rng = StdRng::seed_from_u64(4);
        let params = pick_params(20);
        let t = params.plaintext();
        let (k, n) = (16usize, 3usize);
        let book: Vec<Order> = (0..24)
            .map(|i| Order {
                side: if i % 2 == 0 { Side::Bid } else { Side::Ask },
                limit: (i * 3) % k,
                qty: 1 + (i as u16 % 5),
            })
            .collect();
        let folded = bfv_fold_encrypted(&book, k, &params);
        // direct decryption (the thing production never does in the clear):
        let pt = folded.sk.try_decrypt(&folded.d_ct).expect("direct");
        let direct = Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("decode");
        // the masked path:
        let mut rng_bfv = StdRng09::seed_from_u64(99);
        let md = masked_decrypt_to_shares(
            &folded.d_ct,
            k,
            n,
            &params,
            &folded.pk,
            &folded.sk,
            &mut rng_bfv,
            &mut rng,
        );
        for j in 0..k {
            let rec = md.sigma[j].iter().fold(0u64, |a, &s| (a + s) % t);
            assert_eq!(rec, direct[j], "slot {j}: shares ≠ direct decryption");
        }
    }

    /// The full pipeline KAT: fold → mask → decrypt-masked → shares → a2b →
    /// crossing equals the plaintext reference (correctness preserved end-to-end).
    #[test]
    fn masked_boundary_matches_plaintext_reference() {
        let mut rng = StdRng::seed_from_u64(5);
        let params = pick_params(20);
        for &(nn, k, n) in &[(48usize, 32usize, 3usize), (64, 24, 4)] {
            let book: Vec<Order> = (0..nn)
                .map(|i| Order {
                    side: if i % 2 == 0 { Side::Bid } else { Side::Ask },
                    limit: (i * 7) % k,
                    qty: 1 + (i as u16 % 6),
                })
                .collect();
            let reference = reference_clear(&book, k);
            let run = masked_boundary_clear(&book, k, 16, n, &params, &mut rng);
            assert_eq!(run.cross.p_star, reference.p_star, "N={nn} K={k} n={n}");
            assert_eq!(
                run.cross.v_star as u32, reference.v_star,
                "N={nn} K={k} n={n}"
            );
            assert!(run.transcript.is_reveal_only(k));
        }
    }
}
