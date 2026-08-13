//! KPZ21 (eprint 2021/204) §3.1 encryption-rounding audit, at the DEPLOYED
//! BFV parameters.
//!
//! VERDICT the workstream card asked for, measured here: the vendored
//! `fhe-dregg` (byte-inherited from upstream fhe.rs 0.1.1) ALREADY encrypts
//! with the exact-division encoding of KPZ21's first modification.
//! `Plaintext::to_poly` computes `−t⁻¹·((Q mod t)·m mod t) ≡ ⌊Q·m/t⌋ (mod Q)`
//! — KPZ Remark 3.1's RNS formula, floor variant — NOT the classic
//! pre-rounded `Δ·m` with `Δ = ⌊Q/t⌋`. There is no r_t(Q) term to remove and
//! no depth left on the table from this fix.
//!
//! What this test therefore does:
//!  1. pins the deployed parameter set (degree 4096, FOLD_MODULI, t=1032193,
//!     r_t(Q) = 843789 ≈ 0.818·t);
//!  2. proves the library encoding is exact-division by MEASURE: a fresh
//!     ciphertext's noise must sit far below log2(r_t(Q)) ≈ 19.7 bits;
//!  3. keeps the falsifier alive constructively: it hand-builds the classic
//!     `a·s + e + Δ·[m]_t` ciphertext (public API only: encrypt zero, add
//!     `Δ·m` into c0) and asserts the SAME noise meter sees the r_t(Q)·m
//!     term in it. If the meter ever goes blind, or the library encoding
//!     ever regresses to pre-rounded Δ, this goes red;
//!  4. measures the depth differential: squaring chains from both encodings
//!     under relinearized multiplication, decode-correctness per level.
//!
//! Both arms use the same secret key, relinearization key and message, so
//! the ONLY difference is the encryption-time encoding.

use std::sync::Arc;

use fhe::bfv::{
    BfvParameters, Ciphertext, Encoding, Multiplicator, Plaintext, RelinearizationKey, SecretKey,
};
use fhe_math::rns::RnsContext;
use fhe_math::rq::{traits::TryConvertFrom, Poly, Representation};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter};
use fhegg_core::bfv_lean::{FOLD_DEGREE, FOLD_MODULI};
use rand_09::Rng;

/// Deployed plaintext modulus (fhegg-fhe's FOLD_PLAINTEXT_MODULUS; the largest
/// 20-bit prime ≡ 1 mod 2N, so SIMD is available).
const T: u64 = 1_032_193;

/// r_t(Q) = Q mod t at the deployed set. Derived in-test from the moduli too;
/// this constant is the independently computed pin (0.818·t, the "0.82t" of
/// notes/fhe-core-theory.md).
const R_T_Q: u64 = 843_789;

fn deployed_params() -> Arc<BfvParameters> {
    let params = fhegg_core::params::pick_params(20);
    // Pin: this is the fold set the whole tree deploys, not a lookalike.
    assert_eq!(params.degree(), FOLD_DEGREE, "deployed degree drifted");
    assert_eq!(params.moduli(), FOLD_MODULI, "deployed moduli drifted");
    params
}

/// Bit size of r_t(Q), the term KPZ's exact encoding deletes.
fn rt_bits() -> u32 {
    64 - R_T_Q.leading_zeros() // 20 bits (2^19.69)
}

/// Classic (pre-KPZ) BFV encryption `a·s + e + Δ·[m]_t`, `Δ = ⌊Q/t⌋`,
/// constructed from public API: encrypt the zero plaintext (giving `a·s + e`
/// under c0 + c1·s), then add the pre-rounded `Δ·m` into c0.
fn encrypt_classic_delta<R: rand_09::RngCore + rand_09::CryptoRng>(
    sk: &SecretKey,
    pt: &Plaintext,
    params: &Arc<BfvParameters>,
    rng: &mut R,
) -> Ciphertext {
    let ctx = params.context_at_level(0).expect("level-0 context");

    // [m]_t coefficient vector, lifted into R_Q (PowerBasis, values in [0,t)).
    let mut m_poly = Poly::try_convert_from(pt, ctx, false, Representation::PowerBasis)
        .expect("plaintext lifts into R_Q");
    m_poly.change_representation(Representation::Ntt);

    // Δ = ⌊Q/t⌋ as a constant polynomial of R_Q.
    let rns = RnsContext::new(params.moduli()).expect("RNS context over deployed moduli");
    let q_big = rns.modulus().clone();
    // Cross-check the pinned r_t(Q) against the deployed moduli right here.
    let rt_derived = (&q_big % T)
        .try_into()
        .unwrap_or_else(|_| panic!("r_t(Q) fits u64"));
    assert_eq!(R_T_Q, rt_derived, "pinned r_t(Q) drifted from the moduli");
    let delta = &q_big / T;
    let mut delta_poly = Poly::try_convert_from(
        std::slice::from_ref(&delta),
        ctx,
        true,
        Representation::PowerBasis,
    )
    .expect("Δ lifts into R_Q");
    delta_poly.change_representation(Representation::Ntt);

    m_poly *= &delta_poly; // Δ·[m]_t, the classic encryption's message term

    let zero = Plaintext::zero(Encoding::simd(), params).expect("zero plaintext");
    let mut ct: Ciphertext = sk.try_encrypt(&zero, rng).expect("Enc(0)");
    ct[0] += &m_poly;
    ct
}

struct ChainReport {
    fresh_noise_bits: usize,
    /// (noise bits after level k, decode still correct) for k = 1..
    levels: Vec<(usize, bool)>,
}

impl ChainReport {
    fn depth(&self) -> usize {
        self.levels.iter().take_while(|(_, ok)| *ok).count()
    }
    fn noise_after(&self, level: usize) -> usize {
        self.levels[level - 1].0
    }
}

/// Square `start` repeatedly (relinearized), measuring noise and decode
/// correctness at every level.
fn run_squaring_chain(
    label: &str,
    start: &Ciphertext,
    m: &[u64],
    sk: &SecretKey,
    mul: &Multiplicator,
) -> ChainReport {
    let fresh_noise_bits = unsafe { sk.measure_noise(start).expect("fresh noise") };
    println!("[{label}] fresh noise: {fresh_noise_bits} bits");

    let mut ct = start.clone();
    let mut expected: Vec<u64> = m.to_vec();
    let mut levels = Vec::new();
    for level in 1..=6 {
        ct = mul.multiply(&ct, &ct).expect("relinearized square");
        expected = expected
            .iter()
            .map(|&v| ((v as u128 * v as u128) % T as u128) as u64)
            .collect();
        let noise = unsafe { sk.measure_noise(&ct).expect("noise after square") };
        let pt = sk.try_decrypt(&ct).expect("decrypt");
        let decoded = Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("decode");
        let ok = decoded == expected;
        println!("[{label}] after square #{level}: noise {noise} bits, decode correct: {ok}");
        levels.push((noise, ok));
        if !ok {
            break;
        }
    }
    ChainReport {
        fresh_noise_bits,
        levels,
    }
}

#[test]
fn kpz_exact_encoding_is_deployed_and_measures_ahead_of_classic_delta() {
    let params = deployed_params();
    let mut rng = rand_09::rng();

    let sk = SecretKey::random(&params, &mut rng);
    let rk = RelinearizationKey::new(&sk, &mut rng).expect("relin key at level 0");
    let mul = Multiplicator::default(&rk).expect("default multiplicator");

    let m: Vec<u64> = (0..params.degree())
        .map(|_| rng.random_range(0..T))
        .collect();
    let pt = Plaintext::try_encode(&m, Encoding::simd(), &params).expect("encode");

    // Arm 1: the library encoding (exact division, KPZ §3.1 / Remark 3.1).
    let ct_exact = sk.try_encrypt(&pt, &mut rng).expect("library encryption");
    // Arm 2: the classic pre-rounded encoding the fix replaces.
    let ct_classic = encrypt_classic_delta(&sk, &pt, &params, &mut rng);

    let exact = run_squaring_chain("exact ⌊Q·m/t⌋", &ct_exact, &m, &sk, &mul);
    let classic = run_squaring_chain("classic Δ·m", &ct_classic, &m, &sk, &mul);

    println!(
        "depth (correct relinearized squarings at deployed params): exact = {}, classic = {}",
        exact.depth(),
        classic.depth()
    );

    // (2) The library encoding carries NO r_t(Q)·m term: fresh noise is the
    // encryption noise alone, far under log2(r_t(Q)) ≈ 19.7 bits. If encryption
    // ever regresses to pre-rounded Δ·m, fresh noise jumps to ~20 bits and this
    // fails.
    assert!(
        exact.fresh_noise_bits + 4 < rt_bits() as usize,
        "library fresh noise ({} bits) is within 4 bits of r_t(Q) ({} bits): \
         the exact-division encoding has regressed toward classic Δ·m",
        exact.fresh_noise_bits,
        rt_bits(),
    );

    // (3) The falsifier falsifies: the SAME meter, pointed at the classic
    // encoding, must SEE the r_t(Q)·m term (≈ r_t(Q) in the worst slot).
    // If this fails, the instrument is blind, not the wound healed.
    let expect_classic = rt_bits() as usize; // 20
    assert!(
        classic.fresh_noise_bits + 2 >= expect_classic,
        "classic Δ·m arm measures only {} bits fresh — the noise meter no \
         longer sees the r_t(Q) term (expected ≈{} bits); the falsifier died",
        classic.fresh_noise_bits,
        expect_classic,
    );

    // (4) The first multiplication inherits the gap (KPZ §3.1: the r_t(Q)
    // term "affects the first homomorphic multiplication"): the classic arm
    // must be measurably noisier after square #1.
    let gap_mult1 = classic.noise_after(1) as i64 - exact.noise_after(1) as i64;
    println!("post-first-multiplication noise gap (classic − exact): {gap_mult1} bits");
    assert!(
        gap_mult1 >= 4,
        "expected the classic encoding to pay ≥4 extra bits at the first \
         multiplication, measured {gap_mult1}",
    );

    // The headline: with the exact encoding already deployed, no depth is
    // left on the table — the classic arm can never do BETTER.
    assert!(
        exact.depth() >= classic.depth(),
        "classic Δ·m encoding reached depth {} > exact {}: measurement \
         contradicts KPZ21 §3.1",
        classic.depth(),
        exact.depth(),
    );
}

/// The depth verdict as a DISTRIBUTION, not one draw.
///
/// The single-draw test above put the classic arm at 88 bits against a
/// decryption cliff of log2(Q/2t) = 88.02 bits — it decoded by a hair. Whether
/// the r_t(Q) term costs a whole LEVEL at the deployed ring is therefore a
/// question about a boundary, and one sample cannot answer it. This runs the
/// same A/B over many independent (sk, m) draws and reports the depth
/// histogram plus the per-operation noise ledger the workstream card asked
/// for: bits consumed by add, by plaintext-ciphertext mul, and by each
/// relinearized ciphertext-ciphertext mul.
#[test]
fn kpz_depth_distribution_and_noise_ledger() {
    let params = deployed_params();
    let mut rng = rand_09::rng();

    // Decryption budget: KPZ eq. (8), ||v||_inf < Q/2t.
    let rns = RnsContext::new(params.moduli()).expect("RNS context");
    let budget_bits = (rns.modulus() / (2u64 * T)).bits() as usize;
    println!("decryption budget log2(Q/2t) = {budget_bits} bits (cliff)");

    const TRIALS: usize = 40;
    let mut exact_depths = vec![0usize; 8];
    let mut classic_depths = vec![0usize; 8];
    // Accumulated noise at each stage, for the ledger.
    let mut exact_noise: Vec<Vec<usize>> = vec![Vec::new(); 4];
    let mut classic_noise: Vec<Vec<usize>> = vec![Vec::new(); 4];
    let mut add_noise = Vec::new();
    let mut ptmul_noise = Vec::new();

    for trial in 0..TRIALS {
        let sk = SecretKey::random(&params, &mut rng);
        let rk = RelinearizationKey::new(&sk, &mut rng).expect("relin key");
        let mul = Multiplicator::default(&rk).expect("multiplicator");
        let m: Vec<u64> = (0..params.degree())
            .map(|_| rng.random_range(0..T))
            .collect();
        let pt = Plaintext::try_encode(&m, Encoding::simd(), &params).expect("encode");

        let ct_exact: Ciphertext = sk.try_encrypt(&pt, &mut rng).expect("library encryption");
        let ct_classic = encrypt_classic_delta(&sk, &pt, &params, &mut rng);

        // Per-operation ledger on the DEPLOYED (exact) encoding only: these are
        // the numbers that describe what we actually run.
        if trial == 0 {
            let ct_b: Ciphertext = sk.try_encrypt(&pt, &mut rng).expect("second encryption");
            let sum = &ct_exact + &ct_b;
            add_noise.push(unsafe { sk.measure_noise(&sum).expect("add noise") });
            let prod = &ct_exact * &pt;
            ptmul_noise.push(unsafe { sk.measure_noise(&prod).expect("pt-ct mul noise") });
        }

        for (start, depths, acc) in [
            (&ct_exact, &mut exact_depths, &mut exact_noise),
            (&ct_classic, &mut classic_depths, &mut classic_noise),
        ] {
            let fresh = unsafe { sk.measure_noise(start).expect("fresh noise") };
            acc[0].push(fresh);
            let mut ct = start.clone();
            let mut expected: Vec<u64> = m.clone();
            let mut depth = 0usize;
            for level in 1..=3 {
                ct = mul.multiply(&ct, &ct).expect("relinearized square");
                expected = expected
                    .iter()
                    .map(|&v| ((v as u128 * v as u128) % T as u128) as u64)
                    .collect();
                let noise = unsafe { sk.measure_noise(&ct).expect("noise") };
                acc[level].push(noise);
                let decoded = Vec::<u64>::try_decode(
                    &sk.try_decrypt(&ct).expect("decrypt"),
                    Encoding::simd(),
                )
                .expect("decode");
                if decoded != expected {
                    break;
                }
                depth = level;
            }
            depths[depth] += 1;
        }
    }

    let mean = |v: &[usize]| v.iter().sum::<usize>() as f64 / v.len() as f64;
    println!("\n=== per-operation noise ledger, DEPLOYED exact encoding (bits) ===");
    println!(
        "  fresh ciphertext           : {:.1}",
        mean(&exact_noise[0])
    );
    println!("  after ct+ct add            : {}", add_noise[0]);
    println!("  after pt-ct mul            : {}", ptmul_noise[0]);
    for lvl in 1..=3 {
        println!(
            "  after ct*ct mul #{lvl} (relin): {:.1}   (+{:.1} over previous)",
            mean(&exact_noise[lvl]),
            mean(&exact_noise[lvl]) - mean(&exact_noise[lvl - 1]),
        );
    }
    println!("\n=== counterfactual classic Δ·m encoding (bits) ===");
    for lvl in 0..=3 {
        println!(
            "  stage {lvl}: {:.1}   (classic − exact = {:+.1})",
            mean(&classic_noise[lvl]),
            mean(&classic_noise[lvl]) - mean(&exact_noise[lvl]),
        );
    }
    println!("\n=== depth histogram over {TRIALS} independent draws ===");
    println!("  exact   ⌊Q·m/t⌋ : {:?}", &exact_depths[..4]);
    println!("  classic Δ·m     : {:?}", &classic_depths[..4]);

    // The exact encoding must never reach LESS depth than classic.
    let exact_mean_depth: f64 = exact_depths
        .iter()
        .enumerate()
        .map(|(d, n)| (d * n) as f64)
        .sum::<f64>()
        / TRIALS as f64;
    let classic_mean_depth: f64 = classic_depths
        .iter()
        .enumerate()
        .map(|(d, n)| (d * n) as f64)
        .sum::<f64>()
        / TRIALS as f64;
    println!("  mean depth: exact {exact_mean_depth:.2}, classic {classic_mean_depth:.2}");
    assert!(
        exact_mean_depth >= classic_mean_depth,
        "classic mean depth {classic_mean_depth} exceeded exact {exact_mean_depth}"
    );
}
