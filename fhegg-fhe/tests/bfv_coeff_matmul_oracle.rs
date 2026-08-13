//! THE ORACLE TEETH for `bfv_coeff_matmul` — fhe.rs is the authority. Every
//! test encrypts with REAL fhe.rs, evaluates the rotation-free coefficient
//! matmul, and decrypts with REAL fhe.rs, comparing against the exact integer
//! reference `W·v`. If the packing is wrong in any way, fhe.rs decrypts the
//! wrong vector and the test is RED.
//!
//! Params (asserted, not assumed): degree-4096, RNS moduli
//! {0xffffee001, 0xffffc4001, 0x1ffffe0001} (~109-bit q), t = 1032193 (~2^20)
//! — the deployed fold set.
//!
//! The measurement tests (`measured_*`) print a ledger; they assert only
//! properties that must hold for the route to be usable at all (the matmul
//! consumes noise, and what remains still admits a ct×ct multiply), and leave
//! the numbers themselves to the report. They are MEASUREMENTS, not bounds:
//! nothing here is a proof about all inputs.

use std::sync::Arc;
use std::time::Instant;

use fhe::bfv::{
    BfvParameters, Ciphertext, Encoding, Multiplicator, Plaintext, PublicKey, RelinearizationKey,
    SecretKey,
};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter};
use rand_09::rngs::StdRng;
use rand_09::SeedableRng;

use fhegg_fhe::additive::pick_params;
use fhegg_fhe::bfv_coeff_matmul::{
    max_inner_dim, signed_abs_bound, CoeffMatmulError, MatmulPlan, WeightLift,
};
use fhegg_fhe::bfv_lean::{FOLD_DEGREE, FOLD_MODULI};

struct Fixture {
    params: Arc<BfvParameters>,
    sk: SecretKey,
    pk: PublicKey,
    rng: StdRng,
}

fn fixture(seed: u64) -> Fixture {
    let params = pick_params(20);
    // Pin the parameter facts. If fhe.rs's default set ever drifts, this fails
    // LOUDLY instead of testing a different scheme.
    assert_eq!(params.degree(), FOLD_DEGREE, "degree drifted");
    assert_eq!(params.moduli(), &FOLD_MODULI, "RNS moduli drifted");
    assert_eq!(params.plaintext(), 1_032_193, "plaintext modulus drifted");
    let mut rng = StdRng::seed_from_u64(seed);
    let sk = SecretKey::random(&params, &mut rng);
    let pk = PublicKey::new(&sk, &mut rng);
    Fixture {
        params,
        sk,
        pk,
        rng,
    }
}

/// Client side: encode `v` under the plan and encrypt each input block.
fn encrypt_vector(fx: &mut Fixture, plan: &MatmulPlan, v: &[i64]) -> Vec<Ciphertext> {
    plan.encode_vector(v, &fx.params)
        .expect("poly encode of v")
        .into_iter()
        .map(|pt| fx.pk.try_encrypt(&pt, &mut fx.rng).expect("pk encrypt"))
        .collect()
}

/// Key holder side: decrypt each result ciphertext and poly-decode it to
/// centered coefficients.
fn decrypt_coefficients(fx: &Fixture, cts: &[Ciphertext]) -> Vec<Vec<i64>> {
    cts.iter()
        .map(|ct| {
            let pt: Plaintext = fx.sk.try_decrypt(ct).expect("fhe.rs decrypt");
            Vec::<i64>::try_decode(&pt, Encoding::poly()).expect("poly decode")
        })
        .collect()
}

/// The whole round trip: public `W`, encrypted `v`, out comes `W·v`.
fn evaluate(fx: &mut Fixture, plan: &MatmulPlan, w: &[Vec<i64>], v: &[i64]) -> Vec<i64> {
    let encoded = plan.encode_matrix(w, &fx.params).expect("encode W");
    let cts = encrypt_vector(fx, plan, v);
    let out = plan.apply(&encoded, &cts).expect("apply");
    plan.decode_results(&decrypt_coefficients(fx, &out))
        .expect("decode results")
}

fn pseudorandom_matrix(rows: usize, cols: usize, bound: i64, salt: u64) -> Vec<Vec<i64>> {
    let mut state = 0x9E3779B97F4A7C15u64 ^ salt;
    let span = (2 * bound + 1) as u64;
    (0..rows)
        .map(|_| {
            (0..cols)
                .map(|_| {
                    state = state
                        .wrapping_mul(6364136223846793005)
                        .wrapping_add(1442695040888963407);
                    ((state >> 33) % span) as i64 - bound
                })
                .collect()
        })
        .collect()
}

/// THE LOAD-BEARING TOOTH: a public matrix times a vector nobody decrypted,
/// through REAL fhe.rs encryption, equals the exact integer product — with no
/// rotation, no relinearization, and no key material beyond the encryption key.
#[test]
fn oracle_matvec_decrypts_to_the_exact_integer_product() {
    let mut fx = fixture(0xC0FFEE);
    // 8-bit weights × 8-bit activations at the capacity ceiling of 31.
    let plan = MatmulPlan::new(&fx.params, 64, 31, 128, 128).expect("plan");
    // One BLOCK; two ct×pt multiplies because the default SplitSign lift
    // evaluates W⁺ and W⁻ separately (see the module's measured correction).
    assert_eq!(plan.ct_pt_multiplications(), 2, "64 rows fit one block");
    let w = pseudorandom_matrix(64, 31, 128, 1);
    let v = pseudorandom_matrix(1, 31, 128, 2).remove(0);
    let got = evaluate(&mut fx, &plan, &w, &v);
    assert_eq!(got, plan.reference(&w, &v).unwrap());
    // Not vacuous: the answer is a genuine spread of nonzero values.
    assert!(got.iter().filter(|x| **x != 0).count() > 32);
    assert!(got.iter().any(|x| *x < 0) && got.iter().any(|x| *x > 0));
}

/// The 4-bit × 8-bit row of the quantization ladder at inner dim 512 — the
/// shape `notes/fhe-core-theory.md` names ("inner dim 512 exactly ⇒ 4-bit
/// weights × 8-bit activations, c ≤ 504")… except 512 > 504, so the plan MUST
/// refuse. It admits 504.
#[test]
fn oracle_the_512_shape_refuses_and_504_does_not() {
    let fx = fixture(0x512);
    let (w4, a8) = (signed_abs_bound(4), signed_abs_bound(8));
    assert_eq!(max_inner_dim(fx.params.plaintext(), 4, 8), 504);
    let err = MatmulPlan::new(&fx.params, 8, 512, w4, a8)
        .expect_err("inner dim 512 at 4×8 exceeds the derived ceiling of 504");
    assert!(
        matches!(err, CoeffMatmulError::CapacityExceeded { .. }),
        "{err}"
    );
    MatmulPlan::new(&fx.params, 8, 504, w4, a8).expect("504 is admitted");
}

/// The blocked/batched path end-to-end under encryption: neither dimension
/// divides its window, so both the right-most and bottom-most blocks are
/// zero-padded and results are accumulated across input ciphertexts.
#[test]
fn oracle_blocked_matvec_with_ragged_dimensions() {
    let mut fx = fixture(0x2A66ED);
    // 4-bit weights × 8-bit activations, inner dim 500 (under the 504 ceiling),
    // windows 300 × 10 = 3000 ≤ 4096. Neither 500/300 nor 13/10 divides.
    let plan = MatmulPlan::with_windows(&fx.params, 13, 500, 300, 10, 8, 128).expect("plan");
    assert_eq!(plan.input_blocks(), 2);
    assert_eq!(plan.output_blocks(), 2);
    assert_eq!(plan.ct_pt_multiplications(), 8);
    let w = pseudorandom_matrix(13, 500, 8, 3);
    let v = pseudorandom_matrix(1, 500, 128, 4).remove(0);
    assert_eq!(
        evaluate(&mut fx, &plan, &w, &v),
        plan.reference(&w, &v).unwrap()
    );
}

/// Boundary cases under encryption: a zero row, an all-negative row, and a
/// single row (`n_o = 1`), all in one evaluation.
#[test]
fn oracle_boundary_rows_under_encryption() {
    let mut fx = fixture(0xB0);
    let plan = MatmulPlan::new(&fx.params, 4, 31, 128, 128).expect("plan");
    let mut w = vec![vec![0i64; 31]; 4];
    w[1] = vec![-128i64; 31];
    w[2] = (0..31)
        .map(|j| if j % 2 == 0 { -128 } else { 127 })
        .collect();
    w[3][30] = -1;
    let v: Vec<i64> = (0..31).map(|j| (j as i64) - 5).collect();
    let reference = plan.reference(&w, &v).unwrap();
    assert_eq!(reference[0], 0, "zero row");
    assert_eq!(evaluate(&mut fx, &plan, &w, &v), reference);

    // n_o = 1: a single inner product, the degenerate shape.
    let single = MatmulPlan::new(&fx.params, 1, 31, 128, 128).expect("single-row plan");
    let w1 = vec![w[2].clone()];
    assert_eq!(
        evaluate(&mut fx, &single, &w1, &v),
        single.reference(&w1, &v).unwrap()
    );
}

/// Worst-case magnitudes under encryption: every entry at the declared bound.
/// This is the exact edge the capacity gate protects; if the gate were off by
/// one, fhe.rs decrypts a wrapped (wrong, well-formed) number here.
#[test]
fn oracle_worst_case_magnitudes_do_not_wrap_under_encryption() {
    let mut fx = fixture(0xEDDE);
    let plan = MatmulPlan::new(&fx.params, 8, 31, 128, 128).expect("plan");
    let w: Vec<Vec<i64>> = (0..8)
        .map(|i| vec![if i % 2 == 0 { 128i64 } else { -128 }; 31])
        .collect();
    let v = vec![-128i64; 31];
    let reference = plan.reference(&w, &v).unwrap();
    assert_eq!(reference[0], -(31 * 128 * 128));
    assert_eq!(evaluate(&mut fx, &plan, &w, &v), reference);
}

/// MEASURED: noise consumed by one rotation-free matmul, in bits of centered
/// noise (fhe.rs `measure_noise`), and the depth that remains afterwards —
/// demonstrated, not asserted, by performing a real ct×ct multiply on the
/// result.
#[test]
fn measured_noise_budget_and_remaining_depth() {
    let mut fx = fixture(0x0135);
    let plan = MatmulPlan::new(&fx.params, 64, 31, 128, 128).expect("plan");
    let w = pseudorandom_matrix(64, 31, 128, 7);
    let v = pseudorandom_matrix(1, 31, 128, 8).remove(0);

    let encoded = plan.encode_matrix(&w, &fx.params).expect("encode W");
    let cts = encrypt_vector(&mut fx, &plan, &v);
    let fresh = unsafe { fx.sk.measure_noise(&cts[0]) }.expect("fresh noise");
    let out = plan.apply(&encoded, &cts).expect("apply");
    let after = unsafe { fx.sk.measure_noise(&out[0]) }.expect("matmul noise");

    // Correctness first: a noise number about a wrong answer is worthless.
    assert_eq!(
        plan.decode_results(&decrypt_coefficients(&fx, &out))
            .unwrap(),
        plan.reference(&w, &v).unwrap()
    );

    // How much budget is left, in fhe.rs's own accounting: total bits of q.
    let log_q: f64 = fx.params.moduli().iter().map(|m| (*m as f64).log2()).sum();

    println!(
        "MEASURED coeff-matmul noise ledger @ N={}, log2 q={log_q:.2}, t={}:\n  \
         fresh ct noise           : {fresh} bits\n  \
         after 1 rotation-free matmul (inner dim {}, {} rows, {} ct×pt mults): {after} bits\n  \
         consumed by the matmul   : {} bits\n  \
         headroom to q/2 (~{:.0} bits): ~{:.0} bits",
        fx.params.degree(),
        fx.params.plaintext(),
        plan.inner_dim(),
        plan.rows(),
        plan.ct_pt_multiplications(),
        after as i64 - fresh as i64,
        log_q - 1.0,
        log_q - 1.0 - after as f64,
    );

    // The matmul must consume SOME noise (a zero-cost claim would mean the
    // measurement is not looking at the evaluated ciphertext) but must leave
    // the ciphertext far from the q/2 wall.
    assert!(
        after > fresh,
        "matmul must consume noise: {fresh} -> {after}"
    );
    assert!(
        (after as f64) < log_q - 1.0,
        "matmul result must still be decryptable: {after} vs log q {log_q}"
    );

    // DEPTH DEMONSTRATED, not estimated: perform a real ct×ct multiply +
    // relinearization ON the matmul result and check it still decrypts to the
    // same answer.
    //
    // The second operand is an encryption of the RING IDENTITY — the polynomial
    // `1`, i.e. `Encoding::poly()` of `[1]` — chosen precisely so the plaintext
    // product `A · 1 = A` cannot wrap mod t. That isolates the question under
    // test to the NOISE. (Note this deliberately does NOT go through
    // `bfv_mul::MulEngine`: its `BoundedCiphertext` bound is a per-SLOT SIMD
    // bound, and declaring one for a coefficient-encoded ciphertext would be a
    // false declaration, not a guard.)
    let rk = RelinearizationKey::new(&fx.sk, &mut fx.rng).expect("relin key");
    let mult = Multiplicator::default(&rk).expect("multiplicator");
    let one = Plaintext::try_encode(&[1i64], Encoding::poly(), &fx.params).expect("poly one");
    let ct_one: Ciphertext = fx.pk.try_encrypt(&one, &mut fx.rng).expect("encrypt one");
    let prod = mult
        .multiply(&out[0], &ct_one)
        .expect("ct x ct after the matmul");
    let after_mul = unsafe { fx.sk.measure_noise(&prod) }.expect("post-mul noise");
    println!(
        "  after a further ct×ct multiply + relin: {after_mul} bits (headroom ~{:.0})",
        log_q - 1.0 - after_mul as f64
    );

    let pt: Plaintext = fx.sk.try_decrypt(&prod).expect("decrypt after mul");
    let coeffs = Vec::<i64>::try_decode(&pt, Encoding::poly()).expect("poly decode");
    let round_tripped = plan.decode_results(&[coeffs]).expect("decode");
    assert_eq!(
        round_tripped,
        plan.reference(&w, &v).unwrap(),
        "the matmul result must survive one further ct×ct multiply"
    );
}

/// MEASURED: the theory note's central structural claim, tested directly —
/// "coefficient-encoded plaintext norm is the weight magnitude (2^7 for int8)
/// instead of ~t/2 (2^19) — a flat 12-bit gift per layer."
///
/// SAME weights, SAME ciphertext, ONE ct×pt multiply each; only the plaintext
/// ENCODING differs. The SIMD encoding runs an inverse NTT, which spreads small
/// weights into essentially uniform coefficients over `[0, t)`.
///
/// ⚠ SCOPE: this measures the PLAINTEXT-NORM term only. It is NOT a comparison
/// against the full slot/BSGS diagonal matmul, which additionally needs
/// rotations (and their key-switch noise) that this tree has no key material
/// for. The BSGS route's true cost is that term PLUS this one; the honest
/// reading of this number is "the coefficient route wins by at least this
/// much".
#[test]
fn measured_plaintext_norm_gift_vs_simd_encoding() {
    let mut fx = fixture(0x1201);
    let plan = MatmulPlan::new(&fx.params, 64, 31, 128, 128).expect("plan");
    let w = pseudorandom_matrix(64, 31, 128, 21);
    let v = pseudorandom_matrix(1, 31, 128, 22).remove(0);

    let cts = encrypt_vector(&mut fx, &plan, &v);
    let fresh = unsafe { fx.sk.measure_noise(&cts[0]) }.expect("fresh noise");
    let reference = plan.reference(&w, &v).unwrap();

    // (a) coefficient encoding, weights handed over DIRECTLY — every negative
    //     weight lifts to a ~t-size residue.
    let direct_plan = plan.clone().with_weight_lift(WeightLift::Direct);
    let direct_out = direct_plan
        .apply(
            &direct_plan.encode_matrix(&w, &fx.params).expect("encode W"),
            &cts,
        )
        .expect("apply");
    let direct_noise = unsafe { fx.sk.measure_noise(&direct_out[0]) }.expect("direct noise");

    // (b) coefficient encoding with the SPLIT-SIGN lift — every plaintext
    //     coefficient really is a weight magnitude.
    let split_out = plan
        .apply(&plan.encode_matrix(&w, &fx.params).expect("encode W"), &cts)
        .expect("apply");
    let split_noise = unsafe { fx.sk.measure_noise(&split_out[0]) }.expect("split noise");

    // (c) the SAME weight block, SIMD-encoded, one ct×pt multiply. The SIMD
    //     encoding runs an inverse NTT, spreading small weights over `[0, t)`.
    let block = &direct_plan
        .encode_matrix_coefficients(&w)
        .expect("coefficient block")[0][0];
    let simd_pt =
        Plaintext::try_encode(block, Encoding::simd(), &fx.params).expect("simd encode of W");
    let simd_out = &cts[0] * &simd_pt;
    let simd_noise = unsafe { fx.sk.measure_noise(&simd_out) }.expect("simd noise");

    // All three lifts must agree on the ANSWER; only the noise differs.
    assert_eq!(
        direct_plan
            .decode_results(&decrypt_coefficients(&fx, &direct_out))
            .unwrap(),
        reference
    );
    assert_eq!(
        plan.decode_results(&decrypt_coefficients(&fx, &split_out))
            .unwrap(),
        reference
    );

    println!(
        "MEASURED plaintext-norm term — same weights, same ciphertext, signed int8:\n  \
         fresh ct                                : {fresh} bits\n  \
         ct×pt, SIMD encoding                    : {simd_noise} bits (+{})\n  \
         ct×pt, coefficient / Direct lift        : {direct_noise} bits (+{})\n  \
         ct×pt, coefficient / SplitSign lift     : {split_noise} bits (+{})\n  \
         advantage of coefficient-Direct vs SIMD : {} bits  ⚠ the theory note predicts ~12\n  \
         advantage of SplitSign          vs SIMD : {} bits  (the ~12 recovered)",
        simd_noise as i64 - fresh as i64,
        direct_noise as i64 - fresh as i64,
        split_noise as i64 - fresh as i64,
        simd_noise as i64 - direct_noise as i64,
        simd_noise as i64 - split_noise as i64,
    );

    // The load-bearing assertion is about SplitSign, which is what the module
    // ships. The Direct-vs-SIMD gap is REPORTED, not asserted, precisely
    // because it measured ~1 bit rather than the predicted ~12.
    assert!(
        split_noise + 8 < simd_noise,
        "the split-sign coefficient lift must be substantially cheaper than SIMD: \
         split {split_noise} vs simd {simd_noise}"
    );
    assert!(
        split_noise < direct_noise,
        "the split-sign lift must beat the direct lift: {split_noise} vs {direct_noise}"
    );
}

/// MEASURED: how much multiplicative depth survives the matmul, established by
/// actually consuming it — chain ct×ct multiplies by the RING IDENTITY (the
/// polynomial `1`, so the plaintext never changes and never wraps) until the
/// decryption stops returning the matmul's answer. The last level that still
/// decrypts correctly IS the achievable depth.
#[test]
fn measured_achievable_depth_after_the_matmul() {
    let mut fx = fixture(0xDEB7);
    let plan = MatmulPlan::new(&fx.params, 64, 31, 128, 128).expect("plan");
    let w = pseudorandom_matrix(64, 31, 128, 31);
    let v = pseudorandom_matrix(1, 31, 128, 32).remove(0);
    let reference = plan.reference(&w, &v).unwrap();

    let encoded = plan.encode_matrix(&w, &fx.params).expect("encode W");
    let cts = encrypt_vector(&mut fx, &plan, &v);
    let mut acc = plan.apply(&encoded, &cts).expect("apply").remove(0);

    let rk = RelinearizationKey::new(&fx.sk, &mut fx.rng).expect("relin key");
    let mult = Multiplicator::default(&rk).expect("multiplicator");
    let one = Plaintext::try_encode(&[1i64], Encoding::poly(), &fx.params).expect("poly one");

    let mut depth = 0usize;
    let mut ladder = vec![(
        0usize,
        unsafe { fx.sk.measure_noise(&acc) }.unwrap_or(usize::MAX),
        true,
    )];
    for level in 1..=8 {
        let ct_one: Ciphertext = fx.pk.try_encrypt(&one, &mut fx.rng).expect("encrypt one");
        acc = match mult.multiply(&acc, &ct_one) {
            Ok(c) => c,
            Err(_) => break,
        };
        let noise = unsafe { fx.sk.measure_noise(&acc) }.unwrap_or(usize::MAX);
        let ok = plan
            .decode_results(&decrypt_coefficients(&fx, std::slice::from_ref(&acc)))
            .map(|r| r == reference)
            .unwrap_or(false);
        ladder.push((level, noise, ok));
        if ok {
            depth = level;
        } else {
            break;
        }
    }

    println!(
        "MEASURED depth after one rotation-free matmul (inner dim {}, {} rows, log2 q = 109):",
        plan.inner_dim(),
        plan.rows()
    );
    for (level, noise, ok) in &ladder {
        let noise_s = if *noise == usize::MAX {
            "n/a".to_string()
        } else {
            format!("{noise} bits")
        };
        println!(
            "  + {level} further ct×ct multiply(s): {noise_s:>9}  {}",
            if *ok {
                "DECRYPTS CORRECTLY"
            } else {
                "WRONG — budget exhausted"
            }
        );
    }
    println!("  ⇒ achievable ct×ct depth after the matmul: {depth}");

    assert!(
        depth >= 1,
        "the rotation-free matmul must leave at least one ct×ct multiply of budget"
    );
}

/// MEASURED: wall-clock of the evaluation phase (what a server pays per input),
/// separated from the one-time public-weight encoding.
#[test]
fn measured_wall_clock() {
    let mut fx = fixture(0x77A11);
    // A shape with real work in it: 512 rows at the 8-bit ceiling of 31, so 4
    // output blocks of 132 rows each.
    let plan = MatmulPlan::new(&fx.params, 512, 31, 128, 128).expect("plan");
    assert_eq!(plan.results_per_multiplication(), 132);
    assert_eq!(plan.ct_pt_multiplications(), 8);
    let w = pseudorandom_matrix(512, 31, 128, 11);
    let v = pseudorandom_matrix(1, 31, 128, 12).remove(0);

    let t0 = Instant::now();
    let encoded = plan.encode_matrix(&w, &fx.params).expect("encode W");
    let encode_weights = t0.elapsed();

    let cts = encrypt_vector(&mut fx, &plan, &v);

    let t1 = Instant::now();
    let out = plan.apply(&encoded, &cts).expect("apply");
    let evaluate_ms = t1.elapsed();

    let t2 = Instant::now();
    let decoded = decrypt_coefficients(&fx, &out);
    let decrypt = t2.elapsed();

    assert_eq!(
        plan.decode_results(&decoded).unwrap(),
        plan.reference(&w, &v).unwrap()
    );

    println!(
        "MEASURED coeff-matmul wall-clock ({}x{} @ 8-bit, {} ct×pt mults, {} in / {} out cts):\n  \
         encode public weights (ONE-TIME, reusable): {encode_weights:?}\n  \
         HOMOMORPHIC EVALUATE (per input)          : {evaluate_ms:?}\n  \
         decrypt + poly-decode                     : {decrypt:?}",
        plan.rows(),
        plan.inner_dim(),
        plan.ct_pt_multiplications(),
        plan.input_blocks(),
        plan.output_blocks(),
    );
}

/// MEASURED: the packing efficiency across the quantization ladder, and the
/// ciphertext-plaintext multiplication count for a fixed-size layer. This is
/// the number the "packing detail is the actual engineering" instruction is
/// about — a naive one-inner-product-per-multiply scheme sits at 1.
#[test]
fn measured_packing_efficiency_ladder() {
    let fx = fixture(0x9AC4);
    let t = fx.params.plaintext();
    println!("MEASURED packing ladder @ N={}, t={t}:", fx.params.degree());
    for (wb, ab) in [(8u32, 8u32), (4, 8), (4, 4)] {
        let ceiling = max_inner_dim(t, wb, ab);
        let inner = ceiling.min(fx.params.degree());
        let rows = 512usize;
        let plan = MatmulPlan::new(
            &fx.params,
            rows,
            inner,
            signed_abs_bound(wb),
            signed_abs_bound(ab),
        )
        .expect("plan");
        println!(
            "  {wb}-bit w × {ab}-bit a: inner-dim ceiling {ceiling:>5}  |  at inner dim \
             {inner:>4}: {:>4} results/multiply, slot use {:.1}%, {} ct×pt mults for {rows} rows",
            plan.results_per_multiplication(),
            plan.slot_utilization() * 100.0,
            plan.ct_pt_multiplications(),
        );
        assert!(plan.results_per_multiplication() >= 1);
    }
}
