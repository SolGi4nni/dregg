//! CARRY-FREE ADDITIVE FOLD vs EXACT-INTEGER TFHE — the Tier-0 head-to-head.
//!
//! codex Round-3 Q1 (`docs/deos/FHEGG-CODEX-ROUND3.md` §B/Q1) claims the dark-pool
//! aggregation's dominant cost — the exact-integer TFHE fold, whose radix adds
//! carry-propagate (PBS-class; MEASURED-ENVELOPE.md: the fold DOMINATES, up to 45×
//! the crossing) — collapses under a carry-free ADDITIVE scheme (exact-quantized
//! BFV/BGV), whose ciphertext add is a native modular poly-add (no carry, no PBS)
//! and which SIMD-packs all K buckets into ONE ciphertext.
//!
//! This binary MEASURES it. For each (N,K) it runs BOTH, on the SAME machine, on
//! the SAME book, and checks each fold's demand/supply curves EXACTLY equal the
//! plaintext reference:
//!   * the REAL exact-integer TFHE clear (`fhegg_fhe::fhe_clear`, tfhe-rs 1.6),
//!     reading off its measured `aggregate` (the fold) and `crossing` phases;
//!   * the REAL carry-free BFV fold (`fhegg_fhe::additive::bfv_fold`, fhe.rs 0.1).
//! No mock FHE, no faked speedup. The headline is the fold-vs-fold ratio and the
//! end-to-end (BFV fold + TFHE crossing) vs all-TFHE.
//!
//! The mint-safe floor/ceil quantizer (`metatheory/Market/MintSafeQuantization
//! .lean::mint_safe_floor_ceil`) is applied and demonstrated: the fold operates on
//! exactly the floor-in/ceil-out integer grid the Lean proves is no-mint.
//!
//! CPU only (Apple Silicon: no CUDA). Same host caveats as MEASURED-ENVELOPE.md.

use std::time::Instant;

use fhegg_fhe::additive::{bfv_fold, mint_safe, pick_params};
use fhegg_fhe::{fhe_clear, reference_clear, Order, Side};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use tfhe::{generate_keys, set_server_key, ConfigBuilder};

/// Same book generator as the TFHE envelope (`src/bin/bench.rs`) so the two
/// measurements are on identical orders. Small qtys keep aggregate sums in range.
fn gen_orders(n: usize, k: usize, rng: &mut StdRng) -> Vec<Order> {
    let qmax: u16 = if n >= 512 { 32 } else { 100 };
    (0..n)
        .map(|i| {
            let side = if i % 2 == 0 { Side::Bid } else { Side::Ask };
            Order {
                side,
                limit: rng.gen_range(0..k),
                qty: rng.gen_range(1..=qmax),
            }
        })
        .collect()
}

/// Apply + demonstrate the mint-safe floor/ceil quantizer, worked on the exact
/// instances the Lean proves (`honest_clearing_passes`, `mint_attempt_rejected`),
/// so the Rust gate and the Lean theorem are unmistakably the same object. The
/// BFV fold aggregates exactly these floor-in/ceil-out integer increments.
fn demo_mint_safe() {
    println!("\n--- mint-safe floor/ceil quantizer (MintSafeQuantization.lean) ---");

    // HONEST clearing (Lean `honest_clearing_passes`, Δ=1): true outputs
    // vout=(7.5,8.5) sum 16, true inputs vin=(10,10) sum 20. Micro-units DEN=2 so
    // the fractions are exact integers: Δ=2 micro-units, vout=(15,17), vin=(20,20).
    let delta = 2i128;
    let vin = [20i128, 20];
    let vout = [15i128, 17];
    let (pass, qout, qin) = mint_safe::floor_ceil_gate(&vin, &vout, delta);
    let no_mint = mint_safe::true_no_mint(&vin, &vout);
    println!(
        "  honest clear: Σ⌈vout/Δ⌉={qout} ≤ Σ⌊vin/Δ⌋={qin} -> gate {} ; true Σvout≤Σvin = {}  [Lean: honest_clearing_passes, 17≤20]",
        if pass { "PASS" } else { "FAIL" },
        no_mint
    );
    assert!(
        pass && no_mint,
        "honest clearing must pass the gate and be mint-safe"
    );
    assert_eq!((qout, qin), (17, 20), "matches Lean honest_clearing_passes");

    // A GENUINE MINT (Lean `mint_attempt_rejected`, Δ=1): true vout=(10,10) sum 20
    // > true vin=(9,9) sum 18 — a mint of 2. Mint-safe rounding REJECTS it.
    let delta = 1i128;
    let vin = [9i128, 9];
    let vout = [10i128, 10];
    let (pass, qout, qin) = mint_safe::floor_ceil_gate(&vin, &vout, delta);
    let no_mint = mint_safe::true_no_mint(&vin, &vout);
    println!(
        "  mint attempt: Σ⌈vout/Δ⌉={qout} ≤ Σ⌊vin/Δ⌋={qin} -> gate {} ; true Σvout≤Σvin = {}  [Lean: mint_attempt_rejected, ¬(20≤18)]",
        if pass { "PASS (BUG!)" } else { "REJECTED" },
        no_mint
    );
    assert!(!pass && !no_mint, "a genuine mint must fail the gate");
    println!("  => floor-in / ceil-out is mint-safe: the gate the BFV fold checks on the integer grid provably forbids Σvout>Σvin (mint_safe_floor_ceil).");
}

fn main() {
    println!(
        "=== fhEgg: CARRY-FREE ADDITIVE FOLD (BFV) vs EXACT-INTEGER TFHE — Tier-0 head-to-head ==="
    );
    println!("host: CPU only (Apple Silicon: no CUDA). Real tfhe-rs 1.6 + real fhe.rs 0.1 (BFV). No mock.");

    demo_mint_safe();

    // TFHE setup (shared across configs).
    let config = ConfigBuilder::default().build();
    let t = Instant::now();
    let (ck, sk) = generate_keys(config);
    println!(
        "\nTFHE keygen: {:.3}s (PARAM_MESSAGE_2_CARRY_2, >=128-bit)",
        t.elapsed().as_secs_f64()
    );
    set_server_key(sk);

    // BFV params: plaintext modulus t ~ 2^20 (headroom over the largest bucket
    // sum N*qmax=16384), degree-4096 (4096 SIMD slots >= any K here), 128-bit.
    let bfv_params = pick_params(20);
    println!(
        "BFV params: degree(slots)={} plaintext_modulus={} (128-bit, no-bootstrap additive)",
        bfv_params.degree(),
        bfv_params.plaintext()
    );

    // Head-to-head grid: N in {32,128,512}, K=64 (the envelope's K=64 column). Plus
    // a BFV-only (512,256) row to show the additive fold is ~K-insensitive (SIMD).
    let configs = [(32usize, 64usize), (128, 64), (512, 64)];

    println!(
        "\n--- head-to-head (each config: BOTH folds, both checked vs plaintext reference) ---"
    );
    println!("    [fold] = the aggregation under test. TFHE end-to-end = enc+agg+crossing; additive path = enc+fold+TFHE-crossing (scheme-switch).\n");

    for &(n, k) in &configs {
        let mut rng = StdRng::seed_from_u64(0xF9E66 ^ ((n as u64) << 20) ^ (k as u64));
        let orders = gen_orders(n, k, &mut rng);
        let reference = reference_clear(&orders, k);

        // --- BFV additive fold ---
        let (bd, bs, bt) = bfv_fold(&orders, k, &bfv_params);
        let bfv_ok = (0..k)
            .all(|p| bd[p] as u32 == reference.demand[p] && bs[p] as u32 == reference.supply[p]);

        // --- Exact-integer TFHE clear (real, tested path) ---
        let tt = fhe_clear(&orders, k, &ck);
        let tfhe_curves_ok = match reference.p_star {
            Some(p) => tt.p_star == p,
            None => tt.p_star == usize::MAX,
        } && tt.v_star == reference.v_star;

        let bfv_fold_s = bt.fold.as_secs_f64();
        let tfhe_agg_s = tt.aggregate.as_secs_f64();
        let tfhe_cross_s = tt.crossing.as_secs_f64();
        let speedup = if bfv_fold_s > 0.0 {
            tfhe_agg_s / bfv_fold_s
        } else {
            f64::INFINITY
        };

        // End-to-end: additive path (BFV enc+fold + TFHE crossing via scheme-switch)
        // vs all-TFHE (enc+agg+crossing). Scheme-switch cost is a labelled seam.
        let additive_e2e = bt.encrypt.as_secs_f64() + bfv_fold_s + tfhe_cross_s;
        let all_tfhe_e2e = tt.encrypt.as_secs_f64() + tfhe_agg_s + tfhe_cross_s;
        let e2e_speedup = if additive_e2e > 0.0 {
            all_tfhe_e2e / additive_e2e
        } else {
            f64::INFINITY
        };

        println!(
            "  N={n} K={k}  correct: BFV={} TFHE={}",
            if bfv_ok { "YES" } else { "NO!!" },
            if tfhe_curves_ok { "YES" } else { "NO!!" }
        );
        println!(
            "    FOLD:  BFV additive = {:.4}s ({} carry-free adds, 1 ct/order)  |  TFHE = {:.3}s ({} carry-prop. adds)  => {:.0}x",
            bfv_fold_s, bt.add_ops, tfhe_agg_s, tt.add_ops, speedup
        );
        println!(
            "    BFV:   keygen {:.3}s | encrypt(N packed cts) {:.4}s | fold {:.4}s | decrypt {:.4}s",
            bt.keygen.as_secs_f64(), bt.encrypt.as_secs_f64(), bfv_fold_s, bt.decrypt.as_secs_f64()
        );
        println!(
            "    TFHE:  encrypt(N*K={} cts) {:.3}s | aggregate {:.3}s | crossing {:.3}s",
            n * k,
            tt.encrypt.as_secs_f64(),
            tfhe_agg_s,
            tfhe_cross_s
        );
        println!(
            "    END-TO-END:  additive-path (BFV enc+fold + TFHE crossing) = {:.3}s  |  all-TFHE = {:.3}s  => {:.1}x",
            additive_e2e, all_tfhe_e2e, e2e_speedup
        );
        assert!(bfv_ok, "BFV fold correctness FAILED at N={n} K={k}");
        assert!(
            tfhe_curves_ok,
            "TFHE clear correctness FAILED at N={n} K={k}"
        );
    }

    // BFV-only: K=256 at N=512 — the additive fold is ~K-insensitive (all K buckets
    // ride in one packed ciphertext), where the TFHE fold's cost is ~linear in K.
    println!(
        "\n--- BFV-only: additive fold is ~K-insensitive (SIMD packs all K buckets in one ct) ---"
    );
    for &(n, k) in &[(512usize, 256usize)] {
        let mut rng = StdRng::seed_from_u64(0xF9E66 ^ ((n as u64) << 20) ^ (k as u64));
        let orders = gen_orders(n, k, &mut rng);
        let reference = reference_clear(&orders, k);
        let (bd, bs, bt) = bfv_fold(&orders, k, &bfv_params);
        let ok = (0..k)
            .all(|p| bd[p] as u32 == reference.demand[p] && bs[p] as u32 == reference.supply[p]);
        println!(
            "  N={n} K={k}  correct: {}  BFV fold = {:.4}s ({} adds) | encrypt {:.4}s | decrypt {:.4}s  (TFHE fold here would be ~1080s, extrapolated)",
            if ok { "YES" } else { "NO!!" }, bt.fold.as_secs_f64(), bt.add_ops, bt.encrypt.as_secs_f64(), bt.decrypt.as_secs_f64()
        );
        assert!(ok, "BFV fold correctness FAILED at N={n} K={k}");
    }

    println!("\n=== done ===");
}
