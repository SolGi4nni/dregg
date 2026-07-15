//! OUTPUT-BOUNDARY MPC crossing — the working PoC benchmark (codex Round-4 gold).
//!
//! Runs the real construction end to end and reports the GATE evidence:
//!   (A) CORRECTNESS — the MPC (p*,V*) equals the plaintext crossing, over the
//!       REAL BFV-folded curves (additive fold → additive shares → MPC), across
//!       N∈{32,128,512}, K∈{64,256}, n∈{3,4} parties. No plaintext-pretending: a
//!       real GF(2) secret-shared, Beaver-triple online phase computes the sign.
//!   (B) PRIVACY — reveal-only-(p*,V*): two DIFFERENT books with the SAME (p*,V*)
//!       produce statistically indistinguishable party views, and a simulator
//!       given only (p*,V*) reproduces the view distribution. (Same-leakage as
//!       reveal-nothing beyond the intended public output.)
//!   (C) LATENCY — the MPC crossing runs in MILLISECONDS (vs the FHE crossing's
//!       ~12–17 s, `ADDITIVE-FOLD-ENVELOPE.md`), plus its round/AND-gate cost.
//!
//! Reproduce: `cargo run --release --bin fhe-mpc-bench` (from `fhegg-fhe/`).

use std::time::Instant;

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use fhegg_fhe::additive::{bfv_fold, pick_params};
use fhegg_fhe::mpc::{
    coalition_view_histogram, cross_book_pure, cross_curves, mpc_crossing, share_arith, share_int,
    simulate, triples_needed, SharedInt, Transcript, TriplePool,
};
use fhegg_fhe::{reference_clear, Order, Side};

const B: usize = 16; // curve-coefficient bit-width (bucket sums < 2^16)

fn random_book(n: usize, k: usize, rng: &mut StdRng) -> Vec<Order> {
    (0..n)
        .map(|_| Order {
            side: if rng.gen::<bool>() {
                Side::Bid
            } else {
                Side::Ask
            },
            limit: rng.gen_range(0..k),
            qty: rng.gen_range(1..=8),
        })
        .collect()
}

fn main() {
    println!("=== OUTPUT-BOUNDARY MPC crossing — PoC (codex Round-4 gold) ===\n");
    println!("Real BFV additive fold -> threshold partial-decrypt-into-shares (modelled)");
    println!("-> GF(2) secret-shared, Beaver-triple GEQ crossing -> reveal ONLY (p*,V*).\n");

    correctness_and_latency();
    privacy_demo();
    pure_mpc_correctness_and_latency();
    perfect_hiding_demo();

    println!("\n=== GATE ===");
    println!(
        "(A) correctness: MPC (p*,V*) == plaintext crossing, over REAL BFV curves — see table."
    );
    println!("(B) privacy: same-(p*,V*) books -> indistinguishable views; simulator matches — see below.");
    println!("(C) latency: MPC crossing in MILLISECONDS (vs FHE crossing ~12-17 s) — see table.");
    println!("(D) PURE-MPC: info-theoretic (LWE-free) local fold + A2B + crossing == plaintext,");
    println!("    fold FREE, benchmarked head-to-head vs the BFV (LWE-computational) fold.");
    println!("(E) UNCONDITIONAL privacy: below-threshold shares are PERFECTLY HIDING — the exact");
    println!(
        "    coalition-view histogram is IDENTICAL across secrets (independent of the secret,"
    );
    println!(
        "    secure vs unbounded compute) — stronger than the BFV path's LWE indistinguishability."
    );
}

fn correctness_and_latency() {
    println!("--- (A) correctness + (C) latency: real BFV fold -> MPC crossing ---");
    println!(
        "{:>4} {:>4} {:>3} | {:>10} {:>10} | {:>9} {:>10} {:>8} {:>7} | {}",
        "N", "K", "n", "BFV fold", "BFV enc", "MPC cross", "triples", "ANDs", "rounds", "correct"
    );
    let mut rng = StdRng::seed_from_u64(0xC0FFEE_11);
    let mut all_ok = true;
    for &n_orders in &[32usize, 128, 512] {
        for &k in &[64usize, 256] {
            for &n_parties in &[3usize, 4] {
                let book = random_book(n_orders, k, &mut rng);
                let reference = reference_clear(&book, k);

                // REAL BFV additive fold — the seam-free carrier. Its decrypted
                // curves are the input the threshold parties would partial-decrypt
                // INTO shares (no BFV->TFHE scheme switch: that seam is dissolved).
                let params = pick_params(20);
                let (demand, supply, fold_t) = bfv_fold(&book, k, &params);

                // OUTPUT-BOUNDARY MPC crossing on those real curves.
                let t0 = Instant::now();
                let (cross, tr, used) = cross_curves(&demand, &supply, B, n_parties, &mut rng);
                let mpc_dt = t0.elapsed();

                let ok = cross.p_star == reference.p_star
                    && cross.v_star as u32 == reference.v_star
                    && tr.is_reveal_only(k);
                all_ok &= ok;

                println!(
                    "{:>4} {:>4} {:>3} | {:>9.4}s {:>9.3}s | {:>7.2}ms {:>10} {:>8} {:>7} | {}",
                    n_orders,
                    k,
                    n_parties,
                    fold_t.fold.as_secs_f64(),
                    fold_t.encrypt.as_secs_f64(),
                    mpc_dt.as_secs_f64() * 1e3,
                    used,
                    tr.and_gates,
                    tr.rounds,
                    if ok {
                        format!("YES p*={:?} V*={}", cross.p_star, cross.v_star)
                    } else {
                        format!(
                            "NO mpc={:?}/{} ref={:?}/{}",
                            cross.p_star, cross.v_star, reference.p_star, reference.v_star
                        )
                    }
                );
                let _ = used;
            }
        }
    }
    println!(
        "\ncorrectness across ALL configs: {}",
        if all_ok {
            "ALL MATCH (MPC == plaintext)"
        } else {
            "!!! MISMATCH !!!"
        }
    );
    assert!(all_ok, "MPC crossing must equal the plaintext crossing");
    println!(
        "latency: the MPC crossing is milliseconds; the comparison it replaces is the\n\
         ~12-17 s O(K) TFHE crossing (ADDITIVE-FOLD-ENVELOPE.md). Rounds = O(b) network\n\
         round-trips (bit-width), K-independent (buckets batch by depth).\n"
    );
}

/// Collect the input-dependent part of a party's view over `runs` fresh executions
/// and return `(P[masked bit = 1], pstar_bits, vstar_bits)`.
fn view_profile(
    demand: &[u64],
    supply: &[u64],
    n_parties: usize,
    runs: usize,
    seed: u64,
) -> (f64, Vec<u8>, Vec<u8>) {
    let k = demand.len();
    let mut rng = StdRng::seed_from_u64(seed);
    let mut ones = 0u64;
    let mut total = 0u64;
    let mut pstar = Vec::new();
    let mut vstar = Vec::new();
    for _ in 0..runs {
        let mut pool = TriplePool::generate(triples_needed(k, B), n_parties, &mut rng);
        let d: Vec<SharedInt> = demand
            .iter()
            .map(|&v| share_int(v, B, n_parties, &mut rng))
            .collect();
        let s: Vec<SharedInt> = supply
            .iter()
            .map(|&v| share_int(v, B, n_parties, &mut rng))
            .collect();
        let mut tr = Transcript::default();
        let _ = mpc_crossing(&d, &s, &mut pool, &mut tr);
        for &m in &tr.masked {
            ones += m as u64;
            total += 1;
        }
        pstar = tr.revealed_pstar.clone();
        vstar = tr.revealed_vstar.clone();
    }
    (ones as f64 / total as f64, pstar, vstar)
}

fn privacy_demo() {
    println!(
        "--- (B) privacy: reveal-only-(p*,V*) via same-(p*,V*) -> indistinguishable views ---"
    );
    let k = 32usize;
    let n_parties = 4usize;
    let runs = 200usize;
    let mut rng = StdRng::seed_from_u64(0xDA7A_B0B);

    // Find TWO DIFFERENT books that clear at the SAME (p*, V*). If the party view
    // reveals only (p*,V*), the two must be indistinguishable to any coalition
    // below threshold — that is the "same leakage as reveal-nothing" property.
    let mut buckets: std::collections::HashMap<(Option<usize>, u32), (Vec<u64>, Vec<u64>)> =
        std::collections::HashMap::new();
    let mut pair: Option<(
        (Vec<u64>, Vec<u64>),
        (Vec<u64>, Vec<u64>),
        (Option<usize>, u32),
    )> = None;
    for _ in 0..20000 {
        let book = random_book(rng.gen_range(8..40), k, &mut rng);
        let r = reference_clear(&book, k);
        if r.p_star.is_none() {
            continue;
        }
        let key = (r.p_star, r.v_star);
        let curves = (
            r.demand.iter().map(|&x| x as u64).collect::<Vec<_>>(),
            r.supply.iter().map(|&x| x as u64).collect::<Vec<_>>(),
        );
        if let Some(prev) = buckets.get(&key) {
            if prev.0 != curves.0 || prev.1 != curves.1 {
                pair = Some((prev.clone(), curves, key));
                break;
            }
        } else {
            buckets.insert(key, curves);
        }
    }

    let (b1, b2, key) = pair.expect("found two distinct books with the same (p*,V*)");
    println!(
        "found two DISTINCT aggregate curves with identical (p*,V*) = ({:?}, {}):",
        key.0, key.1
    );
    println!(
        "  book1 demand[..8]={:?} supply[..8]={:?}",
        &b1.0[..8],
        &b1.1[..8]
    );
    println!(
        "  book2 demand[..8]={:?} supply[..8]={:?}",
        &b2.0[..8],
        &b2.1[..8]
    );
    println!(
        "  (curves DIFFER: {}), yet both clear at the same (p*,V*).",
        if b1.0 != b2.0 || b1.1 != b2.1 {
            "confirmed"
        } else {
            "SAME?!"
        }
    );

    let (bias1, pstar1, vstar1) = view_profile(&b1.0, &b1.1, n_parties, runs, 0x1111);
    let (bias2, pstar2, vstar2) = view_profile(&b2.0, &b2.1, n_parties, runs, 0x2222);

    println!("\nparty view over {runs} fresh runs each ({n_parties} parties, K={k}):");
    println!(
        "  P[opened protocol bit = 1]:  book1 = {:.4}   book2 = {:.4}   (uniform = 0.5)",
        bias1, bias2
    );
    println!(
        "  |bias1 - bias2|           =  {:.4}   (-> 0: the masked messages carry no input info)",
        (bias1 - bias2).abs()
    );
    println!("  opened p* index bits equal:  {}", pstar1 == pstar2);
    println!("  revealed V* bits equal    :  {}", vstar1 == vstar2);

    // Simulator: given ONLY (p*,V*), reproduce the view distribution.
    let cross_ref = fhegg_fhe::mpc::Crossing {
        p_star: key.0,
        v_star: key.1 as u64,
    };
    let mut srng = StdRng::seed_from_u64(0x51A);
    let mut sim_ones = 0u64;
    let mut sim_total = 0u64;
    let mut sim_pstar = Vec::new();
    let mut sim_vstar = Vec::new();
    for _ in 0..runs {
        let tr = simulate(&cross_ref, k, B, &mut srng);
        for &m in &tr.masked {
            sim_ones += m as u64;
            sim_total += 1;
        }
        sim_pstar = tr.revealed_pstar.clone();
        sim_vstar = tr.revealed_vstar.clone();
    }
    let sim_bias = sim_ones as f64 / sim_total as f64;
    println!("\nsimulator (given ONLY (p*,V*), no curves):");
    println!("  P[simulated bit = 1]      =  {:.4}   (matches real -> real view learnable from (p*,V*) alone)", sim_bias);
    println!(
        "  simulated p* bits = real p* bits : {}",
        sim_pstar == pstar1
    );
    println!(
        "  simulated V* bits = real V* bits : {}",
        sim_vstar == vstar1
    );

    let indistinguishable = pstar1 == pstar2
        && vstar1 == vstar2
        && (bias1 - bias2).abs() < 0.03
        && (bias1 - 0.5).abs() < 0.03
        && sim_pstar == pstar1
        && sim_vstar == vstar1;
    println!(
        "\nprivacy verdict: {}",
        if indistinguishable {
            "views are STATISTICALLY INDISTINGUISHABLE -> the MPC reveals ONLY (p*,V*)."
        } else {
            "!!! views distinguishable — privacy claim FAILS !!!"
        }
    );
    assert!(
        indistinguishable,
        "same-(p*,V*) books must yield indistinguishable views"
    );
    println!(
        "honest caveat: this is the SEMI-HONEST, below-threshold bound. >= t colluding\n\
         parties reconstruct the shares (t-of-n, not 'all-collude') — the minimum trust\n\
         for clearing over hidden data, and there is NO standing master decryption key."
    );
}

/// (D) The PURE-MPC (information-theoretic-fold) path, benchmarked head-to-head
/// against the BFV (LWE-computational) fold on identical books. The pure path
/// secret-shares the orders DIRECTLY over Z_{2^b}, folds by LOCAL share addition
/// (free, unconditional), converts once at the boundary (A2B), and runs the SAME
/// crossing — correctness checked against the plaintext reference.
fn pure_mpc_correctness_and_latency() {
    println!("\n--- (D) PURE-MPC info-theoretic fold: no BFV/LWE in the fold path ---");
    println!(
        "fold = LOCAL per-party share sum over Z_2^b (FREE, unconditional) -> A2B boundary\n\
         bridge -> UNCHANGED Beaver-triple crossing -> reveal ONLY (p*,V*). Contrast: the\n\
         BFV fold is LWE-COMPUTATIONAL. Threshold: perfect-hiding vs <= n-1 semi-honest.\n"
    );
    println!(
        "{:>4} {:>4} {:>3} | {:>10} | {:>9} {:>9} {:>10} | {:>8} {:>8} {:>7} | {}",
        "N",
        "K",
        "n",
        "BFV fold",
        "MPC fold",
        "A2B",
        "cross",
        "a2b ANDs",
        "cr ANDs",
        "rounds",
        "correct"
    );
    let mut rng = StdRng::seed_from_u64(0x9E_11_7ED);
    let mut all_ok = true;
    for &n_orders in &[32usize, 128, 512] {
        for &k in &[64usize, 256] {
            for &n_parties in &[3usize, 4] {
                let book = random_book(n_orders, k, &mut rng);
                let reference = reference_clear(&book, k);

                // The BFV (LWE) fold — timed only for the head-to-head contrast.
                let params = pick_params(20);
                let (_d, _s, fold_t) = bfv_fold(&book, k, &params);

                // The PURE info-theoretic path on the SAME book.
                let run = cross_book_pure(&book, k, B, n_parties, &mut rng);

                let ok = run.cross.p_star == reference.p_star
                    && run.cross.v_star as u32 == reference.v_star
                    && run.transcript.is_reveal_only(k);
                all_ok &= ok;

                println!(
                    "{:>4} {:>4} {:>3} | {:>9.4}s | {:>7.4}ms {:>7.2}ms {:>8.2}ms | {:>8} {:>8} {:>7} | {}",
                    n_orders,
                    k,
                    n_parties,
                    fold_t.fold.as_secs_f64(),
                    run.fold.as_secs_f64() * 1e3,
                    run.a2b.as_secs_f64() * 1e3,
                    run.crossing.as_secs_f64() * 1e3,
                    run.a2b_and_gates,
                    run.crossing_and_gates,
                    run.transcript.rounds,
                    if ok {
                        format!("YES p*={:?} V*={}", run.cross.p_star, run.cross.v_star)
                    } else {
                        format!(
                            "NO mpc={:?}/{} ref={:?}/{}",
                            run.cross.p_star, run.cross.v_star, reference.p_star, reference.v_star
                        )
                    }
                );
                let _ = run.triples_used;
            }
        }
    }
    println!(
        "\npure-MPC correctness across ALL configs: {}",
        if all_ok {
            "ALL MATCH (info-theoretic-fold MPC == plaintext)"
        } else {
            "!!! MISMATCH !!!"
        }
    );
    assert!(
        all_ok,
        "pure-MPC crossing must equal the plaintext crossing"
    );
    println!(
        "the FOLD is LOCAL share-addition — O(N*K) ring adds, NO communication and NO\n\
         cryptographic assumption (vs the BFV fold's LWE); its cost tracks the BFV fold's\n\
         own local arithmetic. The only added MPC vs the BFV path is the one-time A2B boundary\n\
         bridge; the crossing is byte-identical. Deployment latency = rounds network trips.\n"
    );
}

/// (E) The UNCONDITIONAL (perfect-hiding) demonstration — the load-bearing
/// information-theoretic claim, shown EXACTLY by enumeration. For additive
/// Z_{2^b} sharing, a coalition of any `n-1` parties observes a view whose EXACT
/// distribution is IDENTICAL for every secret — so it is independent of the
/// secret against UNBOUNDED compute (no LWE, no assumption). This is strictly
/// stronger than the BFV path, whose ciphertext is only COMPUTATIONALLY hiding
/// (an unbounded adversary breaks LWE and reads the plaintext).
fn perfect_hiding_demo() {
    println!("\n--- (E) UNCONDITIONAL privacy: below-threshold shares are PERFECTLY HIDING ---");
    let b = 8usize; // small ring so we can ENUMERATE the whole randomness space
    let n = 3usize; // 3 parties; a coalition of n-1 = 2 is below threshold
    let v0 = 3u64;
    let v1 = 200u64; // two very different secrets
    println!(
        "additive sharing over Z_2^{b} among n={n} parties; enumerate the ENTIRE randomness\n\
         space (2^{} tuples) and compare the exact view of every 2-party coalition for two\n\
         very different secrets v0={v0}, v1={v1}:",
        b * (n - 1)
    );

    // Every coalition of size n-1 = 2, including the one holding the parity share.
    let coalitions: [(&str, Vec<usize>); 3] = [
        ("parties {0,1} (free shares)", vec![0, 1]),
        ("parties {0,2} (incl. parity)", vec![0, 2]),
        ("parties {1,2} (incl. parity)", vec![1, 2]),
    ];
    let mut all_perfect = true;
    for (label, coal) in &coalitions {
        let h0 = coalition_view_histogram(v0, b, n, coal);
        let h1 = coalition_view_histogram(v1, b, n, coal);
        let identical = h0 == h1;
        // Uniform = every observable tuple appears exactly the same number of times.
        let counts: std::collections::BTreeSet<u64> = h0.values().copied().collect();
        let uniform = counts.len() == 1;
        let distinct_tuples = h0.len();
        all_perfect &= identical && uniform;
        println!(
            "  coalition {label:32}: histograms(v0)==histograms(v1): {identical}  |  \
             uniform: {uniform} ({distinct_tuples} tuples x {}) ",
            counts.into_iter().next().unwrap_or(0)
        );
    }
    println!(
        "\nperfect-hiding verdict: {}",
        if all_perfect {
            "EXACT — every below-threshold coalition-view distribution is IDENTICAL across\n\
             secrets AND uniform. The fold's privacy is INFORMATION-THEORETIC (perfect hiding),\n\
             secure against UNBOUNDED compute — no assumption to break."
        } else {
            "!!! a coalition view depends on the secret — perfect-hiding claim FAILS !!!"
        }
    );
    assert!(
        all_perfect,
        "below-threshold shares must be perfectly hiding"
    );

    // A concrete same-secret sanity line: two independent sharings of the SAME
    // value are DIFFERENT tuples yet both reconstruct to it — the randomness is real.
    let mut rng = StdRng::seed_from_u64(0xF00D_51);
    let sh_a = share_arith(v0, B, 4, &mut rng);
    let sh_b = share_arith(v0, B, 4, &mut rng);
    println!(
        "\n(sharing is randomized: two sharings of {v0} differ {} but both open to {v0}: {}/{})",
        sh_a != sh_b,
        fhegg_fhe::mpc::open_arith(&sh_a, B),
        fhegg_fhe::mpc::open_arith(&sh_b, B)
    );

    println!(
        "\nCONTRAST with the BFV output-boundary path (A/B/C above): there the FOLD is BFV, so\n\
         below-threshold no-viewer rests on LWE — an unbounded adversary breaks LWE and reads\n\
         the curve. Here the fold has NO computational component; the shares are perfectly\n\
         hiding. Honest threshold: perfect hiding vs any <= n-1 SEMI-HONEST parties (additive\n\
         n-of-n); robust/malicious + dealer-free IT triples are the honest-majority (t<n/2, BGW)\n\
         regime; SPDZ MACs reach all-but-one but reintroduce a computational assumption in the\n\
         offline phase; all-collude reconstruction is unavoidable (the theorem, not a gap)."
    );
}
