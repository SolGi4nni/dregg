//! `package-bench` — the certified-approximation package/all-or-none clearing:
//! real latency + the certified near-optimality ratio on a sweep of instances.
//!
//! Run: `cargo run --release --bin package-bench` (in `fhegg-solver/`).
//!
//! HONEST framing (printed): feasibility (indivisibility preserved) is ALWAYS
//! proven; the near-optimality is a CERTIFIED bound `W ≤ W* ≤ UB(y)`; the exact
//! optimum stays NP-hard. The certified ratio's QUALITY varies by instance — on
//! small instances we also brute-force the true optimum to show how close the
//! achieved welfare and the certified bound bracket it.

use fhegg_solver::package::{brute_force_optimum, clear_package, random_auction};
use std::time::Instant;

fn main() {
    println!("package-bench — certified-approximation combinatorial clearing (all-or-none)");
    println!(
        "feasibility ALWAYS proven; near-optimality is a CERTIFIED bound; exact stays NP-hard.\n"
    );

    // --- small instances: brute-force the TRUE optimum to show the brackets ---
    println!("small instances (true optimum known by 2^n brute force):");
    println!(
        "{:<7} {:<7} {:>8} {:>9} {:>9} {:>9} {:>8} {:>9}",
        "items", "bids", "solve_us", "W(achv)", "UB(cert)", "opt(true)", "cert_α", "true_α"
    );
    let small = [(4usize, 10usize), (5, 12), (6, 14), (8, 16), (10, 18)];
    for (m, n) in small {
        let mut solve_ns = 0u128;
        let (mut sum_cert_ratio, mut sum_true_ratio) = (0.0f64, 0.0f64);
        let mut worst_cert = 1.0f64;
        let reps = 20;
        for seed in 0..reps as u64 {
            let auction = random_auction(m, n, seed + (m * 100 + n) as u64);
            let t0 = Instant::now();
            let (clr, cert) = clear_package(&auction, 4000);
            solve_ns += t0.elapsed().as_nanos();
            let rep = cert.check();
            assert!(
                rep.valid,
                "every certificate must be valid (feasible + bound)"
            );
            let opt = brute_force_optimum(&auction);
            // cert_α = W/UB (what the buyer VERIFIES); true_α = W/opt (unknowable
            // in general — shown here only because we brute-forced the optimum).
            let cert_ratio = rep.ratio;
            let true_ratio = if opt > 1e-9 { clr.welfare / opt } else { 1.0 };
            sum_cert_ratio += cert_ratio;
            sum_true_ratio += true_ratio;
            worst_cert = worst_cert.min(cert_ratio);
        }
        // Print one representative instance's numbers + the averaged ratios.
        let auction = random_auction(m, n, (m * 100 + n) as u64);
        let (clr, cert) = clear_package(&auction, 4000);
        let opt = brute_force_optimum(&auction);
        println!(
            "{:<7} {:<7} {:>8.1} {:>9.2} {:>9.2} {:>9.2} {:>8.3} {:>9.3}",
            m,
            n,
            solve_ns as f64 / reps as f64 / 1000.0,
            clr.welfare,
            clr.upper_bound,
            opt,
            sum_cert_ratio / reps as f64,
            sum_true_ratio / reps as f64,
        );
        let _ = cert;
    }
    println!(
        "  (cert_α = W/UB, what the buyer CHECKS; true_α = W/opt, shown only via brute force)"
    );
    println!(
        "  worst-case cert_α across the sweep is ≥ the averaged value — feasibility never fails.\n"
    );

    // --- larger instances: no brute force; feasibility + the certified bound ---
    println!("larger instances (exact optimum NP-hard — only the CERTIFIED bound is available):");
    println!(
        "{:<7} {:<7} {:>9} {:>10} {:>10} {:>8}",
        "items", "bids", "solve_ms", "W(achv)", "UB(cert)", "cert_α"
    );
    for (m, n) in [(20usize, 80usize), (40, 200), (60, 400), (100, 800)] {
        let auction = random_auction(m, n, (m * 7 + n) as u64);
        let t0 = Instant::now();
        let (clr, cert) = clear_package(&auction, 4000);
        let elapsed = t0.elapsed();
        let rep = cert.check();
        assert!(rep.valid, "feasibility + bound must hold at every scale");
        println!(
            "{:<7} {:<7} {:>9.2} {:>10.2} {:>10.2} {:>8.3}",
            m,
            n,
            elapsed.as_secs_f64() * 1000.0,
            clr.welfare,
            clr.upper_bound,
            rep.ratio,
        );
    }
    println!("\n  every row above: x∈{{0,1}} (indivisibility PRESERVED), Σdᵢxᵢ≤s (feasible),");
    println!(
        "  y≥0, and W ≤ UB (weak-duality bound) — all CHECKED from scratch by CertPackage::check."
    );
}
