//! Price-Cert benchmark — REAL runs, honest numbers (the fhIR-1 runner).
//!
//! Two members of the derivatives family, both certified through the SAME
//! verify-not-find discipline:
//!   - the state-price LP (European / basket / Asian): solve `max hᵀπ s.t. Hπ=a`
//!     by two-phase simplex, emit the tight `(π, y)` CertPrice;
//!   - the Snell-envelope LP (American / Bermudan): backward-induct the
//!     recombining binomial tree, emit the CertSnell.
//!
//! Reports solve latency, certificate-CHECK latency, the duality gap / value, and
//! the certificate validity — for a range of sizes.
//!
//! Usage: `cargo run --release --bin pricecert-bench` (in `fhegg-solver/`).

use fhegg_solver::pricecert::{
    american_put_binomial, solve_price_cert, solve_snell_cert, CertPrice, Market, PriceOutcome,
};
use std::time::Instant;

fn best_of<F: FnMut()>(reps: u32, mut f: F) -> f64 {
    f(); // warmup
    let mut best = f64::MAX;
    for _ in 0..reps {
        let t0 = Instant::now();
        f();
        best = best.min(t0.elapsed().as_secs_f64());
    }
    best
}

/// A deterministic, CONSISTENT (arbitrage-free) incomplete market: random
/// nonneg state prices `π*`, a nonneg instrument grid `H`, marks `a = H π*`
/// (so consistency holds by construction), and a random product payoff `h`.
fn gen_market(n_scenarios: usize, n_instruments: usize, seed: u64) -> Market {
    // A tiny deterministic LCG — no rng dependency needed for a fixed grid.
    let mut st = seed.wrapping_mul(0x9E3779B97F4A7C15) | 1;
    let mut next = || {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        (st >> 11) as f64 / (1u64 << 53) as f64 // in [0,1)
    };
    let (s, j) = (n_scenarios, n_instruments);
    // Instrument 0 is a bond (pays 1 in every scenario) — guarantees a probability
    // normalization row so the market is well-posed.
    let mut h_mat = vec![0.0f64; j * s];
    for sc in 0..s {
        h_mat[sc] = 1.0; // instrument 0 row (bond)
    }
    for inst in 1..j {
        for sc in 0..s {
            h_mat[inst * s + sc] = next() * 2.0;
        }
    }
    let pi_star: Vec<f64> = {
        let raw: Vec<f64> = (0..s).map(|_| next()).collect();
        let sum: f64 = raw.iter().sum();
        raw.iter().map(|v| v / sum).collect() // a probability measure (bond ⇒ Σπ=1)
    };
    let a: Vec<f64> = (0..j)
        .map(|inst| (0..s).map(|sc| h_mat[inst * s + sc] * pi_star[sc]).sum())
        .collect();
    let h: Vec<f64> = (0..s).map(|_| next() * 3.0).collect();
    Market {
        n_scenarios: s,
        n_instruments: j,
        h_mat,
        a,
        h,
        epsilon: 1e-6,
    }
}

fn bench_state_price() {
    println!("\n=== STATE-PRICE LP (European / basket / Asian — CertPrice) ===");
    println!(
        "{:>10} {:>8} {:>14} {:>14} {:>14} {:>10} {:>7}",
        "scenarios", "instr", "solve (µs)", "check (µs)", "gap", "price", "valid"
    );
    for &(s, j) in &[
        (4usize, 2usize),
        (16, 6),
        (64, 16),
        (128, 32),
        (256, 64),
        (512, 96),
    ] {
        let market = gen_market(s, j, 0xF00D ^ (s as u64) ^ ((j as u64) << 20));
        let solve_us = best_of(20, || {
            let _ = solve_price_cert(&market);
        });
        let cert: CertPrice = match solve_price_cert(&market) {
            PriceOutcome::Certified(c) => c,
            PriceOutcome::Arbitrage => {
                println!("{s:>10} {j:>8}   (unexpected arbitrage — skipped)");
                continue;
            }
        };
        let check_us = best_of(50, || {
            let _ = cert.check();
        });
        let rep = cert.check();
        println!(
            "{:>10} {:>8} {:>14.2} {:>14.3} {:>14.2e} {:>10.4} {:>7}",
            s,
            j,
            solve_us * 1e6,
            check_us * 1e6,
            rep.gap,
            cert.primal_price,
            rep.valid,
        );
    }
    println!(
        "  (max hᵀπ s.t. Hπ=a, π≥0 by two-phase simplex; the superhedge y=−y' is the LP\n   \
         dual (yᵀH≥h). Gap ≈ 0 — the certificate is TIGHT. Check re-verifies π≥0, Hπ=a,\n   \
         yᵀH≥h, gap≤ε from scratch (verify-not-find; never trusts the solver's search).)"
    );
}

fn bench_snell() {
    println!("\n=== SNELL-ENVELOPE LP (American / Bermudan — CertSnell) ===");
    println!(
        "{:>7} {:>10} {:>14} {:>14} {:>12} {:>7}",
        "steps", "nodes", "solve (µs)", "check (µs)", "value", "valid"
    );
    for &steps in &[16usize, 64, 128, 256, 512, 1024] {
        let tree = american_put_binomial(100.0, 100.0, 0.05, 0.2, 1.0, steps, true);
        let nodes = tree.n_nodes;
        let solve_us = best_of(10, || {
            let _ = solve_snell_cert(&tree, 1e-9);
        });
        let cert = solve_snell_cert(&tree, 1e-9);
        let check_us = best_of(10, || {
            let _ = cert.check();
        });
        let rep = cert.check();
        println!(
            "{:>7} {:>10} {:>14.2} {:>14.2} {:>12.4} {:>7}",
            steps,
            nodes,
            solve_us * 1e6,
            check_us * 1e6,
            cert.root_value,
            rep.valid,
        );
    }
    println!(
        "  (backward induction on the recombining tree = the exact Snell envelope; the cert\n   \
         checks dominance (V≥g) + superharmonicity (V_n ≥ d·Σ P V_m) — LP feasibility. The\n   \
         value converges to the American put price as steps grow; the cliff is TREE SIZE.)"
    );
}

fn main() {
    println!("fhEgg Price-Cert benchmark (real runs) — one certificate, all derivatives");
    println!("mirrors metatheory/Market/PriceCert.lean (price_cert_certifies + snell_feasible_upper_bound)");
    bench_state_price();
    bench_snell();
    println!(
        "\n  DERIVATIVES FAMILY: European/basket/Asian (state-price LP, CertPrice) · \
         American/Bermudan\n  (Snell-envelope LP, CertSnell) — ONE Price-Cert discipline, \
         checked by ITS certificate,\n  independent of how (π,y)/V were found. Arbitrage markets \
         are REJECTED (no cert)."
    );
}
