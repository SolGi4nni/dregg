//! PERF-REGRESSION HARNESS (coord half) — the budget anti-replay lever.
//!
//! Companion to `perf/tests/perf_growth.rs`; same machine-independent ratio idea
//! (`docs/TEST-GAP-AUDIT.md` §B.2). This file lives in `coord/tests/` because the
//! bomb it guards is in `coord/src/budget.rs`, which `perf` does not depend on. It is
//! a `#[test]`, so `cargo test --workspace` gates it.
//!
//! GROWTH bound: for a genuine input size D, require
//!     t(D_hi)/t(D_lo)  <  SLACK · (D_hi/D_lo)^EXPONENT
//! with SLACK=3.0, EXPONENT=1.2 — a linear path passes, a quadratic fails.

use std::hint::black_box;
use std::time::Instant;

// The fixed HashSet path is O(D) with a mild cache/rehash per-op drift; the bomb is
// O(D²). We use a BIG size span (ratio 8) so the O(D)-vs-O(D²) gap (≈12× vs ≈64× per
// step) sits well outside the shared-machine scheduler-noise band, and a generous SLACK
// so a single inflated timed window (this repo is built by many agents at once) passes
// while a genuine quadratic — 64×+ per ratio-8 step — still blows the bound.
const SLACK: f64 = 4.0;
const EXPONENT: f64 = 1.2;
const MIN_BASELINE_S: f64 = 50e-6;
const WARMUP: usize = 3;
const ITERS: usize = 7;

fn median_time<S, T>(mut setup: impl FnMut() -> S, mut run: impl FnMut(&mut S) -> T) -> f64 {
    for _ in 0..WARMUP {
        let mut s = setup();
        black_box(run(&mut s));
    }
    let mut times = Vec::with_capacity(ITERS);
    for _ in 0..ITERS {
        let mut s = setup();
        let t0 = Instant::now();
        black_box(run(&mut s));
        times.push(t0.elapsed().as_secs_f64());
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    times[times.len() / 2]
}

fn fmt(secs: f64) -> String {
    if secs < 1e-3 {
        format!("{:.1}us", secs * 1e6)
    } else if secs < 1.0 {
        format!("{:.2}ms", secs * 1e3)
    } else {
        format!("{:.3}s", secs)
    }
}

fn assert_subpolynomial(bomb: &str, lever: &str, sizes: &[usize], times: &[f64]) {
    eprintln!("\n[{lever}]  (guards bomb: {bomb})");
    for (n, t) in sizes.iter().zip(times) {
        eprintln!("    D={n:>7}   t={}", fmt(*t));
    }
    for w in 0..sizes.len() - 1 {
        let (nlo, nhi) = (sizes[w] as f64, sizes[w + 1] as f64);
        let (tlo, thi) = (times[w], times[w + 1]);
        if tlo < MIN_BASELINE_S {
            eprintln!(
                "    step {}->{}: baseline {} < {} floor — timer granularity, ratio skipped",
                sizes[w],
                sizes[w + 1],
                fmt(tlo),
                fmt(MIN_BASELINE_S)
            );
            continue;
        }
        let ratio = thi / tlo;
        let bound = SLACK * (nhi / nlo).powf(EXPONENT);
        eprintln!(
            "    step {}->{}: ratio={ratio:.2}  bound={bound:.2}  ({})",
            sizes[w],
            sizes[w + 1],
            if ratio < bound { "ok" } else { "SUPER-LINEAR" }
        );
        assert!(
            ratio < bound,
            "SUPER-LINEAR REGRESSION [{bomb}] in {lever}: \
             t({nhi})/t({nlo}) = {ratio:.2} exceeds bound {bound:.2} \
             (= {SLACK}·({nhi}/{nlo})^{EXPONENT}). The anti-replay set went quadratic."
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// LEVER — COORD BUDGET ANTI-REPLAY.  Guards bomb #6 (`budget.rs` used a `Vec` as the
// anti-replay debit set, so `try_debit_fresh`'s duplicate check was an O(D) scan →
// O(D²) to record D debits). The fix carries a `HashSet` (`debit_set`) alongside, so
// recording D fresh debits is O(D). We record D distinct debits from an empty slice
// and assert the total stays sub-quadratic in D.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn budget_anti_replay_is_subquadratic_in_debit_count() {
    use dregg_cell::CellId;
    use dregg_coord::budget::BudgetSlice;

    let sizes = [2_000usize, 16_000, 128_000];
    let mut times = Vec::new();
    for &d in &sizes {
        let agent = CellId::from_bytes([7u8; 32]);
        let digests: Vec<[u8; 32]> = (0..d)
            .map(|i| {
                let mut b = [0u8; 32];
                b[..8].copy_from_slice(&(i as u64).to_le_bytes());
                b
            })
            .collect();
        // setup = a fresh slice with a ceiling that covers D unit debits (untimed).
        // run = record all D fresh debits (each is a HashSet contains + push + insert).
        let t = median_time(
            || BudgetSlice::new(agent, 0, d as u64 + 1),
            |slice| {
                for dg in &digests {
                    let _ = slice.try_debit_fresh(1, *dg);
                }
                black_box(slice.remaining())
            },
        );
        times.push(t);
    }
    assert_subpolynomial(
        "#6 coord budget Vec anti-replay set O(D²)",
        "BudgetSlice::try_debit_fresh recording D debits",
        &sizes,
        &times,
    );
}
