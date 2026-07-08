//! PERF-REGRESSION HARNESS (finality half) — the `#[test]` that turns "found on a
//! live mesh in three months" into "CI red on the PR".
//!
//! Design + ground: `docs/TEST-GAP-AUDIT.md` §B (the 9-bomb table). The criterion
//! benches RECORD timings but never ASSERT, and `bench.yml` is `workflow_dispatch`-
//! only and does not list `dregg-perf` — so a re-introduced O(n²)/O(n³) produces a
//! number in an artifact nobody diffs and passes every unit test (which run at N≈9
//! blocks, below every bomb's crossover). This is a `#[test]` (so `cargo test
//! --workspace` GATES it) that asserts a MACHINE-INDEPENDENT growth bound on the
//! finality order — the function that had the `has_equivocation_in_past` bomb.
//!
//! ## The machine-independent idea (§B.2)
//!
//! Never assert absolute milliseconds (machine-dependent, flaky). Assert a RATIO of
//! two timings measured on the SAME machine in the SAME run — absolute CPU speed
//! cancels. For a genuine input size N (a lace of N blocks) whose cost is *expected*
//! to be ~linear, require
//!     t(N_hi)/t(N_lo)  <  SLACK · (N_hi/N_lo)^EXPONENT
//! with EXPONENT=1.2 (tolerates near-linear + log) and SLACK=3.0 (constant-factor +
//! scheduler noise). A re-introduced quadratic/cubic blows it; linear/log passes.
//!
//! Robustness: a warmup, the MEDIAN of k≥7 timed runs, a small-end floor (a baseline
//! under ~50 µs is timer granularity, not cost), a generous SLACK, and a failure
//! message that NAMES the bomb.

use std::hint::black_box;
use std::time::Instant;

const SLACK: f64 = 3.0;
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
        eprintln!("    N={n:>7}   t={}", fmt(*t));
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
             (= {SLACK}·({nhi}/{nlo})^{EXPONENT}). A quadratic/cubic path was re-introduced."
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// LEVER — FINALITY ORDER.  Guards bomb #3 (`has_equivocation_in_past` unmemoized,
// O(waves·P·N²)) AND bomb #1 (per-poll finality clones the whole DAG): `ordering::tau`
// over a fully-connected lace of N blocks. tau drives `compute_rounds` /
// `EquivocationIndex::build` / `find_all_final_leaders` — the exact call tree the
// node's `poll_finalized_blocks` / `VerifiedFinality::compute_order` runs each poll.
// (`compute_order` itself is a node-BINARY-private module, `node/src/finality_gate.rs`,
// unreachable from an integration test; its finalization core IS this `tau`, so the
// pure-level ratio guards the same invariant: per-poll finality cost must not grow
// super-linearly with total DAG size.)
// ═══════════════════════════════════════════════════════════════════════════

/// Fully-connected lace: `P` participants, one block each per round, every block
/// referencing ALL of the previous round's blocks. Mirrors `ordering.rs`'s own test
/// helper `build_full_blocklace`.
fn full_lace(participants: usize, rounds: u64) -> (dregg_blocklace::Blocklace, Vec<[u8; 32]>) {
    use dregg_blocklace::{Block, BlockId, Blocklace};
    let keys: Vec<[u8; 32]> = (0..participants).map(|i| [i as u8 + 1; 32]).collect();
    let mut bl = Blocklace::new();
    let mut prev_round: Vec<BlockId> = Vec::new();
    for round in 1..=rounds {
        let preds = if round == 1 {
            Vec::new()
        } else {
            prev_round.clone()
        };
        let mut this_round = Vec::with_capacity(participants);
        for (i, &creator) in keys.iter().enumerate() {
            let block = Block::new(
                creator,
                round - 1,
                preds.clone(),
                vec![round as u8, i as u8],
            );
            let id = block.id();
            bl.insert_unverified(block).expect("strand extension");
            this_round.push(id);
        }
        prev_round = this_round;
    }
    (bl, keys)
}

#[test]
fn finality_order_is_subpolynomial_in_dag_size() {
    use dregg_blocklace::ordering::tau;
    // N ∈ {100, 500, 2000} blocks (§B.1), realized as P=4 participants × {25,125,500}
    // rounds. Modest N so the test adds seconds, not minutes — the ratio catches the
    // asymptotic without a huge lace.
    const P: usize = 4;
    let sizes = [100usize, 500, 2000];
    let mut times = Vec::new();
    let mut agree = Vec::new();
    for &n in &sizes {
        let rounds = (n / P) as u64;
        let (bl, keys) = full_lace(P, rounds);
        agree.push(tau(&bl, &keys).len());
        let t = median_time(|| (), |_| black_box(tau(&bl, &keys)).len());
        times.push(t);
    }
    // Large-N correctness smoke (GAP-3): the 2000-block tau finalizes a non-empty
    // order (a re-added O(n³) would time the whole `cargo test` out here, before the
    // ratio even prints).
    assert!(
        *agree.last().unwrap() > 0,
        "tau over a 2000-block lace must finalize a non-empty order (large-N smoke)"
    );
    assert_subpolynomial(
        "#3 has_equivocation_in_past O(n²) + #1 per-poll DAG clone",
        "finality::tau over N blocks",
        &sizes,
        &times,
    );
}
