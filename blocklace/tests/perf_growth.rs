//! PERF-REGRESSION HARNESS (finality half) — the `#[test]` that turns "found on a
//! live mesh in three months" into "CI red on the PR".
//!
//! Design + ground: `docs/TEST-GAP-AUDIT.md` §B (the 9-bomb table). The criterion
//! benches RECORD timings but never ASSERT, and `bench.yml` is `workflow_dispatch`-
//! only and does not list `dregg-perf` — so a re-introduced O(n²)/O(n³) produces a
//! number in an artifact nobody diffs and passes every unit test (which run at N≈9
//! blocks, below every bomb's crossover). This is a `#[test]` (so `cargo test
//! --workspace` GATES it) that asserts a MACHINE-INDEPENDENT growth bound on the
//! finality order — the function that had the `tauOrderFast` / `has_equivocation_in_past`
//! bombs.
//!
//! ## The machine-independent idea (§B.2)
//!
//! Never assert absolute milliseconds (machine-dependent, flaky). Assert a RATIO of
//! two timings measured on the SAME machine in the SAME run — absolute CPU speed
//! cancels. For a genuine input size N whose cost has a KNOWN growth-class baseline,
//! require   t(N_hi)/t(N_lo)  <  SLACK · (N_hi/N_lo)^EXPONENT   and pick EXPONENT just
//! above the baseline so a WORSE class blows the bound while the baseline (plus noise)
//! passes.
//!
//! ## Measured baseline of `ordering::tau` (a FINDING, see the note on the lever)
//!
//! Bomb #3 (`docs/PERF-BOMB-AUDIT.md`) was the `tauOrderFast` List-cache at **O(n³)**
//! (plus `has_equivocation_in_past` at O(n²)). The fix removed the cubic term; this
//! harness MEASURES the fixed `tau` at ~O(n²) — NOT the ~linear the audit hoped for.
//! The residual quadratic is inherent to the current `tau`: `xsort` computes each
//! ordered block's full causal past (Σ past sizes ≈ n² for a linear-depth DAG). So the
//! finality lever gates **sub-cubic** (the O(n³) List-cache regression FAILS; the
//! present quadratic PASSES) and the quadratic baseline is reported to HORIZONLOG as a
//! separate scaling observation — NOT silently laundered as linear.

use std::hint::black_box;
use std::time::Instant;

// tau is EXPECTED ~quadratic (see the module note); this lever gates SUB-CUBIC so a
// re-introduced O(n³) List-cache (bomb #3) blows the bound while the quadratic baseline
// passes with margin. We assert ONE big-span ratio (100→900, ratio 9) rather than
// ratio-3 steps: at ratio 9 a quadratic reads ~81× and a cubic ~729×, so they separate
// far outside the shared-machine noise band (the small-N baseline swings 2–4× run to
// run on this heavily-parallel build box — a tight ratio-3 step false-fails on it).
const FINALITY_SLACK: f64 = 3.0;
const FINALITY_EXPONENT: f64 = 2.2;
const MIN_BASELINE_S: f64 = 50e-6;

/// Median wall-time (seconds) of `run`, over `iters` timed iterations after `warmup`
/// discarded ones; fresh (untimed) `setup` state per iteration.
fn median_time<S, T>(
    warmup: usize,
    iters: usize,
    mut setup: impl FnMut() -> S,
    mut run: impl FnMut(&mut S) -> T,
) -> f64 {
    for _ in 0..warmup {
        let mut s = setup();
        black_box(run(&mut s));
    }
    let mut times = Vec::with_capacity(iters);
    for _ in 0..iters {
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

/// Ratio-bound assertion: for each consecutive size step the time ratio must stay under
/// `slack·(size_ratio)^exponent`. Choose `exponent` just above the lever's baseline
/// growth-class so a worse class fails and the baseline (+ noise) passes.
fn assert_growth(
    bomb: &str,
    lever: &str,
    sizes: &[usize],
    times: &[f64],
    slack: f64,
    exponent: f64,
) {
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
        let bound = slack * (nhi / nlo).powf(exponent);
        eprintln!(
            "    step {}->{}: ratio={ratio:.2}  bound={bound:.2}  ({})",
            sizes[w],
            sizes[w + 1],
            if ratio < bound { "ok" } else { "OVER-BOUND" }
        );
        assert!(
            ratio < bound,
            "SUPER-{}-POLYNOMIAL REGRESSION [{bomb}] in {lever}: \
             t({nhi})/t({nlo}) = {ratio:.2} exceeds bound {bound:.2} \
             (= {slack}·({nhi}/{nlo})^{exponent}). A worse-than-baseline path was re-introduced.",
            exponent as u32
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// LEVER — FINALITY ORDER.  Guards bomb #3 (`tauOrderFast` List-cache O(n³) +
// `has_equivocation_in_past` O(n²)) AND bomb #1 (per-poll finality clones the whole
// DAG): `ordering::tau` over a fully-connected lace of N blocks. tau drives
// `compute_rounds` / `EquivocationIndex::build` / `find_all_final_leaders` / `xsort` —
// the exact call tree the node's `poll_finalized_blocks` / `VerifiedFinality::compute_order`
// runs each poll. (`compute_order` itself is a node-BINARY-private module,
// `node/src/finality_gate.rs`, unreachable from an integration test; its finalization
// core IS this `tau`, so the pure-level ratio guards the same invariant.)
//
// NOTE (finding): the fixed `tau` measures ~O(n²), not the ~linear the audit hoped.
// This lever gates SUB-CUBIC — the O(n³) List-cache regression FAILS, the present
// quadratic PASSES — and the quadratic baseline is a reported scaling observation.
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
fn finality_order_is_subcubic_in_dag_size() {
    use dregg_blocklace::ordering::tau;
    // A single big-span ratio N: 100 → 900 blocks (P=4 participants × {25, 225} rounds).
    // At ratio 9 a quadratic baseline reads ~81× (bound below) and a re-introduced O(n³)
    // List-cache reads ~729×, so they separate far outside the shared-machine noise band
    // — clean where ratio-3 steps false-fail. Kept ≤900 (not 2000) because tau is ~O(n²):
    // 900 is ~4 s/run, 2000 would be ~12 s.
    const P: usize = 4;
    let sizes = [100usize, 900];
    let mut times = Vec::new();
    let mut agree = Vec::new();
    for &n in &sizes {
        let rounds = (n / P) as u64;
        let (bl, keys) = full_lace(P, rounds);
        agree.push(tau(&bl, &keys).len());
        // tau is expensive (~O(n²)); median of 3 timed runs after 1 warmup keeps the
        // lever near ~20 s while still smoothing scheduler noise.
        let t = median_time(1, 3, || (), |_| black_box(tau(&bl, &keys)).len());
        times.push(t);
    }
    // Large-N correctness smoke (GAP-3): the largest tau finalizes a non-empty order (a
    // re-added O(n³) would time the whole `cargo test` out here, before the ratio prints).
    assert!(
        *agree.last().unwrap() > 0,
        "tau over the largest lace must finalize a non-empty order (large-N smoke)"
    );
    assert_growth(
        "#3 tauOrderFast O(n³) List-cache (must stay sub-cubic) + #1 per-poll DAG clone",
        "finality::tau over N blocks (big-span 100->900)",
        &sizes,
        &times,
        FINALITY_SLACK,
        FINALITY_EXPONENT,
    );
}
