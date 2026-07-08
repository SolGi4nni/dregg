//! PERF-REGRESSION HARNESS (circuit half) — guards the two circuit-side perf bombs
//! (`docs/TEST-GAP-AUDIT.md` §B): the sorted-leaf linear `position` scan (#7) and the
//! per-trace-row lookup-table re-scan (#8). A `#[test]` (so `cargo test --workspace`
//! GATES it) asserting a MACHINE-INDEPENDENT growth bound — a ratio of two timings on
//! the same machine in the same run, so absolute CPU speed cancels.
//!
//! Two lever shapes (§B.2):
//!  * GROWTH — cost expected ~linear in a genuine size N; require
//!        t(N_hi)/t(N_lo) < SLACK·(N_hi/N_lo)^EXPONENT   (SLACK=3.0, EXPONENT=1.2).
//!  * FLAT   — cost must NOT grow with a POPULATION at all; require
//!        t(pop_hi)/t(pop_lo) < FLAT_SLACK.

use std::hint::black_box;
use std::time::Instant;

const SLACK: f64 = 3.0;
const EXPONENT: f64 = 1.2;
const FLAT_SLACK: f64 = 4.0;
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

fn assert_flat(bomb: &str, lever: &str, pops: &[usize], times: &[f64]) {
    eprintln!("\n[{lever}]  (guards bomb: {bomb})  [FLAT: cost must not grow with population]");
    for (n, t) in pops.iter().zip(times) {
        eprintln!("    pop={n:>7}   t={}", fmt(*t));
    }
    let base = times[0];
    if base < MIN_BASELINE_S {
        eprintln!(
            "    baseline {} < {} floor — timer granularity; flat check would divide by noise, SKIPPED",
            fmt(base),
            fmt(MIN_BASELINE_S)
        );
        return;
    }
    for i in 1..pops.len() {
        let ratio = times[i] / base;
        eprintln!(
            "    pop {}: {ratio:.2}x baseline  (flat bound {FLAT_SLACK})  ({})",
            pops[i],
            if ratio < FLAT_SLACK { "ok" } else { "SCALES" }
        );
        assert!(
            ratio < FLAT_SLACK,
            "POPULATION-SCALING REGRESSION [{bomb}] in {lever}: \
             per-op cost at population {} is {ratio:.2}x the cost at {} — it must stay FLAT. \
             A per-op scan of the whole population (which grew from {} to {}) was re-introduced.",
            pops[i],
            pops[0],
            pops[0],
            pops[i]
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// LEVER — HEAP MEMBERSHIP.  Guards bomb #7 (linear `position` on sorted leaves,
// `heap_root.rs` / `cap_root.rs`): `CanonicalHeapTree8::position_of` is now a binary
// search (O(log n)). We build a heap of N leaves and look up ALL N addresses — total
// O(n log n) on the fixed path, O(n²) if the scan is re-introduced.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn heap_membership_is_subquadratic_in_leaf_count() {
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};

    let sizes = [512usize, 2048, 8192];
    let mut times = Vec::new();
    for &n in &sizes {
        let leaves: Vec<HeapLeaf> = (0..n)
            .map(|i| HeapLeaf {
                addr: BabyBear::new((i as u32 + 1) * 2),
                value: BabyBear::new(i as u32 + 7),
            })
            .collect();
        let tree = CanonicalHeapTree8::new(leaves.clone(), HEAP_TREE_DEPTH);
        let keys: Vec<BabyBear> = leaves.iter().map(|l| l.addr).collect();
        // run = look up every one of the N present keys (N · position_of).
        let t = median_time(
            || (),
            |_| {
                let mut hits = 0usize;
                for k in &keys {
                    if tree.position_of(*k).is_some() {
                        hits += 1;
                    }
                }
                hits
            },
        );
        times.push(t);
    }
    assert_subpolynomial(
        "#7 linear position() scan on sorted leaves",
        "heap position_of over N leaves (N lookups)",
        &sizes,
        &times,
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// LEVER — DSL LOOKUP-TABLE MEMBERSHIP.  Guards bomb #8 (`dsl/circuit.rs` re-scans the
// lookup table per trace row, O(rows·entries), tables up to 2^16): `DslCircuit` now
// builds a hashed `LookupIndex` once at construction, so `eval_constraints` (called
// per row) is O(1) in the table size. We drive the PRODUCTION per-row path
// (`DslCircuit::new` → `StarkAir::eval_constraints`) with a FIXED number of query rows
// against tables of growing size R. Cost is flat in R on the index; a reverted per-row
// `entries.find(...)` makes it O(R) — caught by the FLAT bound.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn dsl_lookup_membership_is_flat_in_table_size() {
    use dregg_circuit::dsl::circuit::{CircuitDescriptor, ConstraintExpr, DslCircuit, LookupTable};
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::stark::StarkAir;

    const QUERY_ROWS: usize = 4096; // fixed trace-row count; only the table size R varies
    let table_sizes = [2_000usize, 8_000, 32_000];
    let mut times = Vec::new();
    for &r in &table_sizes {
        let table = LookupTable {
            id: "t".to_string(),
            width: 2,
            entries: (0..r as u32).map(|i| vec![i, i]).collect(),
        };
        let descriptor = CircuitDescriptor {
            name: "perf-lookup".to_string(),
            trace_width: 2,
            max_degree: 1,
            columns: vec![],
            constraints: vec![ConstraintExpr::Lookup {
                table_id: "t".to_string(),
                query_columns: vec![0, 1],
            }],
            boundaries: vec![],
            public_input_count: 0,
            lookup_tables: vec![table],
        };
        // `DslCircuit::new` builds the LookupIndex once (O(R), untimed setup).
        let circuit = DslCircuit::new(descriptor);
        let row = [BabyBear::new(7), BabyBear::new(7)];
        let alpha = BabyBear::ONE;
        // run = QUERY_ROWS per-row evaluations (membership probes), fixed count.
        let t = median_time(
            || (),
            |_| {
                let mut acc = BabyBear::ZERO;
                for _ in 0..QUERY_ROWS {
                    acc += circuit.eval_constraints(&row, &row, &[], alpha);
                }
                acc
            },
        );
        times.push(t);
    }
    assert_flat(
        "#8 per-row lookup-table re-scan O(rows·entries)",
        "DslCircuit::eval_constraints (fixed rows) vs table size R",
        &table_sizes,
        &times,
    );
}
