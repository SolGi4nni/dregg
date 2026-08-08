//! LEAN FFI TURN — Stage 0 baseline of the FFI-optimization campaign.
//!
//! Measures the per-turn cost of the verified-Lean state-producer round-trip
//! (`dregg_exec_lean::execute_via_lean`: Rust JSON-encode → C bridge → Lean parse →
//! Lean execute → Lean JSON-encode → Rust parse → `WireState → Ledger` reconstitution)
//! against the bare Rust `TurnExecutor::execute` on the SAME turn. The DELTA is the
//! tax the FFI imposes.
//!
//! Per turn shape it reports:
//!   * Rust-executor wallclock (median over many iters)
//!   * Lean-FFI wallclock (median over many iters)
//!   * FFI OVERHEAD = Lean-FFI − Rust-executor
//!   * JSON bytes crossing IN (Rust→Lean) and OUT (Lean→Rust) — emitted by the
//!     `DREGG_FFI_MEASURE=1`-gated instrumentation in `exec-lean/src/lean_shadow.rs`
//!     (`run_shadow_state`), captured on stderr during the run.
//!   * TOUCHED cells (the wire serialization footprint = the pre-state id map) and
//!     WRITTEN cells (post ≠ pre by canonical state commitment). touched − written is
//!     the echoed-but-unchanged waste a delta-OUT optimization would remove.
//!
//! This is `harness = false` (a plain timed binary, not a criterion harness): the
//! deliverable is a clear baseline TABLE printed to stdout, and the byte/cell numbers
//! must be aggregated alongside the timings. Criterion's per-fn statistics do not give
//! the side-by-side delta table this campaign needs.
//!
//! GATED on `lean_available()`: with no linked `libdregg_lean.a` it prints a skip line.
//!
//! Run: `cargo bench -p dregg-perf --bench lean_ffi_turn 2>&1 | tee /tmp/ffi-baseline.log`

use std::time::Instant;

use dregg_exec_lean::execute_via_lean;
use dregg_lean_ffi::lean_available;
use dregg_perf::{
    ffi_host, ffi_setfield_turn, ffi_transfer_populated_turn, ffi_transfer_turn, fmt_secs,
    fresh_executor, written_cells,
};

/// Median of `iters` timings (microbench-grade: median is robust to scheduler noise).
fn time_median<T>(iters: u32, mut f: impl FnMut() -> T) -> f64 {
    // Warm a few times: the FIRST FFI call in the process pays Lean-runtime lazy init, which must
    // not contaminate the timed window.
    for _ in 0..3 {
        std::hint::black_box(f());
    }
    let mut samples = Vec::with_capacity(iters as usize);
    for _ in 0..iters {
        let t0 = Instant::now();
        std::hint::black_box(f());
        samples.push(t0.elapsed().as_secs_f64());
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let med = samples[samples.len() / 2];
    let min = samples[0];
    let mean = samples.iter().sum::<f64>() / samples.len() as f64;
    eprintln!(
        "    [timing] min={} median={} mean={} (n={})",
        fmt_secs(min),
        fmt_secs(med),
        fmt_secs(mean),
        iters
    );
    med
}

struct Row {
    name: &'static str,
    rust_s: f64,
    lean_s: f64,
    touched: usize,
    written: usize,
}

fn measure(
    name: &'static str,
    build: fn() -> (dregg_cell::Ledger, dregg_turn::turn::Turn),
    iters: u32,
) -> Row {
    let executor = fresh_executor();
    let host = ffi_host();

    // Pre-build the input ONCE. `execute` mutates the ledger in place, so the Rust leg clones a
    // pristine pre-state per iter (the clone is cheap and OUTSIDE the executor's hot work — we time
    // the same `execute` the executor_turn bench does, plus a clone). The Lean leg takes the
    // pre-state by reference (it does not mutate), so it clones nothing.
    let (pre_ledger, turn) = build();

    // --- Rust executor leg: time `TurnExecutor::execute` only (fresh ledger clone per iter) ---
    let rust_s = time_median(iters, || {
        let mut ledger = pre_ledger.clone();
        let r = executor.execute(&turn, &mut ledger);
        // HARD, not `debug_assert`. This is the RUST side of the FFI-tax ratio; a refused
        // Rust turn is cheaper than a committed one, so a silent refusal here would have
        // INFLATED the reported Lean-FFI overhead. See `symbolic_collapse.rs::run_batch`.
        assert!(r.is_committed(), "{name}: rust turn must commit, got {r:?}");
        r
    });

    // --- Lean FFI leg: time `execute_via_lean` (the full round-trip) on the SAME pre-state ---
    let lean_s = time_median(iters, || {
        execute_via_lean(&turn, &pre_ledger, &host).expect("execute_via_lean runs")
    });

    // --- Sub-phase profile: run the FFI boundary with DREGG_FFI_PROFILE=1 so `run_direct`
    // accumulates (in_build, execDirect, out_read) per call; dump the averages. Kept out of the
    // timed medians above. SAFETY: single-threaded; toggled around this loop only.
    unsafe {
        std::env::set_var("DREGG_FFI_PROFILE", "1");
    }
    for _ in 0..iters {
        std::hint::black_box(
            execute_via_lean(&turn, &pre_ledger, &host).expect("execute_via_lean runs"),
        );
    }
    unsafe {
        std::env::remove_var("DREGG_FFI_PROFILE");
    }
    dregg_exec_lean::prof_outer_dump(name);
    dregg_lean_ffi::lean_direct::prof_dump(name);

    // --- ATTRIBUTE the fixed per-call verified-executor cost (the ~11.7µs execDirect): the BARE
    // FFI-into-Lean identity floor + the 4 Lean sub-phases. Env-gated, additive, off the timed
    // medians. `profile_lean_phases` times `dregg_ffi_identity` (the floor) and runs the profiled
    // executor `iters` times under DREGG_LEAN_PROFILE=1 (each prints a per-sub-phase ns line on
    // stderr; aggregate them with: grep DREGG_LEAN_PROFILE | awk). SAFETY: single-threaded.
    if std::env::var("DREGG_LEAN_PROFILE").as_deref() == Ok("1") {
        match dregg_exec_lean::profile_lean_phases(&turn, &pre_ledger, &host, iters) {
            Ok(id_floor) => eprintln!(
                "  [{name}] DREGG_LEAN_IDENTITY_FLOOR median={} (n={iters}) \
                 — per-sub-phase ns on the DREGG_LEAN_PROFILE lines above",
                fmt_secs(id_floor)
            ),
            Err(e) => eprintln!("  [{name}] profile_lean_phases skipped: {e:?}"),
        }
    }

    // --- Cell footprint + JSON bytes: ONE dedicated call with the measure instrumentation ON, so
    // the IN/OUT byte line prints exactly once per shape (kept OUT of the timed loops above so the
    // eprintln I/O never pollutes the timings). SAFETY: single-threaded; toggled around one call.
    unsafe {
        std::env::set_var("DREGG_FFI_MEASURE", "1");
    }
    eprintln!("  [{name}] DREGG_FFI_MEASURE:");
    let (post_ledger, lean_committed) =
        execute_via_lean(&turn, &pre_ledger, &host).expect("execute_via_lean runs");
    unsafe {
        std::env::remove_var("DREGG_FFI_MEASURE");
    }
    assert!(
        lean_committed,
        "{name}: lean turn must commit (root-agreeing)"
    );
    let written = written_cells(&pre_ledger, &post_ledger);
    // touched = the cells the marshaller serialized = the pre-state id map. The
    // DREGG_FFI_MEASURE line (printed during the calls above) reports the exact count;
    // we recompute it here for the table from the same producer surface.
    let touched = touched_cells(&turn);

    Row {
        name,
        rust_s,
        lean_s,
        touched,
        written,
    }
}

/// The wire serialization footprint = every cell the turn references (agent + every
/// action target + every effect cell), the SAME deterministic set the producer's
/// `collect_id_map` assigns Nats to. The authoritative number is the `touched_cells=`
/// field of the DREGG_FFI_MEASURE line; this recomputes it for the table over the two
/// effect kinds the bench turns use (Transfer / SetField).
fn touched_cells(turn: &dregg_turn::turn::Turn) -> usize {
    use dregg_turn::action::Effect;
    use std::collections::BTreeSet;
    fn walk(tree: &dregg_turn::forest::CallTree, set: &mut BTreeSet<dregg_cell::CellId>) {
        set.insert(tree.action.target);
        for eff in &tree.action.effects {
            match eff {
                Effect::Transfer { from, to, .. } => {
                    set.insert(*from);
                    set.insert(*to);
                }
                Effect::SetField { cell, .. } => {
                    set.insert(*cell);
                }
                _ => {}
            }
        }
        for c in &tree.children {
            walk(c, set);
        }
    }
    let mut set = BTreeSet::new();
    set.insert(turn.agent);
    for r in &turn.call_forest.roots {
        walk(r, &mut set);
    }
    set.len()
}

fn main() {
    if !lean_available() {
        eprintln!(
            "lean_ffi_turn: libdregg_lean.a not linked — skipped. Build with the default Lean link."
        );
        return;
    }

    let iters = 200u32;
    eprintln!("# per-shape: [timing] min/median/mean lines, then ONE DREGG_FFI_MEASURE byte line.");

    let rows = vec![
        measure("transfer (bare, 2 cells)", ffi_transfer_turn, iters),
        measure(
            "transfer (populated sender, 2 cells)",
            ffi_transfer_populated_turn,
            iters,
        ),
        measure(
            "setfield (1 cell ref / 3-cell ledger)",
            ffi_setfield_turn,
            iters,
        ),
    ];

    println!("\n================= LEAN↔RUST FFI PER-TURN BASELINE (Stage 0) =================");
    println!("iterations per leg: {iters} (median reported)\n");
    println!(
        "{:<40} {:>12} {:>12} {:>14} {:>8} {:>8}",
        "turn shape", "rust", "lean-ffi", "ffi overhead", "touched", "written"
    );
    println!("{}", "-".repeat(98));
    for r in &rows {
        let overhead = r.lean_s - r.rust_s;
        let mult = if r.rust_s > 0.0 {
            r.lean_s / r.rust_s
        } else {
            0.0
        };
        println!(
            "{:<40} {:>12} {:>12} {:>14} {:>8} {:>8}",
            r.name,
            fmt_secs(r.rust_s),
            fmt_secs(r.lean_s),
            format!("{} ({:.0}x)", fmt_secs(overhead), mult),
            r.touched,
            r.written,
        );
    }
    println!("{}", "-".repeat(98));
    println!(
        "touched − written = echoed-but-unchanged cells (the delta-OUT optimization target).\n\
         IN/OUT JSON bytes per turn are on the DREGG_FFI_MEASURE stderr lines above."
    );
}
