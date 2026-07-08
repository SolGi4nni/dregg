//! PERF-REGRESSION HARNESS (per-turn half) — guards the per-turn-vs-ledger-size
//! bombs (`docs/TEST-GAP-AUDIT.md` §B): the api full-ledger `template.clone()` ×2 per
//! submit (#9) and the bearer-auth pubkey ledger SCAN (#5). Both surface as the same
//! symptom: per-turn cost scaling with TOTAL ledger size, which it must not. A `#[test]`
//! (so `cargo test --workspace` GATES it) asserting a MACHINE-INDEPENDENT bound.
//!
//! FLAT lever (§B.2): a turn that touches exactly two cells does O(1) work regardless
//! of how many cells the ledger holds. The invariant is *per-turn execution cost must
//! not grow with total ledger size.* Require t(M_hi)/t(M_lo) < FLAT_SLACK across a
//! ledger-population ladder M ∈ {100, 1_000, 10_000}. A re-added whole-ledger clone or
//! pubkey scan makes the per-turn cost O(M) and fires this. Only `execute` is timed;
//! the M-cell ledger clone is untimed per-iteration setup.

use std::hint::black_box;
use std::time::Instant;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{ActionBuilder, ComputronCosts, TurnBuilder, TurnExecutor};

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
             per-turn cost at ledger size {} is {ratio:.2}x the cost at {} — it must stay FLAT. \
             A per-turn scan/clone of the whole ledger (which grew from {} to {} cells) was re-introduced.",
            pops[i],
            pops[0],
            pops[0],
            pops[i]
        );
    }
}

// Open permissions (every action `AuthRequired::None`) — the simplest executor cell,
// mirroring `perf/src/lib.rs::open_permissions` / the executor tests' `make_open_cell`.
fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn open_cell(seed: u8, balance: i64) -> Cell {
    let mut cell = Cell::with_balance([seed; 32], [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// Build a ledger with N open cells (cell 0 funded, the rest empty). Mirrors
/// `perf/src/lib.rs::ledger_with_open_cells` (inlined so this test avoids `dregg-perf`,
/// whose dep tree pulls a crate under concurrent edit).
fn ledger_with_open_cells(n: usize, funded_balance: i64) -> (Ledger, Vec<CellId>) {
    let mut ledger = Ledger::new();
    let mut ids = Vec::with_capacity(n);
    for i in 0..n {
        let bal = if i == 0 { funded_balance } else { 0 };
        let id = ledger
            .insert_cell(open_cell(i as u8 + 1, bal))
            .expect("insert open cell");
        ids.push(id);
    }
    (ledger, ids)
}

// ═══════════════════════════════════════════════════════════════════════════
// LEVER — PER-TURN SUBMIT.  Guards bomb #9 (api full-ledger clone ×2/submit) AND #5
// (bearer-auth pubkey ledger scan): the live Rust `TurnExecutor::execute` over an
// M-cell ledger, running a single Transfer cell0 → cell1 (touches 2 cells, O(1) in M).
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn per_turn_submit_is_flat_in_ledger_size() {
    let pops = [100usize, 1_000, 10_000];
    let mut times = Vec::new();
    for &m in &pops {
        let (base_ledger, ids) = ledger_with_open_cells(m, 1_000_000);
        let action = ActionBuilder::new_unchecked_for_tests(ids[0], "transfer", ids[0])
            .effect_transfer(ids[0], ids[1], 200)
            .build();
        let mut builder = TurnBuilder::new(ids[0], 0);
        builder.add_action(action);
        let turn = builder.fee(0).valid_until(1000).build();
        let executor = TurnExecutor::new(ComputronCosts::zero());

        // setup = fresh ledger clone (untimed); run = the executor's execute (timed).
        let t = median_time(
            || base_ledger.clone(),
            |ledger| {
                black_box(executor.execute(black_box(&turn), ledger));
            },
        );
        times.push(t);
    }
    assert_flat(
        "#9 api full-ledger clone + #5 bearer-auth pubkey scan",
        "TurnExecutor::execute over an M-cell ledger",
        &pops,
        &times,
    );
}
