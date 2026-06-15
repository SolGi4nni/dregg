//! Shared workload builders + timing utilities for the dregg perf harnesses.
//!
//! Every workload here is constructed through the SAME production code paths the
//! node / SDK / circuit use at runtime — `generate_effect_vm_trace` for the
//! Effect-VM witness, `prove_turn_self_sovereign` for the real commit path, the
//! audited `prove_*_p3` provers for each sub-proof. The timings therefore
//! reflect the real prover, not a toy.

use std::time::Instant;

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::generate_effect_vm_trace;

// ---------------------------------------------------------------------------
// SMOKE vs FULL: every criterion bench in this crate runs a TINY input by
// default so `cargo bench --no-run` and a smoke run are cheap, and a REALISTIC
// input when `PERF_FULL=1` (the persvati capture run). This is the single
// switch the benches and the capture-baseline script agree on.
// ---------------------------------------------------------------------------

/// True when `PERF_FULL=1` — the realistic / persvati capture configuration.
/// Default (unset / "0") is SMOKE: tiny inputs, seconds-scale.
pub fn perf_full() -> bool {
    matches!(
        std::env::var("PERF_FULL").ok().as_deref(),
        Some("1") | Some("true") | Some("yes")
    )
}

/// A label for the current input regime, for criterion group/ids and logs.
pub fn regime() -> &'static str {
    if perf_full() { "full" } else { "smoke" }
}

/// A named turn workload: an initial cell state plus the effect bundle that
/// makes up one turn.
pub struct Workload {
    pub name: &'static str,
    pub initial: CellState,
    pub effects: Vec<Effect>,
}

/// The reference workload set, SMOKE-vs-FULL aware.
///
/// * SMOKE (default): the single smallest real turn (`transfer_1effect`) only —
///   so `cargo bench --no-run` and a smoke run stay seconds-scale.
/// * FULL (`PERF_FULL=1`): the 1/4/16-effect ladder, to show how prove time
///   scales with turn size on the fixed-height EffectVM AIR. This is the
///   persvati capture set.
pub fn workloads() -> Vec<Workload> {
    let one = Workload {
        name: "transfer_1effect",
        initial: CellState::new(1_000_000, 0),
        effects: vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }],
    };
    if !perf_full() {
        return vec![one];
    }
    vec![
        one,
        Workload {
            name: "transfer_4effect",
            initial: CellState::new(1_000_000, 0),
            effects: (0..4)
                .map(|i| Effect::Transfer {
                    amount: 10,
                    direction: (i % 2) as u32,
                })
                .collect(),
        },
        Workload {
            name: "transfer_16effect",
            initial: CellState::new(1_000_000, 0),
            effects: (0..16)
                .map(|i| Effect::Transfer {
                    amount: 1,
                    direction: (i % 2) as u32,
                })
                .collect(),
        },
    ]
}

/// Build the (base_trace, public_inputs) pair for a workload — the exact inputs
/// `prove_effect_vm_p3` consumes.
pub fn build_trace(w: &Workload) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    generate_effect_vm_trace(&w.initial, &w.effects)
}

/// A canonical single-Transfer turn — the smallest real turn, and the shape the
/// descriptor-interpreter cutover path is validated for.
pub fn single_transfer() -> (CellState, Vec<Effect>) {
    (
        CellState::new(1_000_000, 0),
        vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }],
    )
}

// ---------------------------------------------------------------------------
// Timing helpers — warm once, then time `iters` runs, report the mean.
// ---------------------------------------------------------------------------

/// Time `iters` runs of `f` after one warm-up run, returning the mean seconds.
pub fn time_mean<T>(iters: u32, mut f: impl FnMut() -> T) -> f64 {
    let _warm = f();
    let t0 = Instant::now();
    for _ in 0..iters {
        std::hint::black_box(f());
    }
    t0.elapsed().as_secs_f64() / iters as f64
}

/// Format a duration in seconds with an adaptive unit.
pub fn fmt_secs(secs: f64) -> String {
    if secs < 1e-6 {
        format!("{:.0} ns", secs * 1e9)
    } else if secs < 1e-3 {
        format!("{:.1} us", secs * 1e6)
    } else if secs < 1.0 {
        format!("{:.1} ms", secs * 1e3)
    } else {
        format!("{:.3} s", secs)
    }
}

/// Format a byte size with an adaptive unit.
pub fn fmt_bytes(n: usize) -> String {
    if n < 1024 {
        format!("{n} B")
    } else if n < 1024 * 1024 {
        format!("{:.1} KiB", n as f64 / 1024.0)
    } else {
        format!("{:.2} MiB", n as f64 / (1024.0 * 1024.0))
    }
}

// ---------------------------------------------------------------------------
// Executor-turn workload: build a real Ledger with two open cells + a Transfer
// turn so the live Rust `TurnExecutor::execute` (the executor entry the node
// drives) can be benchmarked through its PUBLIC API. Mirrors the executor's own
// `setup_two_open_cells` / `effect_transfer` test shape.
// ---------------------------------------------------------------------------

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_turn::{ActionBuilder, Turn, TurnBuilder, TurnExecutor};

/// Open permissions (every action `AuthRequired::None`) — the simplest cell
/// shape for an unauthenticated executor turn, matching the executor tests'
/// `make_open_cell`.
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

/// Build a ledger with two open cells and a single-Transfer turn from the
/// agent to the target — the smallest real executor turn. Returns the pieces
/// `TurnExecutor::execute(&turn, &mut ledger)` consumes.
pub fn executor_transfer_turn() -> (Ledger, Turn) {
    let mut ledger = Ledger::new();
    let agent = open_cell(1, 1_000_000);
    let target = open_cell(2, 0);
    let agent_id = ledger.insert_cell(agent).expect("insert agent");
    let target_id = ledger.insert_cell(target).expect("insert target");

    let mut builder = TurnBuilder::new(agent_id, 0);
    let action = ActionBuilder::new_unchecked_for_tests(agent_id, "transfer", agent_id)
        .effect_transfer(agent_id, target_id, 200)
        .build();
    builder.add_action(action);
    let turn = builder.fee(0).build();
    (ledger, turn)
}

/// A fresh zero-cost executor (the cheapest configuration — the executor logic,
/// not the fee accounting, is what we time).
pub fn fresh_executor() -> TurnExecutor {
    TurnExecutor::new(dregg_turn::ComputronCosts::zero())
}

// ---------------------------------------------------------------------------
// Commitment workload: a populated `Cell` for the canonical state commitment.
// ---------------------------------------------------------------------------

/// A populated cell for the commitment benches: balance + some fields set, so
/// the commitment hashes a non-trivial state (not an all-zero cell).
pub fn commitment_cell() -> Cell {
    let mut cell = Cell::with_balance([7u8; 32], [11u8; 32], 1_000_000);
    // Touch a few state fields so the commitment isn't over an all-zero state.
    for i in 0..4 {
        cell.state.fields[i] = [i as u8 + 1; 32];
    }
    cell
}

/// A default v9 rotation context (zeroed roots) for the rotated-commitment
/// bench — the rotation long pole the umem path drives.
pub fn v9_context() -> dregg_cell::commitment::V9RotationContext {
    dregg_cell::commitment::V9RotationContext {
        cells_root: BabyBear::new(0),
        nullifier_root: [0u8; 32],
        iroot: BabyBear::new(0),
    }
}
