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

/// A named turn workload: an initial cell state plus the effect bundle that
/// makes up one turn.
pub struct Workload {
    pub name: &'static str,
    pub initial: CellState,
    pub effects: Vec<Effect>,
}

/// The reference workload set: a 1-effect self-transfer (the smallest real
/// turn), and progressively larger effect bundles, to show how prove time
/// scales with turn size on the fixed-height EffectVM AIR.
pub fn workloads() -> Vec<Workload> {
    vec![
        Workload {
            name: "transfer_1effect",
            initial: CellState::new(1_000_000, 0),
            effects: vec![Effect::Transfer {
                amount: 100,
                direction: 1,
            }],
        },
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
