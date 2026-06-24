//! MEASUREMENT-ONLY env-gated per-turn phase profiler (`DREGG_TURN_PROFILE=1`).
//!
//! Attributes the per-turn wall-clock cost of `execute_without_shadow` across its
//! phases so the next perf frontier can be named (now that the commitment `root()`
//! is cheap, ~2.85µs post cap-root cache). NOT a correctness gate; off the hot path
//! unless the env var is set — when unset, every `fence`/`accum` call is a no-op
//! atomic-load-and-branch (the `Instant::now()` calls are still cheap, but the
//! accumulation is skipped). Mirrors the `DREGG_FFI_PROFILE` outer-phase profiler in
//! `exec-lean/src/lean_apply.rs`.
//!
//! Phases (one accumulator each), in execution order for the classical forest path:
//!   * `validate`   — Phase 0: empty/expiry/agent/nonce/fee/frozen/receipt-chain/budget gate.
//!   * `pre_root`   — `ledger.root()` for the pre-state hash.
//!   * `phase1`     — fee debit + nonce increment.
//!   * `forest`     — `execute_tree` over every root (the auth+effect-apply walk).
//!   * `post`       — conservation/excess checks, sovereign post-exec, committed-height
//!                    advance, fee distribution, rate-limit counters.
//!   * `post_root`  — `ledger.root()` for the post-state hash.
//!   * `receipt`    — effects/turn/forest hashes, delta build, receipt build, sign, record head.
//!
//! Within `forest`, a second tier attributes the per-action sub-phases:
//!   * `f_cap`      — capability / delegation access check.
//!   * `f_precond`  — `check_preconditions`.
//!   * `f_authz`    — `verify_authorization`.
//!   * `f_snapshot` — `collect_touched_cells` + old-state clones (the touched-set HashMap).
//!   * `f_apply`    — the regular+permission effect-apply loops (`apply_effect`).
//!   * `f_program`  — the per-touched-cell program re-eval loop.

use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

#[cfg(not(target_arch = "wasm32"))]
pub(crate) use std::time::Instant;
/// Platform clock for the profiling fences. `std::time::Instant::now()` panics on
/// `wasm32-unknown-unknown` ("time not implemented on this platform") — and the
/// fences fire UNCONDITIONALLY (the env-gated branch only skips the `accum`, not the
/// `now()` snapshot), so a real in-browser turn would crash even with the profiler
/// off. `web-time::Instant` is a drop-in backed by `performance.now()`; native keeps
/// `std::time::Instant`. Re-exported so the executor's fence call sites
/// (`execute.rs` / `execute_tree.rs`) name one clock across both targets.
#[cfg(target_arch = "wasm32")]
pub(crate) use web_time::Instant;

/// Cached `DREGG_TURN_PROFILE=1` check (read once; the env var is set before the run).
pub(crate) fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("DREGG_TURN_PROFILE").as_deref() == Ok("1"))
}

macro_rules! phases {
    ($($name:ident),* $(,)?) => {
        #[derive(Clone, Copy)]
        #[allow(non_camel_case_types)] // phase names mirror the eprintln labels 1:1
        pub(crate) enum Phase { $($name),* }
        const N_PHASES: usize = { let mut n = 0; $( let _ = stringify!($name); n += 1; )* n };
        static ACC_NS: [AtomicU64; N_PHASES] = [const { AtomicU64::new(0) }; N_PHASES];
        static LABELS: [&str; N_PHASES] = [ $( stringify!($name) ),* ];
        static CALLS: AtomicU64 = AtomicU64::new(0);
    };
}

phases!(
    validate, pre_root, phase1, forest, post, post_root, receipt, // outer
    f_cap, f_precond, f_authz, f_snapshot, f_apply, f_program, // forest inner
);

/// Bump the turn counter (call once per `execute_without_shadow` entry, gated by the caller).
pub(crate) fn count_turn() {
    CALLS.fetch_add(1, Ordering::Relaxed);
}

/// Accumulate `since.elapsed()` into `phase`. Caller must have checked `enabled()`.
#[inline]
pub(crate) fn accum(phase: Phase, since: Instant) {
    ACC_NS[phase as usize].fetch_add(since.elapsed().as_nanos() as u64, Ordering::Relaxed);
}

/// Print + reset the per-turn phase averages (µs). The outer phases sum to ~the full
/// `execute_without_shadow`; the `f_*` inner phases sum to ~the `forest` outer phase.
pub fn dump(label: &str) {
    let n = CALLS.swap(0, Ordering::Relaxed).max(1);
    let mut us = [0.0f64; N_PHASES];
    for i in 0..N_PHASES {
        us[i] = ACC_NS[i].swap(0, Ordering::Relaxed) as f64 / 1e3 / n as f64;
    }
    // Outer = the first 7 phases; inner = the rest.
    let outer_end = 7;
    let outer_sum: f64 = us[..outer_end].iter().sum();
    eprintln!("=== DREGG_TURN_PROFILE[{label}] n={n} (µs/turn) ===");
    for i in 0..outer_end {
        eprintln!("  {:<10} {:>8.3}", LABELS[i], us[i]);
    }
    eprintln!("  {:<10} {:>8.3}  (outer sum)", "TOTAL", outer_sum);
    eprintln!("  --- forest inner breakdown (sums to ~forest above) ---");
    for i in outer_end..N_PHASES {
        eprintln!("  {:<10} {:>8.3}", LABELS[i], us[i]);
    }
}
