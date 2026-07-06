//! Workload-execution characterization: latency + throughput of
//! [`dregg_sandbox::run_source`] on the OWNED wasmi `Sandboxed` tier, plus a
//! horizontal (N-thread) scaling sweep.
//!
//! Ported from the retired operated exec layer's `benches/workload_exec.rs`,
//! adapted to the native surface: only the genuinely-executed tier
//! (`CapTier::Sandboxed` on wasmi) is timed; the stronger tiers
//! (JIT / Caged / MicroVm / Gpu) are honest fail-closed seams here, so instead
//! of timing engines this crate does not own, the bench VERIFIES each seam
//! refuses (never a silent downgrade) and times the refusal path.
//!
//! Hand-rolled `harness = false` bench (no criterion dependency, fully offline):
//! it runs a warmup, times N iterations with `Instant`, and prints a latency
//! distribution + a derived single-thread throughput.
//!
//! WIRING (not yet applied) — add to `dregg-sandbox/Cargo.toml`:
//!     [[bench]]
//!     name = "workload_exec"
//!     harness = false
//! (Until then, `cargo bench` compiles this under the default libtest harness
//! and runs zero benches; the file is inert.)
//!
//! Run:  `cargo bench -p dregg-sandbox --bench workload_exec`
//! Knobs (env): `BENCH_ITERS`, `BENCH_WIDE_N` (comma-list of thread counts),
//! `BENCH_WIDE_ITERS`.

use dregg_sandbox::{CapTier, RunError, run_source};
use std::time::{Duration, Instant};

// ---- canonical workloads (the same sources the unit tests exercise) ----

/// wasmi (Sandboxed): a core module computing add(40, 2) == 42.
const WASMI_ADD: &str = r#"
    (module
      (func $add (param $a i32) (param $b i32) (result i32)
        local.get $a local.get $b i32.add)
      (func (export "run") (result i32)
        (call $add (i32.const 40) (i32.const 2))))
"#;

/// A heavier wasmi workload: sum 1..N in a loop (busy in-sandbox compute), to
/// separate "instantiate + call overhead" from "actual guest work".
const WASMI_LOOP: &str = r#"
    (module
      (func (export "run") (result i32)
        (local $i i32) (local $acc i32)
        (local.set $i (i32.const 0))
        (local.set $acc (i32.const 0))
        (block $done
          (loop $l
            (br_if $done (i32.ge_s (local.get $i) (i32.const 1000000)))
            (local.set $acc (i32.add (local.get $acc) (local.get $i)))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $l)))
        (local.get $acc)))
"#;

// ---- timing harness ----

struct Stats {
    label: String,
    n: usize,
    samples: Vec<Duration>,
}

impl Stats {
    fn report(mut self) {
        self.samples.sort();
        let n = self.samples.len().max(1);
        let total: Duration = self.samples.iter().sum();
        let mean = total / n as u32;
        let min = self.samples[0];
        let p = |q: f64| self.samples[((n as f64 * q) as usize).min(n - 1)];
        let per_sec = if mean.as_secs_f64() > 0.0 {
            1.0 / mean.as_secs_f64()
        } else {
            f64::INFINITY
        };
        println!(
            "  {:<34} n={:<5} min={:>10}  mean={:>10}  p50={:>10}  p95={:>10}  p99={:>10}  ~{:>9.1}/s (1 thread)",
            self.label,
            self.n,
            fmt(min),
            fmt(mean),
            fmt(p(0.50)),
            fmt(p(0.95)),
            fmt(p(0.99)),
            per_sec,
        );
    }
}

fn fmt(d: Duration) -> String {
    let us = d.as_secs_f64() * 1e6;
    if us >= 1000.0 {
        format!("{:.2}ms", us / 1000.0)
    } else {
        format!("{:.1}us", us)
    }
}

fn bench<F: FnMut()>(label: &str, iters: usize, warmup: usize, mut f: F) -> Stats {
    for _ in 0..warmup {
        f();
    }
    let mut samples = Vec::with_capacity(iters);
    for _ in 0..iters {
        let t = Instant::now();
        f();
        samples.push(t.elapsed());
    }
    Stats {
        label: label.to_string(),
        n: iters,
        samples,
    }
}

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

fn main() {
    println!("\n=== dregg-sandbox workload-exec characterization (VERTICAL, single thread) ===");
    println!("    one `run_source` = tier-gate + assemble + store + instantiate + call\n");

    let iters = env_usize("BENCH_ITERS", 0);

    // wasmi Sandboxed — the owned, genuinely-executed tier (pure interpreter).
    bench(
        "wasmi  Sandboxed   add(40,2)",
        if iters > 0 { iters } else { 2000 },
        50,
        || {
            let out = run_source("wat", WASMI_ADD, CapTier::Sandboxed, &[]).expect("wasmi add");
            assert_eq!(out.values, vec!["42".to_string()]);
        },
    )
    .report();

    // wasmi Sandboxed with a 1M-iteration in-guest loop — shows the guest-work
    // floor vs the trivial-add overhead.
    bench(
        "wasmi  Sandboxed   sum(1..1e6)",
        if iters > 0 { iters } else { 500 },
        20,
        || {
            let _ = run_source("wat", WASMI_LOOP, CapTier::Sandboxed, &[]).expect("wasmi loop");
        },
    )
    .report();

    // The fail-closed seams: verify each stronger tier REFUSES (never a silent
    // downgrade), and time the refusal path (it should be O(ns) — refusal is
    // cheaper than execution, so a flood of not-served requests cannot starve
    // the served tier).
    for tier in [
        CapTier::JitSandboxed,
        CapTier::Caged,
        CapTier::MicroVm,
        CapTier::Gpu,
    ] {
        bench(
            &format!("{tier:?} seam refusal (fail-closed)"),
            if iters > 0 { iters } else { 2000 },
            50,
            || {
                let err = run_source("wat", WASMI_ADD, tier, &[])
                    .expect_err("stronger tiers must refuse, never downgrade");
                assert!(matches!(err, RunError::TierNotServed { .. }));
            },
        )
        .report();
    }

    // ---- WIDE: horizontal scaling on the owned in-process tier (wasmi) ----
    println!("\n=== WIDE scaling sweep (N concurrent threads, wasmi Sandboxed add) ===");
    println!("    aggregate throughput vs thread count — finds the per-node plateau\n");

    let wide_iters = env_usize("BENCH_WIDE_ITERS", 2000);
    let ns: Vec<usize> = std::env::var("BENCH_WIDE_N")
        .ok()
        .map(|s| s.split(',').filter_map(|x| x.trim().parse().ok()).collect())
        .unwrap_or_else(|| {
            let cores = std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(8);
            vec![1, 2, 4, cores, cores * 2]
        });

    println!(
        "    detected parallelism: {}",
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(0)
    );
    let mut baseline = 0.0f64;
    for (idx, &n) in ns.iter().enumerate() {
        let t = Instant::now();
        let handles: Vec<_> = (0..n)
            .map(|_| {
                std::thread::spawn(move || {
                    for _ in 0..wide_iters {
                        let _ = run_source("wat", WASMI_ADD, CapTier::Sandboxed, &[])
                            .expect("wasmi add");
                    }
                })
            })
            .collect();
        for h in handles {
            h.join().unwrap();
        }
        let elapsed = t.elapsed();
        let total_ops = (n * wide_iters) as f64;
        let throughput = total_ops / elapsed.as_secs_f64();
        if idx == 0 {
            baseline = throughput;
        }
        let scaling = if baseline > 0.0 {
            throughput / baseline
        } else {
            0.0
        };
        println!(
            "    N={:<4} {:>8} ops in {:>8.3}s  =>  {:>10.0} ops/s   ({:.2}x vs N=1)",
            n,
            n * wide_iters,
            elapsed.as_secs_f64(),
            throughput,
            scaling,
        );
    }
    println!();
}
