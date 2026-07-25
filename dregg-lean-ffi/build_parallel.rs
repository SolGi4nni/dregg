//! Small dependency-free parallel runner shared by the build script's `leanc`
//! phases. Results retain input order even though work executes concurrently.
//!
//! It also owns the ONE mechanism that bounds `lake`'s own process fan-out
//! (`LAKE_FANOUT_ENV` + `run_bounded_lake`), because that budget and the `leanc`
//! budget are the same memory budget and must not drift apart.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Mutex;

/// Resolve the bounded worker count used by both Dregg2 facet and dependency-
/// closure compilation. Invalid/zero overrides fall back to host parallelism.
/// The worker budget, and it is a MEMORY budget wearing a CPU budget's clothes.
///
/// Each `leanc` C-codegen job holds several hundred MB (~642 MB measured), so the binding
/// constraint is RAM, not cores. This used to default to `available` — every core — which is not a
/// bound at all, and it compounds: a build script is per-CRATE and per-LANE, so N concurrent lanes
/// each take the whole machine. On 2026-07-25 that arithmetic produced **55 concurrent `leanc`
/// jobs, ~35 GB**, load average 154 and 54 GB of swap on a laptop, at which point every lane —
/// including the Lean one — made essentially no progress. Nobody wrote a bug; four polite lanes
/// each took 100% of the box.
///
/// So the default is now half the cores, capped at 8. A build script is a guest on someone's
/// machine: being slow costs a cold build some minutes, being greedy costs everyone the machine.
/// `DREGG_LEANC_JOBS` raises it for a box with real headroom (and, ideally, cgroup containment —
/// `swarm-build` on hbox; there is no local equivalent).
pub fn worker_count(override_value: Option<&str>, available: usize) -> usize {
    if let Some(jobs) = override_value
        .and_then(|value| value.trim().parse::<usize>().ok())
        .filter(|&jobs| jobs > 0)
    {
        return jobs;
    }
    (available / 2).clamp(1, 8)
}

/// Run independent jobs concurrently while returning results in the exact
/// input order. A worker panic propagates through `thread::scope`; no caller can
/// mistake a partially populated result set for success.
pub fn run_indexed<T, R, F>(jobs: &[T], workers: usize, run: F) -> Vec<R>
where
    T: Sync,
    R: Send,
    F: Fn(&T) -> R + Sync,
{
    if jobs.is_empty() {
        return Vec::new();
    }

    let next = AtomicUsize::new(0);
    let results: Vec<Mutex<Option<R>>> = (0..jobs.len()).map(|_| Mutex::new(None)).collect();
    let worker_limit = workers.max(1).min(jobs.len());

    std::thread::scope(|scope| {
        for _ in 0..worker_limit {
            scope.spawn(|| loop {
                let index = next.fetch_add(1, Ordering::Relaxed);
                let Some(job) = jobs.get(index) else {
                    break;
                };
                *results[index]
                    .lock()
                    .expect("parallel result lock poisoned") = Some(run(job));
            });
        }
    });

    results
        .into_iter()
        .map(|slot| {
            slot.into_inner()
                .expect("parallel result lock poisoned")
                .expect("parallel worker returned without recording a result")
        })
        .collect()
}

// ── BOUNDING `lake`'s OWN PROCESS FAN-OUT ───────────────────────────────────────────────────────
//
// `run_indexed` above bounds the `leanc -c` jobs THIS build script spawns. It says nothing about
// the far larger fan-out of the `lake build` this script invokes first, which is where the memory
// actually goes: one `lean` per ready module, each elaborating a proof module and holding GBs.
//
// ⚠ THERE IS NO `-j`. `lake build -j 4` dies with `error: unknown short option '-j'` on BOTH
// toolchains present here — the `metatheory/lean-toolchain` pin (Lake 5.0.0-src+d024af0 / Lean
// 4.30.0) and the elan default a bare `lake` gets elsewhere in the tree (Lake 5.0.0-src+f054605 /
// Lean 4.32.1) — and neither `lake help` nor `lake build --help` lists a jobs option. A cap passed
// as `-j` was never a cap: it turned every `lake build` from this script into an instant hard
// failure (2026-07-25, commit 746f239edf).
//
// Nor does Lake read a jobs variable of its own: every `IO.getEnv` in the Lake 5.0.0 source is a
// path/cache/toolchain variable (`LAKE_*`, `LEAN_{SYSROOT,CC,AR,GITHASH}`, `ELAN_*`, `HOME`,
// `XDG_CACHE_HOME`) — there is no `LAKE_JOBS`. Lake's build jobs are Lean `Task`s
// (`Lake/Build/Job/Basic.lean`: `JobTask α := BaseIOTask (JobResult α)`), so what bounds them is
// the size of the Lean runtime's task-manager thread pool, and each ready module's task spawns ONE
// `lean` child that both elaborates and emits the `:c` facet. Pool size therefore IS the process
// fan-out, and `LEAN_NUM_THREADS` is what sizes the pool.

/// The environment variable that ACTUALLY bounds `lake`'s process fan-out.
///
/// MEASURED, not assumed (2026-07-25; Lake 5.0.0-src+d024af0 / Lean 4.30.0; 12-core, 96 GB host).
/// A scratch Lake package of 24 mutually independent modules, each holding its `lean` process ~6 s,
/// built with `lake build` from a wiped `.lake/build` while sampling
/// `pgrep -f 'bin/lean .*<pkg>' | wc -l` every 250 ms:
///
/// | env                    | peak concurrent `lean` | wall |
/// |------------------------|-----------------------|------|
/// | unset                  | **10**                | 28 s |
/// | `LEAN_NUM_THREADS=4`   | **4**                 | 51 s |
/// | `LEAN_NUM_THREADS=2`   | **2**                 | 80 s |
///
/// An exact dial, and the wall times are the same story from the other side (24 modules × 6 s ÷ N).
/// Contrast the flag it replaces: with `-j <n>` the peak is not 4 or 2 but *zero*, because `lake`
/// exits before starting a single job.
///
/// Note this variable also caps the threads used INSIDE each `lean` (it is the default for `lean`'s
/// own `-j/--threads`). That is the same direction of travel — less concurrency, less peak RSS — and
/// is why the budget is a memory budget, not a core count.
pub const LAKE_FANOUT_ENV: &str = "LEAN_NUM_THREADS";

/// How often `run_bounded_lake` samples the child count. Cheap next to a Lean build.
const FANOUT_SAMPLE: std::time::Duration = std::time::Duration::from_millis(400);

/// What a bounded `lake` run actually did.
pub struct BoundedRun {
    pub status: std::process::ExitStatus,
    /// `lake`'s stderr, captured AND echoed, so a failure can name its real cause instead of
    /// guessing (a CLI rejection and a failed elaboration are not the same diagnosis).
    pub stderr: String,
    /// Peak concurrent `lean`/`leanc` children of the `lake` process, or `None` if this host
    /// could not be sampled at all (no `pgrep`, non-unix) — in which case the cap is UNVERIFIED
    /// and the caller must say so rather than assume it held.
    pub peak_children: Option<usize>,
}

/// Whether the fan-out cap we asked for is one we actually got.
#[derive(Debug, PartialEq, Eq)]
pub enum FanoutVerdict {
    /// Sampled, and never above budget. (`peak == 0` on a warm no-op build: nothing to bound.)
    Held { peak: usize },
    /// Sampled, and the cap DID NOT APPLY — the knob has stopped working and the caller must bark.
    Exceeded { peak: usize, budget: usize },
    /// Could not sample. Not evidence of either outcome; the caller must say the cap is unverified.
    Unverified,
}

pub fn fanout_verdict(peak_children: Option<usize>, budget: usize) -> FanoutVerdict {
    match peak_children {
        None => FanoutVerdict::Unverified,
        Some(peak) if peak > budget.max(1) => FanoutVerdict::Exceeded {
            peak,
            budget: budget.max(1),
        },
        Some(peak) => FanoutVerdict::Held { peak },
    }
}

/// Run a prepared `lake` command with its process fan-out bounded to `budget`, and VERIFY the bound
/// held by counting the `lean`/`leanc` children it actually spawned.
///
/// The verification is the point. The failure this replaces was an unverified knob that had never
/// once done anything, and a version table would only move the trust: this asks the running build,
/// every time, so the day `LEAN_NUM_THREADS` stops sizing the pool the build SAYS SO instead of
/// quietly stampeding. Counting is by `pgrep -P <lake pid>` restricted to the `lean`/`leanc` process
/// names, so it sees only OUR children — a sibling lane's concurrent `lake build` cannot trip it.
///
/// An outer `LEAN_NUM_THREADS` already in the environment is an operator decision and is left
/// alone; the returned peak is then measured against that value by the caller.
pub fn run_bounded_lake(
    cmd: &mut std::process::Command,
    budget: usize,
) -> std::io::Result<BoundedRun> {
    if std::env::var_os(LAKE_FANOUT_ENV).is_none() {
        cmd.env(LAKE_FANOUT_ENV, budget.max(1).to_string());
    }
    // stdout stays inherited (lake's progress lines keep flowing); stderr is piped so a failure can
    // be quoted back verbatim, and echoed as it arrives so nothing is swallowed.
    let mut child = cmd.stderr(std::process::Stdio::piped()).spawn()?;
    let pid = child.id();
    let mut stderr_pipe = child.stderr.take();

    let peak = AtomicUsize::new(0);
    let sampled = AtomicBool::new(false);
    let finished = AtomicBool::new(false);
    let captured = Mutex::new(String::new());

    let status = std::thread::scope(|scope| {
        scope.spawn(|| {
            while !finished.load(Ordering::Relaxed) {
                if let Some(n) = count_lean_children(pid) {
                    sampled.store(true, Ordering::Relaxed);
                    peak.fetch_max(n, Ordering::Relaxed);
                }
                std::thread::sleep(FANOUT_SAMPLE);
            }
        });
        scope.spawn(|| {
            if let Some(pipe) = stderr_pipe.as_mut() {
                use std::io::Read;
                let mut buf = String::new();
                // Read to end rather than line-wise: lake's progress uses `\r`, and we want the
                // bytes, not a tidy line model.
                let mut raw = Vec::new();
                let _ = pipe.read_to_end(&mut raw);
                buf.push_str(&String::from_utf8_lossy(&raw));
                eprint!("{buf}");
                *captured.lock().expect("lake stderr lock poisoned") = buf;
            }
        });
        let status = child.wait();
        finished.store(true, Ordering::Relaxed);
        status
    })?;

    Ok(BoundedRun {
        status,
        stderr: captured.into_inner().expect("lake stderr lock poisoned"),
        peak_children: if sampled.load(Ordering::Relaxed) {
            Some(peak.load(Ordering::Relaxed))
        } else {
            None
        },
    })
}

/// Concurrent `lean`/`leanc` children of `pid`, or `None` if this host cannot be asked.
///
/// `pgrep -P <ppid> '<name regex>'` matches the child's process NAME, so `git`/`curl` helpers lake
/// may spawn are excluded and no fudge factor is needed: the count is exactly the compiler
/// processes `LEAN_NUM_THREADS` is supposed to cap. `pgrep` exits 1 with empty output when nothing
/// matches — a real answer of zero, not a failure.
#[cfg(unix)]
fn count_lean_children(pid: u32) -> Option<usize> {
    let out = std::process::Command::new("pgrep")
        .arg("-P")
        .arg(pid.to_string())
        .arg("^leanc?$")
        .output()
        .ok()?;
    Some(
        String::from_utf8_lossy(&out.stdout)
            .lines()
            .filter(|line| !line.trim().is_empty())
            .count(),
    )
}

#[cfg(not(unix))]
fn count_lean_children(_pid: u32) -> Option<usize> {
    None
}

/// The last few meaningful lines of a captured stderr, for quoting in a diagnostic.
pub fn stderr_tail(stderr: &str, lines: usize) -> String {
    let kept: Vec<&str> = stderr
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect();
    let start = kept.len().saturating_sub(lines);
    kept[start..].join(" / ")
}

/// Does this stderr say `lake` REFUSED THE INVOCATION rather than failed a build?
///
/// The distinction is not cosmetic: for ~90 minutes on 2026-07-25 a `-j` that lake rejected was
/// reported to lanes as "the current-source IR tree is not coherent", and a lane spent an hour
/// chasing an IR problem that did not exist. A CLI rejection means NO module was ever elaborated.
pub fn is_cli_rejection(stderr: &str) -> bool {
    let s = stderr.to_ascii_lowercase();
    s.contains("unknown short option")
        || s.contains("unknown long option")
        || s.contains("unknown option")
        || s.contains("unexpected argument")
        || s.contains("unknown flag")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicUsize;
    use std::time::Duration;

    /// The three verdicts, and the boundary that matters: `peak == budget` HELD (the cap is a
    /// ceiling, not a strict inequality), `peak == budget + 1` did not.
    #[test]
    fn fanout_verdict_distinguishes_held_exceeded_and_unverified() {
        assert_eq!(fanout_verdict(Some(0), 6), FanoutVerdict::Held { peak: 0 });
        assert_eq!(fanout_verdict(Some(6), 6), FanoutVerdict::Held { peak: 6 });
        assert_eq!(
            fanout_verdict(Some(7), 6),
            FanoutVerdict::Exceeded { peak: 7, budget: 6 }
        );
        // The uncapped measurement (peak 10 on a 12-core host) against the default budget: the
        // gate must call that what it is.
        assert_eq!(
            fanout_verdict(Some(10), worker_count(None, 12)),
            FanoutVerdict::Exceeded {
                peak: 10,
                budget: 6
            }
        );
        // Unsampled is NOT "held" — a cap nobody measured is the bug this module exists to end.
        assert_eq!(fanout_verdict(None, 6), FanoutVerdict::Unverified);
        // A zero budget still bounds at one process rather than reading as "unbounded".
        assert_eq!(
            fanout_verdict(Some(2), 0),
            FanoutVerdict::Exceeded { peak: 2, budget: 1 }
        );
    }

    /// REGRESSION (2026-07-25). `lake build -j 4` exits `unknown short option '-j'` without
    /// elaborating anything, and that was reported as an incoherent IR tree.
    #[test]
    fn a_rejected_flag_is_not_a_failed_build() {
        assert!(is_cli_rejection("error: unknown short option '-j'"));
        assert!(is_cli_rejection("error: unknown long option '--jobs'"));
        assert!(!is_cli_rejection(
            "error: Dregg2/Exec/FFI.lean:12:0: unknown identifier 'foo'"
        ));
        assert!(!is_cli_rejection(""));
    }

    #[test]
    fn stderr_tail_keeps_the_last_meaningful_lines() {
        assert_eq!(stderr_tail("", 3), "");
        assert_eq!(stderr_tail("a\n\n b \n\nc\n", 2), "b / c");
        assert_eq!(stderr_tail("only\n", 5), "only");
    }

    #[test]
    fn worker_override_is_bounded_away_from_zero() {
        assert_eq!(worker_count(Some("3"), 12), 3);
        // A rejected override falls back to the DEFAULT CAP, not to every core. This assertion
        // used to read `12` — that was the old contract, and the old contract is the bug below.
        assert_eq!(worker_count(Some("0"), 12), 6);
        assert_eq!(worker_count(Some("not-a-number"), 0), 1);
        assert_eq!(worker_count(None, 0), 1);
    }

    /// REGRESSION (2026-07-25). The default was `available` — every core — which is not a bound,
    /// and it compounds per crate and per lane: four concurrent lanes each took the whole machine
    /// and produced 55 concurrent `leanc` jobs at ~642 MB each (~35 GB), load average 154, and
    /// 54 GB of swap on a laptop. Every lane then made ~7% progress, including the Lean one.
    ///
    /// The invariant that matters: **an un-overridden budget never scales with the machine past a
    /// fixed ceiling**, because the constraint is RAM per job, not cores.
    #[test]
    fn the_default_budget_never_takes_the_whole_machine() {
        for cores in [4_usize, 8, 12, 14, 16, 24, 32, 64, 128] {
            let workers = worker_count(None, cores);
            assert!(
                workers <= 8,
                "{cores} cores produced {workers} workers — the ceiling is what stops \
                 N lanes from multiplying into a swap storm"
            );
            assert!(workers >= 1, "{cores} cores produced no workers");
            assert!(
                workers < cores.max(2),
                "{cores} cores produced {workers}: a budget equal to the machine is the \
                 un-bounded default this test exists to forbid"
            );
        }
        // An operator with real headroom (and ideally cgroup containment) can still say so.
        assert_eq!(worker_count(Some("32"), 8), 32);
    }

    #[test]
    fn results_keep_input_order_and_worker_bound() {
        let active = AtomicUsize::new(0);
        let peak = AtomicUsize::new(0);
        let jobs = [5_u64, 1, 4, 2, 3];
        let results = run_indexed(&jobs, 2, |delay| {
            let now = active.fetch_add(1, Ordering::SeqCst) + 1;
            peak.fetch_max(now, Ordering::SeqCst);
            std::thread::sleep(Duration::from_millis(*delay));
            active.fetch_sub(1, Ordering::SeqCst);
            delay * 10
        });
        assert_eq!(results, vec![50, 10, 40, 20, 30]);
        assert!(peak.load(Ordering::SeqCst) <= 2);
        assert!(peak.load(Ordering::SeqCst) > 1);
    }

    #[test]
    fn failures_remain_at_their_deterministic_indices() {
        let results = run_indexed(&[0, 1, 2, 3], 4, |job| *job != 2);
        assert_eq!(results, vec![true, true, false, true]);
    }
}
