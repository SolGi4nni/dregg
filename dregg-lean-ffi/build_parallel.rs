//! Small dependency-free parallel runner shared by the build script's `leanc`
//! phases. Results retain input order even though work executes concurrently.

use std::sync::atomic::{AtomicUsize, Ordering};
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicUsize;
    use std::time::Duration;

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
