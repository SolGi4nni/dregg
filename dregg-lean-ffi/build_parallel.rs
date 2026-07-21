//! Small dependency-free parallel runner shared by the build script's `leanc`
//! phases. Results retain input order even though work executes concurrently.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

/// Resolve the bounded worker count used by both Dregg2 facet and dependency-
/// closure compilation. Invalid/zero overrides fall back to host parallelism.
pub fn worker_count(override_value: Option<&str>, available: usize) -> usize {
    override_value
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|&jobs| jobs > 0)
        .unwrap_or(available.max(1))
        .max(1)
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
        assert_eq!(worker_count(Some("0"), 12), 12);
        assert_eq!(worker_count(Some("not-a-number"), 0), 1);
        assert_eq!(worker_count(None, 0), 1);
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
