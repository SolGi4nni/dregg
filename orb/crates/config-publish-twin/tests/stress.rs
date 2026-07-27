//! Real-hardware hammer (NOT loom): a writer flips the rate-gate pair between the
//! two generations while reader threads pound `observe()`. It witnesses on real
//! atomics what the loom suite proves over all schedules — the deployed
//! two-atomic shape tears (a torn read is observed within a bounded budget), and
//! the packed single-atomic shape never does.
//!
//! Run with:
//! ```text
//! cargo test -p config-publish-twin --release --test stress -- --nocapture
//! ```
//!
//! This is a WITNESS, not a proof: a run that happens to observe zero tears on the
//! torn path does not mean the race is absent (it is proven present by loom). The
//! packed-path assertion (zero tears) is the load-bearing one here.
#![cfg(not(loom))]

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::thread;

use config_publish_twin::{GEN0, GEN1, PackedConfig, TornConfig, is_a_generation};

const READERS: usize = 8;
const FLIPS: u64 = 200_000;

#[test]
fn torn_path_tears_and_packed_path_never_does() {
    // ---- deployed two-atomic shape: expect to WITNESS at least one tear ----
    let torn = Arc::new(TornConfig::new(GEN0, Ordering::Relaxed));
    let stop = Arc::new(AtomicBool::new(false));
    let torn_count = Arc::new(AtomicU64::new(0));

    let readers: Vec<_> = (0..READERS)
        .map(|_| {
            let c = torn.clone();
            let s = stop.clone();
            let n = torn_count.clone();
            thread::spawn(move || {
                while !s.load(Ordering::Relaxed) {
                    if !is_a_generation(c.observe()) {
                        n.fetch_add(1, Ordering::Relaxed);
                    }
                }
            })
        })
        .collect();

    for i in 0..FLIPS {
        torn.publish(if i & 1 == 0 { GEN1 } else { GEN0 });
    }
    stop.store(true, Ordering::Relaxed);
    for r in readers {
        r.join().unwrap();
    }

    let tears = torn_count.load(Ordering::Relaxed);
    eprintln!(
        "stress: two-atomic pair over {FLIPS} flips x {READERS} readers — {tears} torn reads observed"
    );
    // A witness, not an assertion: hardware may serialize a given run. The proof
    // that the tear EXISTS is the loom suite; here we just report the count.

    // ---- packed single-atomic fix: assert ZERO tears, ever ----
    let packed = Arc::new(PackedConfig::new(GEN0));
    let stop2 = Arc::new(AtomicBool::new(false));
    let packed_count = Arc::new(AtomicU64::new(0));

    let readers: Vec<_> = (0..READERS)
        .map(|_| {
            let c = packed.clone();
            let s = stop2.clone();
            let n = packed_count.clone();
            thread::spawn(move || {
                while !s.load(Ordering::Relaxed) {
                    if !is_a_generation(c.observe()) {
                        n.fetch_add(1, Ordering::Relaxed);
                    }
                }
            })
        })
        .collect();

    for i in 0..FLIPS {
        packed.publish(if i & 1 == 0 { GEN1 } else { GEN0 });
    }
    stop2.store(true, Ordering::Relaxed);
    for r in readers {
        r.join().unwrap();
    }

    let packed_tears = packed_count.load(Ordering::Relaxed);
    eprintln!(
        "stress: packed pair over {FLIPS} flips x {READERS} readers — {packed_tears} torn reads observed"
    );
    assert_eq!(
        packed_tears, 0,
        "packed single-atomic publication produced a torn read — the fix is broken"
    );
}
