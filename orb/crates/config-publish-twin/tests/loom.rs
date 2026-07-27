//! Exhaustive schedule check of the metered rate-gate **pair publication**
//! (`config::set_raw`'s `RATE_LIMIT`/`RATE_WINDOW_MS` stores vs the shard accept
//! gate's `rate_limit()`/`rate_window()` reads — `uring.rs:860-863`,
//! `kqueue.rs:488-491`).
//!
//! Run with:
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test -p config-publish-twin --release --test loom -- --test-threads=1
//! ```
//!
//! # The claim (config.rs, drorb)
//!
//! A SIGHUP reload replaces generation `G0 = (l0, w0)` of the rate-gate pair with
//! `G1 = (l1, w1)`. The proven `429` decision (`rate_limit_fires` /
//! `Reactor.Stage.Rate.resp429`, `Reactor/StandingCounters.lean`) is a function of
//! ONE consistent `(limit, window)`. The running gate refines it only if every
//! read observes a WHOLE generation — `observe() ∈ {G0, G1}`. The deployed
//! `config.rs` publishes the pair as two independent stores and each shard reads
//! it as two independent loads, so a read can interleave BETWEEN the two stores
//! and see a torn cross-product `(l1, w0)` or `(l0, w1)`.
//!
//! # What this suite covers vs the real deploy (read before trusting)
//!
//! - MODELS, over every interleaving of one reconfig publish against one shard
//!   read: (1) [`torn_read_reached`] — the DEPLOYED two-atomic shape (`Relaxed`,
//!   exactly `config.rs`) admits a torn read; loom reaches it, including the
//!   clamp-defeating `(l0, w1)`. (2) [`torn_read_reached_even_seqcst`] — the tear
//!   survives `SeqCst` on both fields, so it is an interleaving fault, not a
//!   memory-ordering one: strengthening the per-field ordering cannot fix it.
//!   (3) [`packed_read_is_always_a_whole_generation`] — the single-`AtomicU64`
//!   fix makes every observation a whole generation, over all schedules.
//! - DOES NOT model: `standing.rs` window aging / the `Instant` clock, the
//!   `max-connections` and `slowloris-timeout` fields (each read ALONE, so no
//!   pair-atomicity requirement; a single consistent 4-tuple would need the
//!   seqlock in the scope note below), the `RwLock<Arc<Deployment>>` serve-config
//!   swap (already all-or-nothing), or the SIGHUP/parse path. This is loom
//!   evidence for the PAIR publication only — not a proof that `config.rs` is
//!   verified.
//!
//! # Scope note — the general fix
//!
//! [`PackedConfig`] fixes the `(limit, window)` PAIR because both fields fit
//! `u32`. If an operator needs joint consistency across all FOUR accept-gate
//! fields (`max_connections`, `rate_limit`, `rate_window`, `slowloris`), or a
//! window wider than `u32::MAX` ms, the pack does not scale; the general answer
//! is a generation seqlock (an even/odd counter with `SeqCst` fences, the reader
//! retrying while the counter is odd or changed) or publishing the whole tuple in
//! one `Arc` the reader clones — the same all-or-nothing discipline the serve
//! config's `RwLock<Arc<Deployment>>` already uses.
#![cfg(loom)]

use std::sync::atomic::{AtomicBool as StdBool, AtomicUsize as StdUsize, Ordering as StdOrd};

use loom::sync::Arc;
use loom::sync::atomic::Ordering as LoomOrd;
use loom::thread;

use config_publish_twin::{GEN0, GEN1, PackedConfig, TornConfig, is_a_generation};

/// Schedules explored, per test, for the report.
static ITERS_PACKED: StdUsize = StdUsize::new(0);
static ITERS_TORN: StdUsize = StdUsize::new(0);
static ITERS_TORN_SC: StdUsize = StdUsize::new(0);

/// PRIMARY ASSURANCE. One reconfig publish (`G0 → G1`) races one shard read of
/// the packed pair. Over EVERY interleaving loom constructs, the observed pair is
/// a WHOLE generation — never a torn cross-product. Green over all schedules = the
/// single-`AtomicU64` publication is tear-free.
#[test]
fn packed_read_is_always_a_whole_generation() {
    loom::model(|| {
        ITERS_PACKED.fetch_add(1, StdOrd::Relaxed);

        let cfg = Arc::new(PackedConfig::new(GEN0));

        let w = cfg.clone();
        let writer = thread::spawn(move || w.publish(GEN1));

        // The shard reads the pair on its accept hot path, concurrently.
        let seen = cfg.observe();

        writer.join().unwrap();

        assert!(
            is_a_generation(seen),
            "TORN READ on the FIXED path: shard observed {seen:?}, which is neither \
             G0 {GEN0:?} nor G1 {GEN1:?} — the packed publication is not atomic",
        );
        // And a read after the publish settles must be exactly G1.
        assert_eq!(
            cfg.observe(),
            GEN1,
            "post-publish read must be the whole new generation"
        );
    });

    eprintln!(
        "loom: packed_read_is_always_a_whole_generation — {} schedules explored, \
         every observation was a whole generation",
        ITERS_PACKED.load(StdOrd::Relaxed)
    );
}

/// TEETH (the deployed shape). Two INDEPENDENT `Relaxed` atomics — exactly
/// `config.rs`'s `RATE_LIMIT`/`RATE_WINDOW_MS` and the shard's
/// `rate_limit()`/`rate_window()` reads. One reconfig publish `G0 → G1` races one
/// shard read. loom finds the interleaving where the read lands BETWEEN the two
/// stores and observes a torn cross-product — proving the deployed pair
/// publication is NOT atomic, and that the green packed test above is meaningful
/// (loom WOULD flag a torn read; the packed path never produces one).
///
/// The bad state is detected-and-flagged (not asserted-against), so the test
/// passes exactly when loom REACHES a torn read — the static-flag teeth pattern
/// `conn-limit-twin` / `ring-twin` / the SplitSend litmus use. It separately
/// records the SECURITY-relevant torn read `(l0, w1)` (loose old limit over the
/// long new window), which defeats the freshly-tightened DoS clamp.
#[test]
fn torn_read_reached() {
    static TORN_REACHED: StdBool = StdBool::new(false);
    static CLAMP_DEFEAT_REACHED: StdBool = StdBool::new(false);

    // The two torn cross-products, named for the report.
    const CLAMP_DEFEAT: (u32, u32) = (GEN0.0, GEN1.1); // (100, 60000): loose count, long window
    const OVER_TIGHT: (u32, u32) = (GEN1.0, GEN0.1); // (5, 1000): tight count, short window

    loom::model(|| {
        ITERS_TORN.fetch_add(1, StdOrd::Relaxed);

        let cfg = Arc::new(TornConfig::new(GEN0, LoomOrd::Relaxed));

        let w = cfg.clone();
        let writer = thread::spawn(move || w.publish(GEN1));

        let seen = cfg.observe();

        writer.join().unwrap();

        if !is_a_generation(seen) {
            TORN_REACHED.store(true, StdOrd::Relaxed);
            if seen == CLAMP_DEFEAT {
                CLAMP_DEFEAT_REACHED.store(true, StdOrd::Relaxed);
            }
            assert!(
                seen == CLAMP_DEFEAT || seen == OVER_TIGHT,
                "unexpected torn value {seen:?}: only the two cross-products are reachable"
            );
        }
    });

    assert!(
        TORN_REACHED.load(StdOrd::Relaxed),
        "loom found NO torn read with two independent atomics — the teeth test is \
         broken; the green packed test no longer witnesses that single-atomic \
         publication is load-bearing"
    );
    assert!(
        CLAMP_DEFEAT_REACHED.load(StdOrd::Relaxed),
        "loom did not reach the clamp-defeating torn read {CLAMP_DEFEAT:?} \
         (loose old limit over the long new window)"
    );
    eprintln!(
        "loom: torn_read_reached — {} schedules; TORN read REACHED (as expected), \
         including the clamp-defeat {CLAMP_DEFEAT:?}: the deployed two-atomic pair \
         publication is not atomic",
        ITERS_TORN.load(StdOrd::Relaxed)
    );
}

/// TEETH (ordering is not the fix). The IDENTICAL two-atomic model, but every
/// store and load is `SeqCst`. The torn read is STILL reachable — the reader runs
/// both loads between the writer's two stores regardless of per-field ordering.
/// This pins the honest conclusion: the tear is an interleaving fault over a
/// non-atomic composite, so no strengthening of the individual atomics'
/// ordering fixes it; only a single atomic (or a lock / seqlock) does.
#[test]
fn torn_read_reached_even_seqcst() {
    static TORN_REACHED_SC: StdBool = StdBool::new(false);

    loom::model(|| {
        ITERS_TORN_SC.fetch_add(1, StdOrd::Relaxed);

        let cfg = Arc::new(TornConfig::new(GEN0, LoomOrd::SeqCst));

        let w = cfg.clone();
        let writer = thread::spawn(move || w.publish(GEN1));

        let seen = cfg.observe();

        writer.join().unwrap();

        if !is_a_generation(seen) {
            TORN_REACHED_SC.store(true, StdOrd::Relaxed);
        }
    });

    assert!(
        TORN_REACHED_SC.load(StdOrd::Relaxed),
        "loom found NO torn read even with SeqCst on both fields — if this ever \
         fails, re-examine the claim that the tear is ordering-independent"
    );
    eprintln!(
        "loom: torn_read_reached_even_seqcst — {} schedules; TORN read REACHED under \
         SeqCst too: the fix must be a single atomic / lock, NOT a stronger per-field \
         ordering",
        ITERS_TORN_SC.load(StdOrd::Relaxed)
    );
}
