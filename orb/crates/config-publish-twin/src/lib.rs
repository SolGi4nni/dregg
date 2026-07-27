//! Twin (executable model) of the reactor's hot-reload **publication of the
//! metered rate-gate config PAIR** — the `(rate_limit, rate_window)` couple the
//! `429` accept gate reads on every connection.
//!
//! # The real seam (drorb)
//!
//! The DoS accept gates (`rate-limit <n>` / `rate-window <ms>`) are cached in two
//! separate process-global atomics, `config.rs`:
//!
//! ```text
//! static RATE_LIMIT: AtomicU64      // config.rs:167
//! static RATE_WINDOW_MS: AtomicU64  // config.rs:173
//! ```
//!
//! Two threads touch them, and they are genuinely concurrent:
//!
//! - **Reconfig watcher thread**, on a SIGHUP reload (`config::set_raw`,
//!   `config.rs:260-270`), re-derives the DoS directives and publishes them as
//!   TWO INDEPENDENT stores:
//!   ```text
//!   RATE_LIMIT.store(rate as u64, Relaxed);       // config.rs:268
//!   RATE_WINDOW_MS.store(window_ms, Relaxed);      // config.rs:269
//!   ```
//!   The doc-comment there calls the fields "retuned atomically on every
//!   (re)load" (`config.rs:263-267`) — but *each store* is atomic, the *pair* is
//!   not.
//! - **Every shard's accept hot path** reads the pair as TWO INDEPENDENT loads,
//!   in argument-evaluation order, feeding the proven `429` decision
//!   (`uring.rs:860-863`; `kqueue.rs:488-491`, both reactor families):
//!   ```text
//!   sh.standing.rate_note(peer_ip,
//!       crate::config::rate_limit(),   // RATE_LIMIT.load(Relaxed)     (read #1)
//!       crate::config::rate_window(),  // RATE_WINDOW_MS.load(Relaxed) (read #2)
//!       now)
//!   ```
//!   (`rate_window()` also drives the per-window prune throttle, `uring.rs:692-698`.)
//!
//! # The invariant this models
//!
//! A reload replaces one *generation* of the pair, `G0 = (l0, w0)`, with the
//! next, `G1 = (l1, w1)`. The proven admission decision — `rate_limit_fires` /
//! `Reactor.Stage.Rate.resp429` (`Reactor/StandingCounters.lean`) — is a function
//! of ONE consistent `(limit, window)`: "at most `limit` arrivals from a source
//! within `window`, else `429`." The running gate refines that decision only if,
//! at every instant, the pair it reads is a WHOLE generation:
//!
//! > **`observe() ∈ {G0, G1}`** — never a torn cross-product `(l1, w0)` or
//! > `(l0, w1)`.
//!
//! Two separate atomics break this. A shard's read #1 can land after the store to
//! `RATE_LIMIT` while its read #2 lands before the store to `RATE_WINDOW_MS`
//! (timeline `store_l · load_l · load_w · store_w`), yielding `(l1, w0)`; the
//! mirror timeline yields `(l0, w1)`. For a reload that tightens the clamp —
//! `G0 = (100, 1000 ms)` → `G1 = (5, 60000 ms)` ("5 requests per minute") — the
//! torn read `(100, 60000)` meters a source at the LOOSE old count over the LONG
//! new window: the counter does not age for a full minute, so the hard clamp the
//! operator just deployed is DEFEATED for that window. No generation ever authored
//! `(100, 60000)`; the running gate refines no proven config at that instant.
//!
//! This tear is an *interleaving* fault, not a memory-ordering one: it is present
//! even if both fields are `SeqCst`, because the reader can still run both loads
//! *between* the writer's two stores (witnessed by
//! [`torn_read_reached_even_seqcst`](../tests/loom.rs) in the loom suite).
//! Strengthening the per-field ordering cannot fix it — only publishing the pair
//! as a SINGLE atomic object (or under one lock / seqlock) can.
//!
//! # The fix this models
//!
//! [`PackedConfig`] packs the pair into ONE `AtomicU64`
//! (`(limit as u64) << 32 | window_ms`). The reconfig store is a single
//! `store`; the shard read is a single `load` that decomposes into `(limit,
//! window)`. Every observation is then exactly one generation, over every
//! interleaving loom can construct. Both fields fit `u32` (a limit is already
//! `u32`; a window of `u32::MAX` ms is ~49.7 days), so the pack is lossless for
//! the deployed range — see the scope note in the loom suite for the alternative
//! (a generation seqlock) when a single consistent *N*-tuple across all four
//! accept-gate fields is wanted.
//!
//! # What this twin is NOT
//!
//! It is loom evidence for the PUBLICATION atomicity of the rate-gate pair — that
//! a single-atomic (or locked) publish is tear-free where two separate atomics
//! are not. It does not model `standing.rs`'s window aging / `Instant` clock, the
//! `RwLock<Arc<Deployment>>` that carries the *serve* config (already an
//! all-or-nothing swap), or prove `config.rs` verified. The model lives in
//! [`tests/loom.rs`](../tests/loom.rs) (exhaustive) and [`tests/stress.rs`] (a
//! real-hardware hammer).
#![deny(unsafe_op_in_unsafe_fn)]

mod sync;

use sync::{AtomicU32, AtomicU64, Ordering};

/// A generation of the metered rate-gate pair: `(rate_limit, rate_window_ms)`.
pub type Gen = (u32, u32);

/// The "loose baseline" generation: 100 arrivals per 1 s window.
pub const GEN0: Gen = (100, 1_000);

/// The "hard clamp" generation a reload tightens to: 5 arrivals per 60 s window.
/// The tightening is deliberate — the torn read `(GEN1.limit-with-GEN0... )` is
/// only dangerous when the two generations disagree on BOTH fields, which a real
/// clamp-tightening reload does.
pub const GEN1: Gen = (5, 60_000);

/// Is `g` a whole authored generation (the safety predicate the reader must
/// satisfy)? Anything else is a torn cross-product of the two.
#[inline]
pub fn is_a_generation(g: Gen) -> bool {
    g == GEN0 || g == GEN1
}

/// **BROKEN — the deployed shape.** The pair as two independent atomics, exactly
/// `config.rs`'s `RATE_LIMIT` / `RATE_WINDOW_MS`. `publish` mirrors `set_raw`'s
/// two stores; `observe` mirrors the shard's `rate_limit()` then `rate_window()`
/// reads in argument order.
pub struct TornConfig {
    limit: AtomicU32,
    window: AtomicU32,
    /// The per-field ordering used for both the stores and the loads. `Relaxed`
    /// is the deployed choice; the loom suite also drives this with `SeqCst` to
    /// show the tear is an interleaving fault that survives the strongest
    /// per-field ordering.
    ord: Ordering,
}

impl TornConfig {
    pub fn new(g: Gen, ord: Ordering) -> Self {
        TornConfig {
            limit: AtomicU32::new(g.0),
            window: AtomicU32::new(g.1),
            ord,
        }
    }

    /// Reconfig-thread publish (`config::set_raw`, `config.rs:268-269`): store the
    /// limit, then store the window. Two separate stores — no pair atomicity.
    pub fn publish(&self, g: Gen) {
        self.limit.store(g.0, self.ord);
        self.window.store(g.1, self.ord);
    }

    /// Shard-thread read of the pair (`rate_note(_, rate_limit(), rate_window(),
    /// _)`, `uring.rs:861-862` / `kqueue.rs:490-491`): load the limit, then load
    /// the window. Two separate loads — the reader can slot both between the
    /// writer's two stores.
    pub fn observe(&self) -> Gen {
        let l = self.limit.load(self.ord);
        let w = self.window.load(self.ord);
        (l, w)
    }
}

/// **FIXED — single-atomic publication.** The pair packed into one `AtomicU64`,
/// so publish and observe are each ONE atomic operation and no torn cross-product
/// is representable.
pub struct PackedConfig {
    pair: AtomicU64,
}

impl PackedConfig {
    #[inline]
    fn pack(g: Gen) -> u64 {
        ((g.0 as u64) << 32) | (g.1 as u64)
    }

    #[inline]
    fn unpack(v: u64) -> Gen {
        ((v >> 32) as u32, (v & 0xffff_ffff) as u32)
    }

    pub fn new(g: Gen) -> Self {
        PackedConfig {
            pair: AtomicU64::new(Self::pack(g)),
        }
    }

    /// Reconfig-thread publish: one store of the packed pair.
    pub fn publish(&self, g: Gen) {
        self.pair.store(Self::pack(g), Ordering::Relaxed);
    }

    /// Shard-thread read: one load, decomposed. Always a whole generation.
    pub fn observe(&self) -> Gen {
        Self::unpack(self.pair.load(Ordering::Relaxed))
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;

    #[test]
    fn packed_roundtrips_both_generations() {
        for g in [GEN0, GEN1, (0, 1), (u32::MAX, u32::MAX)] {
            assert_eq!(PackedConfig::unpack(PackedConfig::pack(g)), g);
        }
    }

    #[test]
    fn generation_predicate() {
        assert!(is_a_generation(GEN0));
        assert!(is_a_generation(GEN1));
        // The two dangerous torn cross-products are NOT generations.
        assert!(!is_a_generation((GEN1.0, GEN0.1))); // (5, 1000)
        assert!(!is_a_generation((GEN0.0, GEN1.1))); // (100, 60000) — clamp defeated
    }
}
