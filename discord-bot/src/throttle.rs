//! A tiny per-user token-bucket rate limiter — defense-in-depth for the executor-driving
//! interaction funnels (session opens / turn presses / re-verifications).
//!
//! **This state is DELIBERATELY EPHEMERAL and must stay that way.** When the persistence sweep
//! went through the bot's in-RAM stores (sessions, the crown board), this one was examined and
//! left alone on purpose. A token bucket is *recovery* state: the only thing persisting it could
//! do is carry a penalty across a restart. It authorizes nothing — a full bucket and a fresh
//! bucket are indistinguishable by construction (see [`PRUNE_THRESHOLD`], which already discards
//! idle buckets mid-run for exactly that reason), so "forgetting" on restart is not a loss of a
//! guarantee, it is the same forgetting the limiter does every few minutes anyway. The abuse
//! ceiling that actually matters is the executor's, and that is durable.
//!
//! This is NOT a security boundary. The verified executor is still the referee: every turn a
//! press drives is cap-bounded and audited on its own, and no throttle decision authorizes
//! anything. This is a conservative shock absorber so that one Discord user pressing across
//! channels cannot, by volume alone, saturate the shared single-threaded store or the STARK
//! prover pool with session/turn spam. A denied action is answered ephemerally and never reaches
//! the executor; an honest player at human speed never meets it.

use std::collections::HashMap;
use std::sync::Mutex;
use std::time::Instant;

/// Above this many tracked keys, opportunistically forget fully-refilled (idle) buckets so the
/// map stays bounded by *active* users rather than every user ever seen. A full bucket is
/// indistinguishable from a fresh one, so dropping it is state-preserving.
const PRUNE_THRESHOLD: usize = 4096;

/// A refilling token bucket for one key.
#[derive(Debug, Clone, Copy)]
struct Bucket {
    /// Tokens available right now (fractional, so sub-token refill accumulates).
    tokens: f64,
    /// When `tokens` was last brought current.
    last: Instant,
}

/// A per-`u64`-key token-bucket limiter. Construct one per funnel (a process-global) and call
/// [`RateLimiter::allow`] on each executor-driving action.
#[derive(Debug)]
pub struct RateLimiter {
    /// Bucket depth — the largest burst allowed from a cold (or long-idle) key.
    capacity: f64,
    /// Steady-state refill rate, tokens per second.
    refill_per_sec: f64,
    buckets: Mutex<HashMap<u64, Bucket>>,
}

impl RateLimiter {
    /// A limiter allowing bursts of `capacity` actions, refilling `refill_per_sec` tokens/sec.
    pub fn new(capacity: u32, refill_per_sec: f64) -> Self {
        Self {
            capacity: f64::from(capacity),
            refill_per_sec,
            buckets: Mutex::new(HashMap::new()),
        }
    }

    /// Try to spend one token for `key`. `true` ⇒ allowed (a token was consumed); `false` ⇒ the
    /// key is rate-limited right now and the caller must refuse the action.
    pub fn allow(&self, key: u64) -> bool {
        self.allow_at(key, Instant::now())
    }

    /// [`allow`](Self::allow) with an injected `now` — the deterministic core the tests drive.
    fn allow_at(&self, key: u64, now: Instant) -> bool {
        let mut buckets = self
            .buckets
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let allowed = {
            let bucket = buckets.entry(key).or_insert(Bucket {
                tokens: self.capacity,
                last: now,
            });
            // Refill for the elapsed time, capped at capacity.
            let elapsed = now.saturating_duration_since(bucket.last).as_secs_f64();
            bucket.tokens = (bucket.tokens + elapsed * self.refill_per_sec).min(self.capacity);
            bucket.last = now;
            if bucket.tokens >= 1.0 {
                bucket.tokens -= 1.0;
                true
            } else {
                false
            }
        };
        // The current key just moved below capacity (spent a token, or was already empty), so it
        // is never pruned here — only genuinely idle keys are.
        if buckets.len() > PRUNE_THRESHOLD {
            buckets.retain(|_, b| b.tokens < self.capacity);
        }
        allowed
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    // GATE (F3): N rapid actions from ONE user are BOUNDED. A cold bucket allows exactly
    // `capacity`, then refuses — the executor-driving funnel cannot be spammed faster than the
    // bucket refills.
    #[test]
    fn rapid_actions_from_one_user_are_bounded() {
        let rl = RateLimiter::new(5, 0.5); // burst 5, then 1 token / 2s
        let t0 = Instant::now();
        for i in 0..5 {
            assert!(rl.allow_at(42, t0), "burst action {i} must be allowed");
        }
        // The 6th and 7th at the same instant are REFUSED (bucket empty).
        assert!(
            !rl.allow_at(42, t0),
            "the 6th rapid action must be throttled"
        );
        assert!(!rl.allow_at(42, t0), "still throttled");
    }

    // Tokens refill over time: after draining, exactly the refilled tokens become available.
    #[test]
    fn tokens_refill_over_time() {
        let rl = RateLimiter::new(3, 1.0); // 1 token / sec
        let t0 = Instant::now();
        for _ in 0..3 {
            assert!(rl.allow_at(7, t0));
        }
        assert!(!rl.allow_at(7, t0), "drained");
        // +2s → 2 tokens back, so exactly two more are allowed, then refused again.
        let t2 = t0 + Duration::from_secs(2);
        assert!(rl.allow_at(7, t2));
        assert!(rl.allow_at(7, t2));
        assert!(!rl.allow_at(7, t2), "only the refilled tokens, no more");
    }

    // The limit is PER USER: one user being throttled never blocks another.
    #[test]
    fn limits_are_per_user() {
        let rl = RateLimiter::new(1, 0.001);
        let t0 = Instant::now();
        assert!(rl.allow_at(1, t0));
        assert!(!rl.allow_at(1, t0), "user 1 is now throttled");
        assert!(
            rl.allow_at(2, t0),
            "user 2 is unaffected by user 1's throttle"
        );
    }

    // Capacity is a ceiling: idle time cannot bank more than `capacity` tokens.
    #[test]
    fn refill_is_capped_at_capacity() {
        let rl = RateLimiter::new(2, 100.0);
        let t0 = Instant::now();
        let long_idle = t0 + Duration::from_secs(3600);
        assert!(rl.allow_at(9, long_idle));
        assert!(rl.allow_at(9, long_idle));
        assert!(
            !rl.allow_at(9, long_idle),
            "cannot bank more than capacity while idle"
        );
    }
}
