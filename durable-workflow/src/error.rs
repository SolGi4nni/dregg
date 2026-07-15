//! `error` — the step error taxonomy and the retry policy the orchestration honors.
//!
//! A durable workflow used to treat every step failure the same: any `Err` aborted
//! the whole workflow, permanently, with no retry and no classification. That is the
//! wrong default for a hosting substrate — a runner that momentarily could not reach
//! an isolate host, or whose step timed out, is a *transient* fault the workflow
//! should retry with backoff; a step whose input is malformed or whose program
//! faulted is a *permanent* fault that must fail fast.
//!
//! [`StepError`] carries that classification. A [`StepRunner`](crate::StepRunner)
//! returns it, and the orchestration reads it back — deterministically, from the
//! recorded activity error — to decide whether to retry ([`RetryPolicy`]) or fail.
//! The classification survives the activity boundary as a small wire encoding
//! ([`StepError::to_wire`] / [`StepError::from_wire`]) so the retry decision is made
//! from durable history and is therefore replay-safe.

use serde::{Deserialize, Serialize};
use std::time::Duration;

/// Whether a step failure is worth retrying.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum StepErrorKind {
    /// A retryable fault: a timeout, a lost connection to an isolate host, a
    /// resource-temporarily-unavailable. The orchestration retries it with backoff
    /// up to the [`RetryPolicy`] budget.
    Transient,
    /// A non-retryable fault: malformed input, a program fault, a policy refusal.
    /// The orchestration fails the workflow immediately — retrying cannot help.
    Permanent,
}

/// A classified step failure returned by a [`StepRunner`](crate::StepRunner).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StepError {
    pub kind: StepErrorKind,
    pub message: String,
}

impl StepError {
    /// A retryable fault.
    pub fn transient(message: impl Into<String>) -> StepError {
        StepError {
            kind: StepErrorKind::Transient,
            message: message.into(),
        }
    }

    /// A non-retryable fault.
    pub fn permanent(message: impl Into<String>) -> StepError {
        StepError {
            kind: StepErrorKind::Permanent,
            message: message.into(),
        }
    }

    /// Whether this fault is worth retrying.
    pub fn is_transient(&self) -> bool {
        self.kind == StepErrorKind::Transient
    }

    /// The sentinel prefix that marks an activity error string as a classified
    /// [`StepError`]. An activity `Err` that does NOT begin with this (e.g. a
    /// duroxide join error, a serde failure) is treated as permanent by
    /// [`StepError::from_wire`].
    const WIRE_PREFIX: &'static str = "STEPERR/1:";

    /// Encode this error into the activity `Err` string so the orchestration can
    /// classify it deterministically on replay. `kind` is a single leading tag byte
    /// (`T`/`P`) so decoding never depends on JSON field order.
    pub fn to_wire(&self) -> String {
        let tag = match self.kind {
            StepErrorKind::Transient => 'T',
            StepErrorKind::Permanent => 'P',
        };
        format!("{}{}{}", Self::WIRE_PREFIX, tag, self.message)
    }

    /// Decode an activity `Err` string back into a [`StepError`]. Anything not
    /// carrying our sentinel is treated as a permanent fault carrying the raw string
    /// — the safe default (an unclassified failure is never silently retried).
    pub fn from_wire(s: &str) -> StepError {
        if let Some(rest) = s.strip_prefix(Self::WIRE_PREFIX) {
            let mut chars = rest.chars();
            match chars.next() {
                Some('T') => return StepError::transient(chars.as_str().to_string()),
                Some('P') => return StepError::permanent(chars.as_str().to_string()),
                _ => {}
            }
        }
        StepError::permanent(s.to_string())
    }
}

impl std::fmt::Display for StepError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let k = match self.kind {
            StepErrorKind::Transient => "transient",
            StepErrorKind::Permanent => "permanent",
        };
        write!(f, "{k}: {}", self.message)
    }
}

impl std::error::Error for StepError {}

/// How the orchestration retries a transient step failure. Serialized into the
/// [`WorkloadRun`](crate::WorkloadRun) input so the policy is part of durable history
/// and the retry decision replays identically.
///
/// A default policy (`max_attempts = 1`) never retries — byte-identical to the
/// original abort-on-first-error behavior — so existing workloads are unchanged.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct RetryPolicy {
    /// Total attempts for a step, including the first. `1` = no retry.
    pub max_attempts: u32,
    /// The first backoff delay (before attempt 2); doubles each subsequent attempt.
    pub base_backoff_ms: u64,
    /// The backoff ceiling — exponential growth is clamped here.
    pub max_backoff_ms: u64,
    /// A per-attempt wall-clock deadline (milliseconds) the runner enforces, `0` =
    /// no deadline. A runner that supports cancellation kills the work and returns a
    /// transient timeout when an attempt exceeds this.
    pub step_timeout_ms: u64,
}

impl Default for RetryPolicy {
    fn default() -> RetryPolicy {
        RetryPolicy {
            max_attempts: 1,
            base_backoff_ms: 0,
            max_backoff_ms: 0,
            step_timeout_ms: 0,
        }
    }
}

impl RetryPolicy {
    /// Retry a transient failure up to `max_attempts` times, exponential backoff from
    /// `base` capped at `max`.
    pub fn retrying(max_attempts: u32, base: Duration, max: Duration) -> RetryPolicy {
        RetryPolicy {
            max_attempts: max_attempts.max(1),
            base_backoff_ms: base.as_millis() as u64,
            max_backoff_ms: max.as_millis() as u64,
            step_timeout_ms: 0,
        }
    }

    /// Set a per-attempt wall-clock deadline the runner enforces.
    pub fn with_step_timeout(mut self, timeout: Duration) -> RetryPolicy {
        self.step_timeout_ms = timeout.as_millis() as u64;
        self
    }

    /// The backoff delay before `attempt` (1-based; the delay applies before attempt
    /// `n+1`). Exponential in the attempt number, clamped to `max_backoff_ms`.
    pub fn backoff_before(&self, next_attempt: u32) -> Duration {
        if self.base_backoff_ms == 0 || next_attempt <= 1 {
            return Duration::from_millis(0);
        }
        // next_attempt=2 → base, 3 → 2*base, 4 → 4*base, ...
        let shift = (next_attempt - 2).min(32);
        let scaled = self.base_backoff_ms.saturating_mul(1u64 << shift);
        let capped = if self.max_backoff_ms == 0 {
            scaled
        } else {
            scaled.min(self.max_backoff_ms)
        };
        Duration::from_millis(capped)
    }

    /// The per-attempt deadline, if any.
    pub fn step_timeout(&self) -> Option<Duration> {
        if self.step_timeout_ms == 0 {
            None
        } else {
            Some(Duration::from_millis(self.step_timeout_ms))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wire_roundtrip_preserves_classification() {
        let t = StepError::transient("host unreachable");
        let p = StepError::permanent("bad input: x");
        assert_eq!(StepError::from_wire(&t.to_wire()), t);
        assert_eq!(StepError::from_wire(&p.to_wire()), p);
        // Embedded colons/newlines survive (message is the tail, not parsed).
        let weird = StepError::permanent("expr: not a: recognized\nexpr");
        assert_eq!(StepError::from_wire(&weird.to_wire()), weird);
    }

    #[test]
    fn unclassified_error_is_permanent() {
        // A raw duroxide/serde error string carries no sentinel → never retried.
        let e = StepError::from_wire("RunWorkload: join error: panicked");
        assert_eq!(e.kind, StepErrorKind::Permanent);
        assert!(e.message.contains("join error"));
    }

    #[test]
    fn backoff_is_exponential_and_capped() {
        let p = RetryPolicy::retrying(5, Duration::from_millis(10), Duration::from_millis(50));
        assert_eq!(p.backoff_before(1), Duration::from_millis(0)); // no delay before 1st
        assert_eq!(p.backoff_before(2), Duration::from_millis(10));
        assert_eq!(p.backoff_before(3), Duration::from_millis(20));
        assert_eq!(p.backoff_before(4), Duration::from_millis(40));
        assert_eq!(p.backoff_before(5), Duration::from_millis(50)); // capped, not 80
    }

    #[test]
    fn default_never_retries() {
        let p = RetryPolicy::default();
        assert_eq!(p.max_attempts, 1);
        assert_eq!(p.backoff_before(2), Duration::from_millis(0));
        assert!(p.step_timeout().is_none());
    }
}
