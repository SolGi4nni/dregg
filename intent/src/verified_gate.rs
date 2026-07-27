//! The verified-Lean gate SEAM for `dregg-intent`.
//!
//! `dregg-intent` is FFI-free: `verified_settle` builds the per-leg asset-projection wire and routes
//! it through this seam, never calling `dregg-lean-ffi` directly. A native node installs the
//! Lean-backed implementation once at startup (`dregg-exec-lean`'s `register_distributed_gates`); a
//! wasm / verifier-PD / pg build never registers one, so every gate query returns `None`.
//!
//! ⚠ **An absent gate REFUSES the ring; it does not skip a cross-check.** This doc used to end
//! "…so the cross-check is skipped (the in-process verified transition stands on its own)", which
//! was true until the twin-deletion sweep (`e3f0e7b92`, 2026-07-24) INVERTED the polarity: the
//! export is now the AUTHORITY per leg and the in-process Rust fold is the cross-checked
//! differential. With no gate registered, `ffi::settle_leg` returns
//! `Err(VerifiedSettleError::FfiUnavailable)`, which refuses the leg — and since a ring is
//! all-or-none, the whole ring (`verified_settle::settle_leg_authoritative`, whose own comment says
//! so). A production node MUST install the gate, as must any test binary or app that settles a
//! non-empty ring; `starbridge-apps/tussle` and `dreggnet-catalog`'s private bazaar both learned
//! this the same way.

use std::sync::OnceLock;

/// The verified-Lean intent gate. Implemented by `dregg-exec-lean` (the single FFI boundary) and
/// injected on a native node; absent (⇒ `gate()` is `None`) on FFI-free targets.
pub trait IntentVerifiedGate: Send + Sync {
    /// Settle one ring leg through the REAL verified executor export `dregg_record_kernel_step`
    /// over the leg's asset projection. `input` is the encoded ledger+leg wire; the reply is the
    /// post-state wire (`{"cells":…,"ok":B}`). `Err` only on FFI unavailability / wire errors.
    fn record_kernel_step(&self, input: &str) -> Result<String, String>;
}

static GATE: OnceLock<Box<dyn IntentVerifiedGate>> = OnceLock::new();

/// Install the verified-Lean intent gate (call once at node startup). A second call is a no-op.
pub fn register_intent_verified_gate(gate: Box<dyn IntentVerifiedGate>) {
    let _ = GATE.set(gate);
}

/// The installed gate, or `None` when none is registered (every FFI-free target / pre-registration).
pub(crate) fn gate() -> Option<&'static dyn IntentVerifiedGate> {
    GATE.get().map(|b| b.as_ref())
}
