//! The verified-Lean gate SEAM for `dregg-coord`.
//!
//! `dregg-coord` is FFI-free: it builds the wire encodings for its three verified decisions
//! (causal happened-before, 2PC decide, shared-budget resolve) and routes them through this seam,
//! never calling `dregg-lean-ffi` directly. A native node installs the Lean-backed implementation
//! once at startup (`dregg-exec-lean`'s `register_distributed_gates`); a wasm / verifier-PD / pg
//! build simply never registers one, so every gate query returns `None`.
//!
//! # ⚠ AN ABSENT GATE REFUSES. ALL THREE OF THEM.
//!
//! This doc used to end "…and the native-Rust differential sibling decides — exactly the behavior
//! the deleted `no-lean-link` feature used to compile in," and the trait below used to add that the
//! gate "is never allowed to break a live coordinator path, only to make it verified." Both were
//! true when this seam was written and BOTH ARE NOW BACKWARDS: the twin-deletion sweep
//! (`e3f0e7b92`, 2026-07-24) removed the native sibling from all three LIVE paths in favour of
//! fail-closed refusals, and updated each decision site's own comment without touching this file.
//! At HEAD an unregistered gate does not degrade a coordinator to unverified — it stops it:
//!
//! | decision | consumer | gate absent ⇒ |
//! |---|---|---|
//! | causal happened-before | `causal::happened_before_verified` | `lean_happened_before(..).unwrap_or(false)` — reports NOT ordered for every pair. |
//! | 2PC decide | `atomic`'s `evaluate_votes` | `evaluate_votes_no_gate()` — a `Proposing` state ABORTS rather than commit. |
//! | shared-budget resolve | `shared_budget`'s tau resolution | `resolve_ordering_no_gate()` — REJECTS every debit, balance untouched. |
//!
//! The native siblings still exist, but as `#[cfg(test)]`/differential objects that the live path no
//! longer reaches. A production coordinator MUST install the gate; the same is true of any test
//! binary that drives one of these decisions and expects a non-refusal.
//!
//! The wire grammars are documented at the seam impl in `dregg-exec-lean`; the encode/decode logic
//! that produces / consumes them lives here in `dregg-coord` (it is pure, FFI-free).

use std::sync::OnceLock;

/// The verified 2PC verdict the gate returns (mirrors the Lean `Decision2pc`, kept crate-local so
/// the `dregg-lean-ffi` type never leaks across the seam).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict2pc {
    /// Threshold reached — commit.
    Commit,
    /// Threshold impossible — abort.
    Abort,
    /// Still waiting for votes.
    Pending,
}

/// The verified-Lean coordination gate. Implemented by `dregg-exec-lean` (the single FFI boundary)
/// and injected on a native node; absent (⇒ `gate()` is `None`) on FFI-free targets.
///
/// Each method returns `None` when the verified gate is unavailable (archive not linked / export
/// absent / wire error). ⚠ That `None` is a REFUSAL on all three live paths, not a fallback to the
/// native-Rust decision — see the module docs above for the per-decision table. (This doc used to
/// say the opposite: "the gate is never allowed to break a live coordinator path, only to make it
/// verified." Not installing it breaks every one of them.)
pub trait CoordVerifiedGate: Send + Sync {
    /// Whether the verified distributed-exports module is linked and queryable.
    fn distributed_exports_available(&self) -> bool;
    /// Decide `happened-before` over the interned causal-DAG wire (`"G=…;a=…;b=…"`).
    fn happened_before(&self, wire: &str) -> Option<bool>;
    /// Decide the 2PC verdict over the vote-tally wire (`"y=…;n=…;N=…;t=…"`).
    fn decide_2pc(&self, wire: &str) -> Option<Verdict2pc>;
    /// Resolve the shared-budget ordering; returns the reply wire
    /// (`"R=…;b=…;a=…"`) for the caller to parse, or `None` if unavailable.
    fn shared_budget(&self, wire: &str) -> Option<String>;
}

static GATE: OnceLock<Box<dyn CoordVerifiedGate>> = OnceLock::new();

/// Install the verified-Lean coordination gate (call once at node startup). A second call is a
/// no-op (the first registration wins) — the seam is process-global like the linked archive it
/// fronts.
pub fn register_coord_verified_gate(gate: Box<dyn CoordVerifiedGate>) {
    let _ = GATE.set(gate);
}

/// The installed gate, or `None` when no verified gate is registered (every FFI-free target, and a
/// native build before registration) — in which case the native-Rust differential decides.
pub(crate) fn gate() -> Option<&'static dyn CoordVerifiedGate> {
    GATE.get().map(|b| b.as_ref())
}
