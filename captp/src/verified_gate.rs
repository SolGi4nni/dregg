//! The verified-Lean gate SEAM for `dregg-captp`.
//!
//! `dregg-captp` is FFI-free: it builds the wire encodings for its three verified decisions
//! (handoff non-amplification, process-drop GC verdict, pipeline FIFO resolve) and routes them
//! through this seam, never calling `dregg-lean-ffi` directly. A native node installs the
//! Lean-backed implementation once at startup (`dregg-exec-lean`'s `register_distributed_gates`);
//! a wasm / verifier-PD / pg build never registers one, so every gate query returns `None`.
//!
//! # ⚠ AN ABSENT GATE DOES NOT MEAN THE SAME THING ON ALL THREE PATHS
//!
//! It is NOT true that "no gate registered ⇒ the native Rust sibling decides". That was the
//! behaviour when this seam was introduced (`e2743afae`, 2026-06-22) and it is still the behaviour
//! on two of the three paths, but the twin-deletion sweep (`e3f0e7b92`, 2026-07-24) changed the
//! handoff path to a HARD REFUSAL and this doc was not updated with it. The drift is why an honest
//! `granted == held` presentation was refused as `Amplification` in every binary that links captp
//! and forgets to register — with nothing anywhere saying so. Per path, at HEAD:
//!
//! | path | consumer | gate absent ⇒ |
//! |---|---|---|
//! | §6 handoff non-amplification | [`crate::handoff::validate_handoff`] | **FAILS CLOSED — REFUSES.** No fallback: the Rust rights lattice was DELETED from that decision. Reported as [`crate::handoff::HandoffError::VerifiedGateUnavailable`], NOT as `Amplification`, so "the check could not run" is distinguishable from "the check ran and found an attack". |
//! | `process_drop` GC verdict | [`crate::gc::ExportGcManager::process_drop_with_session`] | falls back — the native Rust session-refcount mutation's own verdict decides (`verified.unwrap_or(native)`). |
//! | pipeline FIFO resolve | [`crate::pipeline`]'s drain reorder | falls back — the native FIFO `drained` order is returned unchanged. |
//!
//! So the seam is uniform (`None` everywhere) and the CONSEQUENCE is not. A native vat MUST call
//! `register_distributed_gates()`; on the handoff path that is not an optimisation, it is the
//! difference between a working vat and one that refuses every handoff it is ever offered.

use std::sync::OnceLock;

/// The verified-Lean CapTP gate. Implemented by `dregg-exec-lean` (the single FFI boundary) and
/// injected on a native node; absent (⇒ `gate()` is `None`) on FFI-free targets.
///
/// Each method returns `None` when the verified gate is unavailable (archive not linked / export
/// absent / wire error). What the CALLER does with that `None` is per-path and is NOT uniform —
/// see the module docs above: the GC and pipeline consumers fall back to their native Rust
/// siblings, and the §6 handoff consumer REFUSES.
pub trait CaptpVerifiedGate: Send + Sync {
    /// Whether the verified distributed-exports module is linked and queryable.
    fn distributed_exports_available(&self) -> bool;
    /// Decide §6 handoff non-amplification over the wire (`"h=…;g=…;he=…;ge=…"`).
    ///
    /// ⚠ `None` here is a REFUSAL, not a fallback: `validate_handoff` has no second decider for
    /// this verdict.
    fn handoff_non_amplifying(&self, wire: &str) -> Option<bool>;
    /// Decide a `process_drop` GC verdict; returns the reply wire (`"S=<tag>;t=…"`) for the caller
    /// to parse, or `None` if unavailable (⇒ the native Rust mutation's verdict stands).
    fn process_drop(&self, wire: &str) -> Option<String>;
    /// Resolve a pipeline drain order; returns the reply wire (`"D=…;q=…"`) for the caller to
    /// parse, or `None` if unavailable (⇒ the native FIFO drain order stands).
    fn pipeline_resolve(&self, wire: &str) -> Option<String>;
}

static GATE: OnceLock<Box<dyn CaptpVerifiedGate>> = OnceLock::new();

/// Install the verified-Lean CapTP gate (call once at node startup). A second call is a no-op.
pub fn register_captp_verified_gate(gate: Box<dyn CaptpVerifiedGate>) {
    let _ = GATE.set(gate);
}

/// The installed gate, or `None` when none is registered (every FFI-free target / pre-registration).
pub(crate) fn gate() -> Option<&'static dyn CaptpVerifiedGate> {
    GATE.get().map(|b| b.as_ref())
}
