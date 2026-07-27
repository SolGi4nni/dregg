//! Shared setup for the `dregg-wire` integration binaries.
//!
//! # Why a wire-delivery test has to install something
//!
//! `dregg_captp::validate_handoff` decides §6 handoff non-amplification ONLY through the verified
//! Lean gate (`dregg_captp_validate_handoff` = `Dregg2.Exec.CapTPConcrete.handoffNonAmplifyingC`),
//! routed through `dregg_captp::verified_gate`. The twin-deletion sweep (`e3f0e7b92`) deleted the
//! hand-written Rust rights lattice from that decision, so an unregistered gate is not a fallback —
//! it is a refusal of every handoff, honest ones included.
//!
//! Nothing in this crate's graph registered one, so the three `captp_delivery_tests` that need a
//! LEGITIMATE handoff to validate were RED: GAP-1's three-party handoff, GAP-2's replay test (whose
//! FIRST presentation must be ADMITTED for "the second is rejected as a replay" to mean anything),
//! and the GAP-12/13 wire-delivery → on-chain-receipt keystone. A native node avoids this by calling
//! `dregg_exec_lean::register_distributed_gates()` at startup
//! (`node/src/lib.rs::install_verified_distributed_gates`); a test binary that drives the same path
//! has to do it for itself. This is the identical omission that had `dregg-teasting`'s handoff tests
//! refusing a first, honest, `granted == held` presentation.
//!
//! This installs the REAL Lean-backed gate over the linked archive, not a permissive stand-in, so
//! the wire layer observes the true accept/reject verdict. An archive that lacks the export PANICS
//! (`dregg_lean_ffi::demand_lean`) rather than letting these binaries report `ok`.

/// Install the verified-Lean CapTP gate for THIS test process, as a native node does at startup.
/// Idempotent; call it at the top of any test that drives `validate_handoff`.
///
/// PANICS (rather than skipping) when the linked archive lacks the distributed exports, unless
/// `DREGG_TEST_ALLOW_MISSING_LEAN=1` is set out loud.
pub fn install_verified_captp_gate() -> bool {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::distributed_exports_available(),
        "the verified CapTP handoff gate (distributed_exports_available()==false)",
    ) {
        return false;
    }
    dregg_exec_lean::register_distributed_gates();
    true
}
