//! Shared test support for the `dregg-teasting` integration binaries.
//!
//! # Why a handoff test has to install something
//!
//! `dregg_captp::validate_handoff` decides §6 non-amplification ONLY through the verified Lean gate
//! (`dregg_captp_validate_handoff` = `Dregg2.Exec.CapTPConcrete.handoffNonAmplifyingC`), routed
//! through `dregg_captp::verified_gate`. The twin-deletion sweep (`e3f0e7b92`) removed the
//! hand-written Rust rights lattice from that live decision, so with no gate registered the verdict
//! is not "fall back to Rust" — it is a REFUSAL.
//!
//! Nothing in this crate's graph registered one, so `captp_sessions::test_handoff_certificate_flow`
//! and `fault_byzantine::test_byzantine_certificate_replay_rejected` both failed on a first, honest,
//! `granted == held` presentation. A native node avoids this by calling
//! `dregg_exec_lean::register_distributed_gates()` at startup
//! (`node/src/lib.rs::install_verified_distributed_gates`); a test binary that drives the handoff
//! path has to do the same thing, and this module is where this suite does it.
//!
//! # This is the REAL gate, not a permissive stand-in
//!
//! [`install_verified_captp_gate`] installs `dregg-exec-lean`'s Lean-backed implementation, so both
//! poles are decided by the machine-checked rule over the linked archive: an attenuating handoff is
//! ADMITTED and an amplifying one is REFUSED as `Amplification`. That matters — `captp`'s own
//! integration tests use an `AssumeNonAmplifyingGate` that answers `Some(true)` unconditionally,
//! which is fine for tests probing OTHER properties and useless for probing this one. A stand-in
//! here would have turned "the handoff path works" into "the handoff path compiles".
//!
//! # It cannot silently do nothing
//!
//! The archive-absent case routes through `dregg_lean_ffi::demand_lean`, which PANICS by default
//! (`DREGG_TEST_REQUIRE_LEAN` is armed unless explicitly disarmed) naming the missing capability,
//! rather than returning and letting the caller print `ok` for a test that asserted nothing about
//! the verified gate. `tests/captp_verified_gate_poles.rs` is the canary for the registration
//! itself: delete the call there and its amplifying poles report `VerifiedGateUnavailable`.

/// Install the verified-Lean CapTP gate for THIS test process, exactly as a native node does at
/// startup. Idempotent (the underlying `OnceLock` ignores a second install); call it at the top of
/// any test that drives `validate_handoff`.
///
/// PANICS (rather than skipping) when the linked archive lacks the distributed exports, unless the
/// developer opt-out `DREGG_TEST_ALLOW_MISSING_LEAN=1` is set out loud — in which case it returns
/// `false` after printing that the resulting green is evidence about the Rust half only.
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
