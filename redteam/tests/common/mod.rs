//! Shared setup for the adversarial binaries.
//!
//! # An attack suite has to install the defence it is attacking
//!
//! `dregg_captp::validate_handoff` decides §6 handoff non-amplification ONLY through the verified
//! Lean gate (`dregg_captp_validate_handoff` = `Dregg2.Exec.CapTPConcrete.handoffNonAmplifyingC`),
//! routed through `dregg_captp::verified_gate`; the twin-deletion sweep (`e3f0e7b92`) deleted the
//! hand-written Rust rights lattice from that decision. With no gate registered, `validate_handoff`
//! refuses EVERY handoff — the amplifying ones this suite mounts and the attenuating ones it does
//! not.
//!
//! That is exactly the shape of a passing test that proves nothing. `captp_attacks.rs`'s
//! `assert_eq!(res.err(), Some(HandoffError::Amplification))` was green, and printed
//! `[ATTACK 2] permission amplification: Defended`, in a process where the amplification rule had
//! never executed — the refusal it observed was "this validator has no checker installed", which is
//! returned for honest certificates too. Deleting the non-amplification check outright would not
//! have reddened it. A defence you cannot turn off is a defence you have not tested.
//!
//! [`install_verified_captp_gate`] installs `dregg-exec-lean`'s Lean-backed implementation over the
//! linked archive — the same object `node/src/lib.rs::install_verified_distributed_gates` installs
//! in production, not a permissive stand-in — so each `Amplification` below is a verdict the
//! verified rule returned on that specific certificate. `validate_handoff` now names the other case
//! separately (`HandoffError::VerifiedGateUnavailable`), so a future regression in this setup
//! reddens these suites instead of silently re-vacating them.

/// Install the verified-Lean CapTP gate for THIS test process, as a native node does at startup.
/// Idempotent; call it at the top of any adversarial test that drives `validate_handoff`.
///
/// PANICS (rather than skipping) when the linked archive lacks the distributed exports, unless
/// `DREGG_TEST_ALLOW_MISSING_LEAN=1` is set out loud — an attack suite reporting `Defended` without
/// the defence linked is the failure mode this whole module exists to close.
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
