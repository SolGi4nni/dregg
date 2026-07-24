//! Shared test support for the captp integration tests.
//!
//! `captp/src/handoff.rs::validate_handoff` now decides §6 non-amplification through the VERIFIED
//! Lean gate (`dregg_captp_validate_handoff`) and FAILS CLOSED (refuses the handoff) when no gate is
//! registered — the hand-written Rust rights lattice was deleted from the live path. The integration
//! tests below exercise OTHER properties of the handoff path (introducer/recipient signatures, target
//! binding, replay, revocation, GC) over LEGITIMATE (attenuating) handoffs, so they need the §6 gate
//! to admit non-amplifying handoffs.
//!
//! This registers a permissive TEST stand-in for the verified gate: it reports every handoff as
//! non-amplifying. It is confined to the test process (never a live path — the deployed vat installs
//! `dregg-exec-lean`'s real Lean gate) and is used ONLY by tests that do not themselves probe
//! non-amplification. The non-amplification decision itself is pinned Rust↔Lean by
//! `handoff_lattice_differential.rs` and exercised over the real archive in `dregg-exec-lean`.

use std::sync::Once;

use dregg_captp::{CaptpVerifiedGate, register_captp_verified_gate};

/// A permissive stand-in for the verified CapTP gate: reports the distributed exports as available and
/// every handoff as non-amplifying. Used only by integration tests that test properties OTHER than
/// non-amplification and need legitimate handoffs admitted at §6.
struct AssumeNonAmplifyingGate;

impl CaptpVerifiedGate for AssumeNonAmplifyingGate {
    fn distributed_exports_available(&self) -> bool {
        true
    }
    fn handoff_non_amplifying(&self, _wire: &str) -> Option<bool> {
        // Test stand-in: assume non-amplifying. (Real non-amplification is decided by the Lean gate
        // and pinned by `handoff_lattice_differential.rs`.)
        Some(true)
    }
    fn process_drop(&self, _wire: &str) -> Option<String> {
        None
    }
    fn pipeline_resolve(&self, _wire: &str) -> Option<String> {
        None
    }
}

static REGISTER: Once = Once::new();

/// Register the permissive §6 gate for this test process (idempotent). Call at the start of any test
/// that drives a LEGITIMATE handoff through `validate_handoff` and expects it to be admitted.
pub fn assume_non_amplifying_handoffs() {
    REGISTER.call_once(|| {
        register_captp_verified_gate(Box::new(AssumeNonAmplifyingGate));
    });
}
