//! mldsa_wire_silo_verify.rs — the RUNNING-BINARY gate that an SDK-HOSTED process's ML-DSA-65 verify
//! (the wire `SiloServer`'s token/revocation verify + the SDK's turn/captp receipt verifies) runs through
//! the VERIFIED Lean core (BRICK 8's `MlDsaVerifyReal.verifyCore`), NOT the `fips204` crate.
//!
//! ## What this closes (the surface node can't cover)
//!
//! `dregg_pq::ml_dsa_verify` is a PROCESS-GLOBAL: it routes through an install-time function pointer and,
//! with the REAL core installed, takes its accept/reject verdict from the extracted, full-byte
//! `MlDsaVerifyReal.verifyCore` and NEVER consults the `fips204` crate (`dregg-pq/src/mldsa.rs`: the
//! installed branch computes the wire, calls the core, and `return`s BEFORE the crate `vk.verify`). Only
//! `dregg-node` installed it — so an SDK-hosted process (the wire silo, an `AgentRuntime`) and starbridge-v2
//! were falling through to the `fips204` crate at every verify (`wire/src/server.rs` sites V2/V3).
//!
//! An `AgentRuntime` now performs the SAME shared install the node does at construction (see
//! `sdk/src/runtime.rs::ensure_verified_mldsa_verify_core_installed`, over
//! `dregg_pq::install_verified_mldsa_verify_core`). This test:
//!
//!   1. constructs an `AgentRuntime` — the EXACT SDK-agent-startup path — driving the production install;
//!   2. asserts `dregg_pq::lean_verify_core_real_installed()` is `true` afterward;
//!   3. mints a GENUINE ML-DSA-65 `(pk, msg, ctx, sig)` with the `fips204` crate and asserts
//!      `dregg_pq::ml_dsa_verify(pk, ctx, msg, sig) == true` (a real signature accepted);
//!   4. asserts the routed verdict is BYTE-FOR-BYTE the Lean core's — for accept / tamper / wrong-msg the
//!      deployed `ml_dsa_verify(..)` equals `dregg_lean_ffi::shadow_fips204_verify_real(wire) == "1"`, i.e.
//!      the SDK-hosted verify's answer IS the Lean object's answer on the same wire the silo builds;
//!   5. asserts a one-byte-tampered signature and a wrong message REJECT.
//!
//! The `SiloServer`'s PresentToken/SubmitRevocation verify and the SDK's turn/captp receipt verify are all
//! calls into this same `dregg_pq::ml_dsa_verify` global, so routing it through Lean here closes those
//! surfaces for the SDK-hosted process; the AgentRuntime construction is the startup point that arms it.
//!
//! ## If the linked archive lacks the export
//!
//! The install gates on `fips204_verify_real_core_available()`: a build whose Lean archive does not export
//! `dregg_fips204_verify_real` returns `ExportAbsent` and the process keeps the `fips204`-crate fallback. In
//! that build routing cannot be demonstrated, so this test FAILS LOUDLY with the exact blocker rather than
//! passing vacuously — a green here means the crate has actually left the SDK-hosted verify TCB on this build.

use dregg_sdk::{AgentCipherclerk, AgentRuntime, MlDsaVerifyCoreInstall};
use fips204::ml_dsa_65;
use fips204::traits::{SerDes as _, Signer as _};

/// Rebuild the exact byte wire the deployed verify feeds the Lean core: `"hex(pk) hex(msg) hex(ctx) hex(sig)"`
/// (four space-separated lowercase-hex fields; field order pk‖msg‖ctx‖sig — matching
/// `dregg-pq/src/mldsa.rs::real_verify_wire`).
fn real_verify_wire(pk: &[u8], msg: &[u8], ctx: &[u8], sig: &[u8]) -> String {
    format!(
        "{} {} {} {}",
        dregg_types::hex_encode(pk),
        dregg_types::hex_encode(msg),
        dregg_types::hex_encode(ctx),
        dregg_types::hex_encode(sig),
    )
}

/// The Lean core's raw verdict on a wire; `None` if the archive lacks the export (fault). This is the
/// object `ml_dsa_verify` routes through when a real core is installed.
fn lean_shadow_verdict(wire: &str) -> Option<bool> {
    match dregg_lean_ffi::shadow_fips204_verify_real(wire) {
        Ok(s) => Some(s == "1"),
        Err(_) => None,
    }
}

#[test]
fn sdk_hosted_ml_dsa_verify_routes_through_lean_core() {
    // ── DRIVE THE SDK AGENT STARTUP (the exact production construction path) ─────────────────────
    // Constructing an AgentRuntime fires `ensure_verified_mldsa_verify_core_installed()` — the same
    // once-per-process install every SDK-hosted process (and the wire silo it hosts) runs.
    let _runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), "wire-silo-gate");

    // Confirm the exact production install fn reports the core is present (also idempotent here).
    match dregg_sdk::install_verified_mldsa_verify_core() {
        MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled => {}
        MlDsaVerifyCoreInstall::ExportAbsent => panic!(
            "BLOCKER: the Lean archive linked into this test binary does NOT export \
             `dregg_fips204_verify_real` (`fips204_verify_real_core_available()` is false), so the \
             SDK-hosted process's ML-DSA verify cannot route through Lean. Rebuild against a HEAD-matching \
             archive: this gate must not pass while the crate is still the verify authority."
        ),
    }

    assert!(
        dregg_pq::lean_verify_core_real_installed(),
        "after SDK agent startup the Lean-verified REAL verify core must be installed — \
         `dregg_pq::ml_dsa_verify` is otherwise routed to the `fips204` crate"
    );

    // ── MINT A GENUINE ML-DSA-65 SIGNATURE (the `fips204` crate, deployed params) ────────────────
    let (pk, sk) = ml_dsa_65::try_keygen().expect("ml-dsa-65 keygen");
    let msg = b"a wire-silo PresentToken / turn-receipt payload";
    let ctx = b"dregg-wire-silo";
    let sig = sk.try_sign(msg, ctx).expect("ml-dsa-65 sign");

    let pk_bytes = pk.into_bytes();
    let sig_bytes = sig; // fips204 0.4 returns the raw signature byte array

    // (2)+(3) genuine signature ACCEPTED, and the routed verdict IS the Lean object's verdict.
    let accept_wire = real_verify_wire(&pk_bytes, msg, ctx, &sig_bytes);
    let routed_accept = dregg_pq::ml_dsa_verify(&pk_bytes, ctx, msg, &sig_bytes);
    assert!(
        routed_accept,
        "a genuine ML-DSA-65 signature must be ACCEPTED by the routed verify"
    );
    assert_eq!(
        Some(routed_accept),
        lean_shadow_verdict(&accept_wire),
        "the deployed verdict on a genuine signature must EQUAL the Lean shadow's verdict on the same \
         wire (proving the Lean object — not the crate — produced it)"
    );

    // (4)+(5) one-byte tamper REJECTED, and the verdict still equals the Lean object's.
    let mut tampered = sig_bytes;
    tampered[0] ^= 0x01;
    let tamper_wire = real_verify_wire(&pk_bytes, msg, ctx, &tampered);
    let routed_tamper = dregg_pq::ml_dsa_verify(&pk_bytes, ctx, msg, &tampered);
    assert!(
        !routed_tamper,
        "a one-byte-tampered signature must be REJECTED"
    );
    assert_eq!(
        Some(routed_tamper),
        lean_shadow_verdict(&tamper_wire),
        "the deployed verdict on a tampered signature must EQUAL the Lean shadow's verdict"
    );

    // Wrong message REJECTED, verdict equals the Lean object's.
    let wrong_msg = b"a DIFFERENT payload than the one signed";
    let wrong_wire = real_verify_wire(&pk_bytes, wrong_msg, ctx, &sig_bytes);
    let routed_wrong = dregg_pq::ml_dsa_verify(&pk_bytes, ctx, wrong_msg, &sig_bytes);
    assert!(!routed_wrong, "a wrong-message verify must be REJECTED");
    assert_eq!(
        Some(routed_wrong),
        lean_shadow_verdict(&wrong_wire),
        "the deployed verdict on a wrong message must EQUAL the Lean shadow's verdict"
    );

    eprintln!(
        "SDK-hosted ML-DSA verify routes through the Lean core: genuine accepted, tamper+wrong-msg \
         rejected, every verdict == the Lean shadow's on the same wire; the `fips204` crate is out of \
         the SDK-hosted verify TCB."
    );
}
