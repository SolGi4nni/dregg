//! mlkem_sdk_kem_verified.rs — the RUNNING-BINARY, GATE-ARMED gate that an SDK-HOSTED process's ML-KEM-768
//! encaps + decaps (the X-Wing / `X25519MLKEM768` session KEM and the hybrid combiners it hosts) run through
//! the VERIFIED Lean cores (`Dregg2.Crypto.MlKemEncaps.mlkemEncaps` / `MlKemDecaps.mlkemDecaps`), NOT the
//! `ml-kem` crate — closing the gap where the SDK installed verify + sign but NOT the KEM cores, so every
//! SDK-hosted KEM op hit dregg-pq's audit gate (Gate 2) and ABORTED.
//!
//! ## Why this is a real observation, not a green tautology
//!
//! `dregg-pq`'s `guard_unaudited_fallback` `test_override` is `#[cfg(test)]` — it exists ONLY inside
//! `dregg-pq`'s own unit-test binary. In THIS binary `dregg-pq` is an ordinary dependency rlib, so the
//! override does NOT exist and the gate is FULLY ARMED. With no `DREGG_ALLOW_UNAUDITED_PQ` opt-out set (the
//! harness asserts it is unset), if any KEM op below fell through to the `ml-kem`-crate fallback it would
//! `std::process::abort()` the whole test binary. Reaching the assertions past a real encaps AND a real
//! decaps therefore PROVES the verified cores — not the crate, not an abort — answered them.
//!
//! ## What it drives / observes
//!
//!   1. constructs an `AgentRuntime` — the EXACT SDK-agent-startup path — firing the production installs
//!      (`sdk/src/runtime.rs::ensure_verified_mlkem_{encaps,decaps}_core_installed`);
//!   2. asserts the production install fns report `Installed`/`AlreadyInstalled` (ExportAbsent ⇒ loud
//!      blocker, not a vacuous pass) and `dregg_pq::mlkem_{encaps,decaps}_real_core_installed()` == true;
//!   3. GATE-ARMED KEM op with NO opt-out: keygen → encaps(ek) → decaps(dk, ct). A fallback would abort;
//!      that these return proves the verified path ran;
//!   4. ROUND-TRIP: the encaps' `(ct, ss)` decapsulates back to the SAME `ss` — a genuine ML-KEM-768 pair;
//!   5. DISPATCH WITNESS: `ml_kem768_decaps(dk, ct)` equals BYTE-FOR-BYTE what the Lean decaps shadow returns
//!      on the same `hex(dk) hex(ct)` wire — the deployed function's output IS the Lean core's output;
//!   6. a one-byte-tampered ciphertext implicit-rejects to a DIFFERENT secret through the verified decaps.
//!
//! ## If the linked archive lacks the export
//!
//! The installs gate on `mlkem_{encaps,decaps}_real_core_available()`: a build whose archive does not export
//! the real cores returns `ExportAbsent`, and step 2 FAILS LOUDLY with the exact blocker rather than passing
//! on the crate path. A green here (export present) means the `ml-kem` crate has left the SDK-hosted process's
//! KEM-encaps/decaps TCB.

use dregg_sdk::{AgentCipherclerk, AgentRuntime, MlKemDecapsCoreInstall, MlKemEncapsCoreInstall};

/// Rebuild the exact byte wire the deployed decaps feeds the Lean core: `"hex(dk) hex(ct)"` (two
/// space-separated lowercase-hex fields — matching `dregg-pq/src/hybrid_kem.rs::real_decaps_wire`).
fn real_decaps_wire(dk: &[u8], ct: &[u8]) -> String {
    format!(
        "{} {}",
        dregg_types::hex_encode(dk),
        dregg_types::hex_encode(ct)
    )
}

/// Decode the Lean decaps shadow's 64-hex-char reply into the 32-byte shared secret. `None` on any malformed
/// reply — the same fail-closed decode the deployed path uses.
fn decode_ss_hex(reply: &str) -> Option<[u8; 32]> {
    let b = reply.as_bytes();
    if b.len() != 64 {
        return None;
    }
    fn nib(c: u8) -> Option<u8> {
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            b'A'..=b'F' => Some(c - b'A' + 10),
            _ => None,
        }
    }
    let mut out = [0u8; 32];
    for (i, o) in out.iter_mut().enumerate() {
        *o = (nib(b[2 * i])? << 4) | nib(b[2 * i + 1])?;
    }
    Some(out)
}

/// The Lean decaps core's raw shared secret on a wire; `None` if the archive lacks the export (fault). This
/// is the object `ml_kem768_decaps` routes through when the verified core is installed.
fn lean_decaps_shadow(dk: &[u8], ct: &[u8]) -> Option<[u8; 32]> {
    match dregg_lean_ffi::shadow_mlkem_decaps_real(&real_decaps_wire(dk, ct)) {
        Ok(reply) => decode_ss_hex(&reply),
        Err(_) => None,
    }
}

#[test]
fn sdk_hosted_ml_kem_routes_through_lean_cores_gate_armed() {
    // ── PRECONDITION: the audit gate is ARMED (no opt-out) ───────────────────────────────────────
    // If this were set, a fallback would be permitted and the observation would be worthless.
    assert!(
        std::env::var("DREGG_ALLOW_UNAUDITED_PQ").is_err(),
        "this gate must run with DREGG_ALLOW_UNAUDITED_PQ UNSET — otherwise a crate-fallback KEM op would \
         be permitted and 'it ran verified' would be unproven"
    );

    // ── DRIVE THE SDK AGENT STARTUP (the exact production construction path) ──────────────────────
    // Constructing an AgentRuntime fires `ensure_verified_mlkem_{encaps,decaps}_core_installed()`.
    let _runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), "sdk-kem-gate");

    // Confirm the exact production install fns report the cores present (idempotent here).
    match dregg_sdk::install_verified_mlkem_encaps_core() {
        MlKemEncapsCoreInstall::Installed | MlKemEncapsCoreInstall::AlreadyInstalled => {}
        MlKemEncapsCoreInstall::ExportAbsent => panic!(
            "BLOCKER: the Lean archive linked into this test binary does NOT export the real ML-KEM encaps \
             core (`mlkem_encaps_real_core_available()` is false), so the SDK-hosted process's KEM encaps \
             cannot route through Lean. Rebuild against a HEAD-matching archive: this gate must not pass \
             while the `ml-kem` crate is still the encaps authority."
        ),
    }
    match dregg_sdk::install_verified_mlkem_decaps_core() {
        MlKemDecapsCoreInstall::Installed | MlKemDecapsCoreInstall::AlreadyInstalled => {}
        MlKemDecapsCoreInstall::ExportAbsent => panic!(
            "BLOCKER: the Lean archive linked into this test binary does NOT export the real ML-KEM decaps \
             core (`mlkem_decaps_real_core_available()` is false), so the SDK-hosted process's KEM decaps \
             cannot route through Lean. Rebuild against a HEAD-matching archive."
        ),
    }

    assert!(
        dregg_pq::mlkem_encaps_real_core_installed(),
        "after SDK agent startup the Lean-verified REAL encaps core must be installed — \
         `dregg_pq::ml_kem768_encaps` is otherwise the `ml-kem` crate (which the armed gate aborts)"
    );
    assert!(
        dregg_pq::mlkem_decaps_real_core_installed(),
        "after SDK agent startup the Lean-verified REAL decaps core must be installed"
    );

    // ── GATE-ARMED KEM OP: every call below aborts the process if it hits the crate fallback ──────
    // keygen has no verified core (structural gap) — it WARNS and proceeds; encaps/decaps are the
    // refuse-gated ops, and reaching past them proves the verified cores answered.
    let (ek, dk) = dregg_pq::ml_kem768_keygen();
    let (ct, ss_enc) =
        dregg_pq::ml_kem768_encaps(&ek).expect("verified encaps must produce a genuine (ct, ss)");
    let ss_dec =
        dregg_pq::ml_kem768_decaps(&dk, &ct).expect("verified decaps must recover a shared secret");

    // (4) ROUND-TRIP: the verified encaps' secret is exactly what the verified decaps recovers.
    assert_eq!(
        ss_enc, ss_dec,
        "the ML-KEM-768 shared secret from the verified encaps must round-trip through the verified decaps"
    );

    // (5) DISPATCH WITNESS: the deployed bare decaps' output IS the Lean object's output on the same wire.
    assert_eq!(
        Some(ss_dec),
        lean_decaps_shadow(&dk, &ct),
        "the deployed `ml_kem768_decaps(dk, ct)` must EQUAL the Lean decaps shadow's secret on the same \
         `hex(dk) hex(ct)` wire — proving the Lean object, not the `ml-kem` crate, produced it"
    );

    // (6) one-byte-tampered ciphertext implicit-rejects to a DIFFERENT secret (FO implicit reject), still
    // through the verified decaps (a fallback here would have aborted).
    let mut tampered = ct.clone();
    tampered[0] ^= 0x01;
    let ss_tamper =
        dregg_pq::ml_kem768_decaps(&dk, &tampered).expect("implicit reject returns a valid secret");
    assert_ne!(
        ss_dec, ss_tamper,
        "a one-byte-tampered ciphertext must implicit-reject to a DIFFERENT secret"
    );
    assert_eq!(
        Some(ss_tamper),
        lean_decaps_shadow(&dk, &tampered),
        "even the implicit-reject secret must EQUAL the Lean object's on the same wire"
    );

    eprintln!(
        "SDK-hosted ML-KEM-768 routes through the Lean cores (gate ARMED, no opt-out): keygen→encaps→decaps \
         round-trips, decaps == the Lean shadow on the same wire, tamper implicit-rejects — reaching here \
         past the armed gate proves the verified cores (not the `ml-kem` crate, not an abort) answered."
    );
}
