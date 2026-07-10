//! mlkem_live_decaps.rs — the RUNNING-BINARY gate that the node's deployed ML-KEM-768 decapsulation runs
//! through the VERIFIED Lean core (BRICK K6's `Dregg2.Crypto.MlKemDecaps.mlkemDecaps`), not the `ml-kem`
//! crate.
//!
//! ## What this proves ("the ml-kem crate leaves the LIVE KEM-decaps TCB")
//!
//! The hybrid session KEM (`dregg_pq::hybrid_kem`) recovers the ML-KEM-768 shared secret on the responder
//! side inside `HybridResponder::finish`. It routes through an install-time function pointer: with the REAL
//! core installed it recovers the secret from the extracted, full-byte `MlKemDecaps.mlkemDecaps` running as
//! leanc-native code and NEVER calls the `ml-kem` crate's `.decapsulate` (`dregg-pq/src/hybrid_kem.rs`: the
//! installed branch builds the `hex(dk) hex(ct)` wire, calls the core, decodes the reply, and the crate
//! `.decapsulate` sits only in the `else`). The X25519 + transcript + HKDF combiner around the ML-KEM secret
//! is unchanged — only the `.decapsulate` call is replaced.
//!
//! The node installs that core at startup via `dregg_node::install_mlkem_verified_decaps_core()` (wired in
//! `node/src/lib.rs` right after the ML-DSA sign install). This test drives that EXACT production install
//! function — not a copy — then:
//!
//!   1. asserts `dregg_pq::mlkem_decaps_real_core_installed()` is `true` after the install;
//!   2. generates a GENUINE ML-KEM-768 `(dk, ct, ss)` with the `ml-kem` crate and asserts the verified Lean
//!      shadow, on the SAME `hex(dk) hex(ct)` wire the node builds, recovers the crate's encapsulated shared
//!      secret BYTE-FOR-BYTE (`shadow_mlkem_decaps_real(wire)` == `hex(ss)`) — the Lean object recovers the
//!      real secret;
//!   3. asserts a one-byte-tampered ciphertext implicit-rejects to a DIFFERENT secret through the same core;
//!   4. drives the DEPLOYED hybrid path end-to-end (`responder_offer` → `initiate` → `finish`, all public
//!      API): with the core installed, `finish`'s Lean-routed decaps agrees with the crate's encaps
//!      (`initiator_key == responder_key`), and a ciphertext tampered in flight makes the two DIVERGE.
//!
//! Together (1)+(2) show the deployed decaps IS the Lean object over the real bytes; (4) shows the live hybrid
//! handshake succeeds on that object.
//!
//! ## If the linked archive lacks the export
//!
//! `install_mlkem_verified_decaps_core()` gates on `mlkem_decaps_real_core_available()`: a build whose Lean
//! archive does not export `dregg_mlkem_decaps_real` returns `ExportAbsent` and the node keeps the `ml-kem`-
//! crate fallback (a valid FIPS-203 decaps, just not Lean-authoritative). In that build the routing cannot be
//! demonstrated; the test then FAILS LOUDLY with the exact blocker rather than passing vacuously.

use dregg_node::{MlKemDecapsCoreInstall, install_mlkem_verified_decaps_core};
use ml_kem::kem::{Decapsulate as _, Encapsulate as _};
use ml_kem::{EncodedSizeUser as _, KemCore, MlKem768};
use rand_core::OsRng;

/// Rebuild the exact byte wire the node feeds the Lean decaps core: `"hex(dk) hex(ct)"` (two space-separated
/// lowercase-hex fields, order dk‖ct — matching `dregg-pq/src/hybrid_kem.rs::real_decaps_wire`).
fn real_decaps_wire(dk: &[u8], ct: &[u8]) -> String {
    format!(
        "{} {}",
        dregg_types::hex_encode(dk),
        dregg_types::hex_encode(ct),
    )
}

/// Decode a lowercase/uppercase-hex string to bytes; `None` on odd length or a non-hex char.
fn hex_decode(s: &str) -> Option<Vec<u8>> {
    let b = s.as_bytes();
    if b.len() % 2 != 0 {
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
    let mut out = Vec::with_capacity(b.len() / 2);
    for chunk in b.chunks_exact(2) {
        out.push((nib(chunk[0])? << 4) | nib(chunk[1])?);
    }
    Some(out)
}

/// The Lean core's recovered secret on a wire, as raw bytes; `None` if the archive lacks the export (fault)
/// or the reply is the malformed sentinel `"ERR"`. This is the object `finish` routes through when a real
/// core is installed.
fn lean_shadow_secret(wire: &str) -> Option<Vec<u8>> {
    match dregg_lean_ffi::shadow_mlkem_decaps_real(wire) {
        Ok(reply) => hex_decode(&reply),
        Err(_) => None,
    }
}

#[test]
fn deployed_ml_kem_decaps_routes_through_lean_core() {
    // ── DRIVE THE NODE'S STARTUP INSTALL (the exact production function) ────────────────────────
    let outcome = install_mlkem_verified_decaps_core();
    match outcome {
        MlKemDecapsCoreInstall::Installed | MlKemDecapsCoreInstall::AlreadyInstalled => {
            eprintln!("install outcome: {outcome:?} — verified Lean decaps core is the authority");
        }
        MlKemDecapsCoreInstall::ExportAbsent => {
            panic!(
                "BLOCKER: the Lean archive linked into this test binary does NOT export \
                 `dregg_mlkem_decaps_real` (`mlkem_decaps_real_core_available()` is false), so the node's \
                 ML-KEM decaps still falls through to the `ml-kem` crate. The routing cannot be demonstrated \
                 on this build. Rebuild dregg-lean-ffi against a HEAD-matching archive that lake-builds \
                 `Dregg2.Crypto.MlKemDecaps` (build.rs lists it as a splice target), then re-run. A green on \
                 this test REQUIRES the crate to have left the KEM-decaps TCB."
            );
        }
    }

    // (1) The real core is installed → `HybridResponder::finish` is Lean-backed, not crate-backed.
    assert!(
        dregg_pq::mlkem_decaps_real_core_installed(),
        "after install, the Lean-verified REAL decaps core must be installed"
    );

    // (2) A GENUINE ML-KEM-768 keypair + encapsulation, minted by the `ml-kem` crate itself.
    let (dk, ek) = MlKem768::generate(&mut OsRng);
    let (ct, ss_crate) = ek.encapsulate(&mut OsRng).expect("ml-kem-768 encapsulate");
    let dk_bytes = dk.as_bytes();
    let ct_bytes = ct.as_slice().to_vec();
    let ss_crate_bytes = ss_crate.as_slice().to_vec();
    assert_eq!(
        dk_bytes.as_slice().len(),
        2400,
        "ML-KEM-768 dk is 2400 bytes"
    );
    assert_eq!(ct_bytes.len(), 1088, "ML-KEM-768 ct is 1088 bytes");
    assert_eq!(ss_crate_bytes.len(), 32, "ML-KEM shared secret is 32 bytes");

    // The Lean core, on the SAME wire the node builds, recovers the crate's encapsulated secret BYTE-FOR-BYTE.
    let honest_wire = real_decaps_wire(dk_bytes.as_slice(), &ct_bytes);
    let ss_lean = lean_shadow_secret(&honest_wire)
        .expect("the installed core must answer (archive exports the real decaps)");
    assert_eq!(
        ss_lean, ss_crate_bytes,
        "the verified Lean decaps recovers the REAL ml-kem crate shared secret over the real bytes"
    );

    // (3) A one-byte-tampered ciphertext implicit-rejects to a DIFFERENT secret through the same core.
    let mut ct_tampered = ct_bytes.clone();
    ct_tampered[500] ^= 0xff;
    let tamper_wire = real_decaps_wire(dk_bytes.as_slice(), &ct_tampered);
    let ss_lean_tampered =
        lean_shadow_secret(&tamper_wire).expect("core answers on the tampered wire");
    assert_ne!(
        ss_lean_tampered, ss_crate_bytes,
        "a tampered ciphertext implicit-rejects to a DIFFERENT secret (ML-KEM FO semantics)"
    );

    // (4) THE DEPLOYED HYBRID PATH end-to-end (public API): `finish`'s Lean-routed decaps agrees with the
    //     crate's encaps, so both parties derive the SAME session key; a ciphertext tampered in flight
    //     makes them DIVERGE (the ML-KEM half genuinely participates through the Lean core).
    let (offer, responder) = dregg_pq::hybrid_kem::responder_offer();
    let (msg, initiator_key) = dregg_pq::hybrid_kem::initiate(&offer).expect("initiate");
    let responder_key = responder.finish(&msg).expect("finish (Lean-routed decaps)");
    assert_eq!(
        initiator_key, responder_key,
        "both sides agree on the hybrid session key — finish's Lean decaps recovered the crate's encaps secret"
    );

    let (offer2, responder2) = dregg_pq::hybrid_kem::responder_offer();
    let (mut msg2, initiator_key2) = dregg_pq::hybrid_kem::initiate(&offer2).expect("initiate");
    msg2.mlkem_ct[500] ^= 0xff;
    let responder_key2 = responder2
        .finish(&msg2)
        .expect("finish still succeeds on a well-formed ct");
    assert_ne!(
        initiator_key2, responder_key2,
        "a ciphertext tampered in flight makes the Lean-routed responder diverge — key agreement breaks"
    );

    eprintln!(
        "PROVED: the node's deployed ML-KEM decaps routes through the verified Lean core; it recovers the \
         real ml-kem crate secret byte-for-byte, implicit-rejects tampers, and the live hybrid handshake \
         agrees — the ml-kem crate has left the node's KEM-decaps TCB on this build."
    );
}
