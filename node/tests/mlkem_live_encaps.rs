//! mlkem_live_encaps.rs — the RUNNING-BINARY gate that the node's deployed ML-KEM-768 ENCAPSULATION runs
//! through the VERIFIED Lean core (BRICK K5's `Dregg2.Crypto.MlKemEncaps.mlkemEncaps`), not the `ml-kem`
//! crate — and that the full Lean-routed handshake (Lean encaps → Lean decaps) agrees.
//!
//! ## What this proves ("the ml-kem crate leaves the LIVE KEM-encaps TCB")
//!
//! The hybrid session KEM initiator (`dregg_pq::hybrid_kem::initiate`) produces the ML-KEM-768 ciphertext +
//! shared secret. It routes through an install-time function pointer: with the REAL encaps core installed it
//! produces `(ct, K)` from the extracted, full-byte `MlKemEncaps.mlkemEncaps` running as leanc-native code and
//! NEVER calls the `ml-kem` crate's `.encapsulate` (`dregg-pq/src/hybrid_kem.rs`: the installed branch generates
//! a fresh 32-byte `m`, builds the `hex(ek) hex(m)` wire, calls the core, decodes `hex(ct) hex(K)`; the crate
//! `.encapsulate` sits only in the `else`). The X25519 + transcript + HKDF combiner is unchanged.
//!
//! The node installs that core at startup via `dregg_node::install_mlkem_verified_encaps_core()` (wired in
//! `node/src/lib.rs` right after the ML-KEM decaps install). This test drives that EXACT production install
//! function — not a copy — then:
//!
//!   1. asserts `dregg_pq::mlkem_encaps_real_core_installed()` is `true` after the install;
//!   2. mints a GENUINE ML-KEM-768 keypair with the `ml-kem` crate, feeds the verified Lean encaps shadow the
//!      SAME `hex(ek) hex(m)` wire the node builds, and asserts the crate — decapsulating the Lean-produced
//!      ciphertext — recovers the Lean-produced shared secret (`decapsulate(dk, ct_lean) == K_lean`): the Lean
//!      encaps produced a genuine ct/K pair (byte-exactness vs the crate's deterministic encaps is the
//!      build-time proof `encaps_matches_crate`);
//!   3. drives the DEPLOYED hybrid path end-to-end with BOTH cores installed (`responder_offer` → `initiate`
//!      Lean-encaps → `finish` Lean-decaps): `initiator_key == responder_key`, and a ciphertext tampered in
//!      flight makes the two DIVERGE.
//!
//! ## If the linked archive lacks the export
//!
//! `install_mlkem_verified_encaps_core()` gates on `mlkem_encaps_real_core_available()`: a build whose Lean
//! archive does not export `dregg_mlkem_encaps_real` returns `ExportAbsent` and the node keeps the `ml-kem`-
//! crate fallback. In that build the routing cannot be demonstrated; the test FAILS LOUDLY with the exact
//! blocker rather than passing vacuously.

use dregg_node::{
    MlKemDecapsCoreInstall, MlKemEncapsCoreInstall, MlKemKeygenCoreInstall,
    install_mlkem_verified_decaps_core, install_mlkem_verified_encaps_core,
    install_mlkem_verified_keygen_core,
};
use ml_kem::kem::Decapsulate as _;
use ml_kem::{Ciphertext, EncodedSizeUser as _, KemCore, MlKem768};
use rand_core::OsRng;

/// Rebuild the exact byte wire the node feeds the Lean encaps core: `"hex(ek) hex(m)"` (two space-separated
/// lowercase-hex fields, order ek‖m — matching `dregg-pq/src/hybrid_kem.rs::real_encaps_wire`).
fn real_encaps_wire(ek: &[u8], m: &[u8]) -> String {
    format!(
        "{} {}",
        dregg_types::hex_encode(ek),
        dregg_types::hex_encode(m)
    )
}

/// Decode a lowercase/uppercase-hex string to bytes; `None` on odd length or a non-hex char.
fn hex_decode(s: &str) -> Option<Vec<u8>> {
    let b = s.as_bytes();
    if b.is_empty() || b.len() % 2 != 0 {
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

/// The Lean encaps core's `(ct, K)` on a wire; `None` if the archive lacks the export (fault) or the reply is
/// the malformed sentinel `"ERR"`. This is the object `initiate` routes through when a real core is installed.
fn lean_shadow_encaps(wire: &str) -> Option<(Vec<u8>, Vec<u8>)> {
    let reply = dregg_lean_ffi::shadow_mlkem_encaps_real(wire).ok()?;
    let mut fields = reply.split(' ');
    let ct = hex_decode(fields.next()?)?;
    let k = hex_decode(fields.next()?)?;
    if fields.next().is_some() {
        return None;
    }
    Some((ct, k))
}

#[test]
fn deployed_ml_kem_encaps_routes_through_lean_core() {
    assert!(
        matches!(
            install_mlkem_verified_keygen_core(),
            MlKemKeygenCoreInstall::Installed | MlKemKeygenCoreInstall::AlreadyInstalled
        ),
        "the deployed hybrid path requires the verified ML-KEM keygen authority"
    );
    // ── DRIVE THE NODE'S STARTUP INSTALL (the exact production function) ────────────────────────
    let outcome = install_mlkem_verified_encaps_core();
    match outcome {
        MlKemEncapsCoreInstall::Installed | MlKemEncapsCoreInstall::AlreadyInstalled => {
            eprintln!(
                "encaps install outcome: {outcome:?} — verified Lean encaps core is the authority"
            );
        }
        MlKemEncapsCoreInstall::ExportAbsent => {
            panic!(
                "BLOCKER: the Lean archive linked into this test binary does NOT export \
                 `dregg_mlkem_encaps_real` (`mlkem_encaps_real_core_available()` is false), so the node's \
                 ML-KEM encaps still falls through to the `ml-kem` crate. The routing cannot be demonstrated \
                 on this build. Rebuild dregg-lean-ffi against a HEAD-matching archive that lake-builds \
                 `Dregg2.Crypto.MlKemEncaps` (build.rs lists it as a splice target), then re-run. A green on \
                 this test REQUIRES the crate to have left the KEM-encaps TCB."
            );
        }
    }

    // (1) The real encaps core is installed → `initiate` is Lean-backed, not crate-backed.
    assert!(
        dregg_pq::mlkem_encaps_real_core_installed(),
        "after install, the Lean-verified REAL encaps core must be installed"
    );

    // (2) A GENUINE ML-KEM-768 keypair, minted by the `ml-kem` crate; feed the Lean encaps the same wire the
    //     node builds, then confirm the crate decapsulates the Lean-produced ct back to the Lean-produced K.
    let (dk, ek) = MlKem768::generate(&mut OsRng);
    let ek_bytes = ek.as_bytes();
    assert_eq!(
        ek_bytes.as_slice().len(),
        1184,
        "ML-KEM-768 ek is 1184 bytes"
    );
    let m = [0x5au8; 32]; // a fixed 32-byte message (the initiator supplies its own m)
    let wire = real_encaps_wire(ek_bytes.as_slice(), &m);
    let (ct_lean, k_lean) = lean_shadow_encaps(&wire)
        .expect("the installed core must answer (archive exports the real encaps)");
    assert_eq!(ct_lean.len(), 1088, "Lean encaps ciphertext is 1088 bytes");
    assert_eq!(k_lean.len(), 32, "Lean encaps shared secret is 32 bytes");

    let ct_parsed = Ciphertext::<MlKem768>::try_from(ct_lean.as_slice())
        .expect("Lean-produced ciphertext parses at ML-KEM-768 length");
    let ss_crate = dk.decapsulate(&ct_parsed).expect("decapsulate the Lean ct");
    assert_eq!(
        ss_crate.as_slice(),
        k_lean.as_slice(),
        "the crate decapsulates the Lean-produced ciphertext back to the Lean-produced shared secret — the \
         Lean encaps produced a genuine ML-KEM-768 ct/K pair"
    );

    // (3) THE DEPLOYED HYBRID PATH end-to-end, BOTH directions Lean-routed. Install the decaps core too so
    //     `finish` is also Lean-backed, then run the full public API. `initiate`'s Lean encaps and `finish`'s
    //     Lean decaps must agree on the session key; a ct tampered in flight makes them DIVERGE.
    match install_mlkem_verified_decaps_core() {
        MlKemDecapsCoreInstall::Installed | MlKemDecapsCoreInstall::AlreadyInstalled => {}
        MlKemDecapsCoreInstall::ExportAbsent => panic!(
            "BLOCKER: the linked archive lacks `dregg_mlkem_decaps_real`; the full Lean-routed handshake \
             (Lean encaps → Lean decaps) cannot be demonstrated. Rebuild against a HEAD-matching archive."
        ),
    }
    assert!(dregg_pq::mlkem_decaps_real_core_installed());

    let (offer, responder) = dregg_pq::hybrid_kem::responder_offer();
    let (msg, initiator_key) =
        dregg_pq::hybrid_kem::initiate(&offer).expect("initiate (Lean-routed encaps)");
    let responder_key = responder.finish(&msg).expect("finish (Lean-routed decaps)");
    assert_eq!(
        initiator_key, responder_key,
        "both sides agree on the hybrid session key — the Lean-routed encaps and decaps agree end-to-end"
    );

    let (offer2, responder2) = dregg_pq::hybrid_kem::responder_offer();
    let (mut msg2, initiator_key2) =
        dregg_pq::hybrid_kem::initiate(&offer2).expect("initiate (Lean-routed encaps)");
    msg2.mlkem_ct[500] ^= 0xff;
    let responder_key2 = responder2
        .finish(&msg2)
        .expect("finish still succeeds on a well-formed ct");
    assert_ne!(
        initiator_key2, responder_key2,
        "a ciphertext tampered in flight makes the Lean-routed handshake diverge — key agreement breaks"
    );

    eprintln!(
        "PROVED: the node's deployed ML-KEM encaps routes through the verified Lean core; the crate \
         decapsulates the Lean-produced ciphertext back to the Lean-produced secret, and the full Lean-routed \
         hybrid handshake (Lean encaps → Lean decaps) agrees — the ml-kem crate has left the node's \
         KEM-encaps TCB on this build."
    );
}
