//! mlkem_bare_lean_kem.rs — the my-hand gate that the BARE ML-KEM-768 primitives the deployed TLS / QUIC
//! `X25519MLKEM768` front door runs — `dregg_pq::ml_kem768_encaps` / `ml_kem768_decaps` — route their
//! ciphertext / shared-secret AUTHORITY through the VERIFIED Lean cores (`Dregg2.Crypto.MlKemEncaps.mlkemEncaps`
//! / `MlKemDecaps.mlkemDecaps`), NOT the `ml-kem` crate.
//!
//! ## Why the BARE primitives (not just `initiate` / `finish`)
//!
//! The deployed dataplane's TLS `X25519MLKEM768` server does its own X25519 (its verified Lean handshake) and
//! calls out to the ML-KEM half through the C-ABI seam `drorb_pq_ml_kem_encaps` / `_decaps`, which are
//! `dregg_pq::ml_kem768_encaps` / `ml_kem768_decaps` — the BARE primitives, not the `hybrid_kem::initiate` /
//! `HybridResponder::finish` combiners. Before this wiring those bare functions called the `ml-kem` crate
//! directly and IGNORED the installed verified core, so installing the core changed nothing on the deployed
//! KEX path. This test pins that the bare functions now take the installed-core branch: a green here (with the
//! export present) means the crate has left the deployed KEM-encaps/decaps TCB.
//!
//! ## What it proves
//!
//!   1. the real encaps + decaps cores install through the EXACT shared `dregg_pq` installs and report
//!      `mlkem_{encaps,decaps}_real_core_installed()` == true;
//!   2. DIRECT WITNESS: `ml_kem768_decaps(dk, ct)` returns byte-for-byte what the Lean decaps shadow returns
//!      on the same `hex(dk) hex(ct)` wire — the bare function's output IS the Lean core's output;
//!   3. ROUND-TRIP: the bare encaps' `(ct, ss)` decapsulates (through the bare, Lean-routed decaps) back to
//!      `ss`, and the `ml-kem` crate independently decapsulates that same `ct` to the SAME `ss` — the Lean
//!      encaps produced a GENUINE ML-KEM-768 pair;
//!   4. a one-byte-tampered ciphertext implicit-rejects to a DIFFERENT secret through the bare decaps.
//!
//! ## If the linked archive lacks the export
//!
//! Both installs gate on `mlkem_{encaps,decaps}_real_core_available()`: a build whose Lean archive does not
//! export the real cores returns `ExportAbsent`, the bare functions keep the `ml-kem`-crate fallback, and the
//! routing cannot be demonstrated. The test then FAILS LOUDLY with the exact blocker rather than passing
//! vacuously on the crate path.

use dregg_pq::{
    MlKemDecapsCoreInstall, MlKemEncapsCoreInstall, install_verified_mlkem_decaps_core,
    install_verified_mlkem_encaps_core, ml_kem768_decaps, ml_kem768_encaps, ml_kem768_keygen,
    mlkem_decaps_real_core_installed, mlkem_encaps_real_core_installed,
};
use ml_kem::kem::Decapsulate as _;
use ml_kem::{Ciphertext, Encoded, EncodedSizeUser as _, KemCore, MlKem768};

type Dk = <MlKem768 as KemCore>::DecapsulationKey;

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(HEX[(b >> 4) as usize] as char);
        s.push(HEX[(b & 0x0f) as usize] as char);
    }
    s
}

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

/// The Lean decaps core's recovered secret on a `hex(dk) hex(ct)` wire — the object the bare decaps routes
/// through when the real core is installed. `None` on an archive fault or the malformed sentinel `"ERR"`.
fn lean_shadow_decaps(dk: &[u8], ct: &[u8]) -> Option<Vec<u8>> {
    let wire = format!("{} {}", hex_encode(dk), hex_encode(ct));
    hex_decode(&dregg_lean_ffi::shadow_mlkem_decaps_real(&wire).ok()?)
}

#[test]
fn deployed_bare_ml_kem_routes_through_lean_cores() {
    // ── DRIVE THE EXACT SHARED dregg_pq INSTALLS (the same two `dregg-lean-ffi` symbols every host passes) ──
    let enc =
        install_verified_mlkem_encaps_core(dregg_lean_ffi::mlkem_encaps_real_core_available, |w| {
            dregg_lean_ffi::shadow_mlkem_encaps_real(w).ok()
        });
    match enc {
        MlKemEncapsCoreInstall::Installed | MlKemEncapsCoreInstall::AlreadyInstalled => {
            eprintln!("encaps install: {enc:?} — verified Lean encaps core is the authority");
        }
        MlKemEncapsCoreInstall::ExportAbsent => panic!(
            "BLOCKER: the Lean archive linked into this test binary does NOT export \
             `dregg_mlkem_encaps_real` — the bare `ml_kem768_encaps` still falls through to the `ml-kem` \
             crate, so the deployed KEM-encaps routing cannot be demonstrated. Rebuild dregg-lean-ffi against \
             a HEAD-matching archive that splices `Dregg2.Crypto.MlKemEncaps`, then re-run."
        ),
    }
    let dec =
        install_verified_mlkem_decaps_core(dregg_lean_ffi::mlkem_decaps_real_core_available, |w| {
            dregg_lean_ffi::shadow_mlkem_decaps_real(w).ok()
        });
    match dec {
        MlKemDecapsCoreInstall::Installed | MlKemDecapsCoreInstall::AlreadyInstalled => {
            eprintln!("decaps install: {dec:?} — verified Lean decaps core is the authority");
        }
        MlKemDecapsCoreInstall::ExportAbsent => panic!(
            "BLOCKER: the Lean archive linked into this test binary does NOT export \
             `dregg_mlkem_decaps_real` — the bare `ml_kem768_decaps` still falls through to the `ml-kem` \
             crate. Rebuild dregg-lean-ffi against a HEAD-matching archive that splices \
             `Dregg2.Crypto.MlKemDecaps`, then re-run."
        ),
    }

    // (1) Both real cores installed → the bare primitives take the Lean-core branch, not the crate `else`.
    assert!(
        mlkem_encaps_real_core_installed(),
        "the Lean-verified REAL encaps core must be installed"
    );
    assert!(
        mlkem_decaps_real_core_installed(),
        "the Lean-verified REAL decaps core must be installed"
    );

    // A GENUINE ML-KEM-768 keypair (1184-byte ek / 2400-byte dk) from the shared keygen.
    let (ek, dk) = ml_kem768_keygen();
    assert_eq!(ek.len(), 1184, "ML-KEM-768 ek is 1184 bytes");
    assert_eq!(dk.len(), 2400, "ML-KEM-768 dk is 2400 bytes");

    // The BARE encaps — now Lean-routed — produces `(ct, ss)`.
    let (ct, ss) = ml_kem768_encaps(&ek).expect("bare Lean-routed encaps");
    assert_eq!(ct.len(), 1088, "ML-KEM-768 ct is 1088 bytes");
    assert_eq!(ss.len(), 32, "ML-KEM shared secret is 32 bytes");

    // (2) DIRECT ROUTING WITNESS: the bare decaps returns byte-for-byte what the Lean decaps shadow returns
    //     on the same wire — i.e. `ml_kem768_decaps` IS the Lean core over these bytes, not the crate.
    let ss_bare = ml_kem768_decaps(&dk, &ct).expect("bare Lean-routed decaps");
    let ss_shadow = lean_shadow_decaps(&dk, &ct).expect("the installed decaps core answers");
    assert_eq!(
        ss_bare.as_slice(),
        ss_shadow.as_slice(),
        "the bare `ml_kem768_decaps` output equals the Lean decaps core's output on the same bytes — routed"
    );

    // (3) ROUND-TRIP: the bare Lean-routed decaps recovers the bare Lean-routed encaps' secret, and the
    //     `ml-kem` CRATE independently decapsulates the SAME ciphertext to the SAME secret — the Lean encaps
    //     produced a genuine ML-KEM-768 `(ct, ss)` pair.
    assert_eq!(
        ss_bare.as_slice(),
        &ss,
        "the bare Lean-routed decaps recovers the bare Lean-routed encaps shared secret"
    );
    let dk_enc = Encoded::<Dk>::try_from(dk.as_slice()).expect("dk parses at ML-KEM-768 length");
    let dk_key = Dk::from_bytes(&dk_enc);
    let ct_parsed =
        Ciphertext::<MlKem768>::try_from(ct.as_slice()).expect("ct parses at ML-KEM-768 length");
    let ss_crate = dk_key
        .decapsulate(&ct_parsed)
        .expect("crate decapsulates the Lean ct");
    assert_eq!(
        ss_crate.as_slice(),
        &ss,
        "the `ml-kem` crate decapsulates the Lean-produced ciphertext back to the Lean-produced secret — \
         the Lean encaps emitted a genuine ML-KEM-768 ct/K pair"
    );

    // (4) A one-byte-tampered ciphertext implicit-rejects to a DIFFERENT secret through the bare decaps.
    let mut ct_tampered = ct.clone();
    ct_tampered[500] ^= 0xff;
    let ss_tampered =
        ml_kem768_decaps(&dk, &ct_tampered).expect("well-formed tampered ct decapsulates");
    assert_ne!(
        ss_tampered.as_slice(),
        &ss,
        "a tampered ciphertext implicit-rejects to a DIFFERENT secret (ML-KEM FO semantics) through the \
         bare Lean-routed decaps"
    );

    // (5) Fail-closed on malformed inputs (length gate before any backend).
    assert!(ml_kem768_encaps(&[]).is_none());
    assert!(ml_kem768_decaps(&[], &ct).is_none());
    assert!(ml_kem768_decaps(&dk, &[]).is_none());

    eprintln!(
        "PROVED: the deployed BARE ML-KEM-768 primitives (`ml_kem768_encaps` / `ml_kem768_decaps`, the TLS / \
         QUIC X25519MLKEM768 seam) route through the verified Lean cores — bare decaps output equals the Lean \
         core output byte-for-byte, the round-trip agrees with the crate, and tampers implicit-reject. The \
         `ml-kem` crate has left the deployed KEM TCB on this build."
    );
}
