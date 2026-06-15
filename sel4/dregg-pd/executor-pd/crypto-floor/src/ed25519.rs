//! §1 — ed25519 strict signature verification. REAL (ed25519-dalek 2, no_std).
//!
//! The executor PD's core turn-authorization path (`turn/src/executor/authorize.rs`)
//! and the net-client turn gate (`sel4/dregg-pd/net-client/src/turn_gate.rs`)
//! both authenticate a turn by `VerifyingKey::from_bytes(pk)` +
//! `verify_strict(msg, sig)` — the cofactorless, malleability-resistant Ed25519
//! check (RFC 8032 §5.1.7 with the extra small-order/canonical-`R` guards). The
//! Lean §8 `SignatureKernel` (`Dregg2/Crypto/PortalFloor.lean`, primitive #1:
//! EUF-CMA) names exactly this oracle. THIS module wires the same crate + the same
//! `verify_strict` shape into the executor PD's crypto floor, so a turn that needs
//! a signature check is decided by a real Ed25519 verify on-device — accept iff the
//! signature is valid under the public key over the message, reject otherwise
//! (NEVER a spurious accept).
//!
//! `no_std`: ed25519-dalek 2 with `default-features = false, features =
//! ["alloc", "hazmat"]` is a pure-Rust no_std build (its curve25519-dalek backend
//! is the portable serial backend on this cross target). No `rand`, no `std`.

use ed25519_dalek::{Signature, VerifyingKey};

/// Strict Ed25519 verification over raw bytes.
///
/// - `pk`: the 32-byte compressed Edwards public key.
/// - `msg` / `msg_len`: the signed message bytes.
/// - `sig`: the 64-byte signature `(R, s)`.
///
/// Returns `1` iff `verify_strict` accepts; `0` on a bad public key (non-canonical
/// / small-order), a malformed signature, OR a verification failure — FAIL-CLOSED,
/// the exact contract of the executor's `verify_strict(&message, &sig)` call.
///
/// # Safety
/// `pk` must point to 32 readable bytes; `sig` to 64 readable bytes; `msg` to
/// `msg_len` readable bytes (or be null iff `msg_len == 0`).
pub unsafe fn verify(pk: *const u8, msg: *const u8, msg_len: usize, sig: *const u8) -> u8 {
    if pk.is_null() || sig.is_null() {
        return 0;
    }
    let pk_bytes = {
        let s = core::slice::from_raw_parts(pk, 32);
        let mut b = [0u8; 32];
        b.copy_from_slice(s);
        b
    };
    let sig_bytes = {
        let s = core::slice::from_raw_parts(sig, 64);
        let mut b = [0u8; 64];
        b.copy_from_slice(s);
        b
    };
    let message: &[u8] = if msg.is_null() || msg_len == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(msg, msg_len)
    };

    // VerifyingKey::from_bytes rejects non-canonical encodings; verify_strict adds
    // the cofactorless + small-order R guards. A failure at any step → reject.
    let vk = match VerifyingKey::from_bytes(&pk_bytes) {
        Ok(vk) => vk,
        Err(_) => return 0,
    };
    let sig = Signature::from_bytes(&sig_bytes);
    match vk.verify_strict(message, &sig) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}
