//! §7 — ChaCha20-Poly1305 AEAD. REAL (chacha20poly1305 0.10, no_std).
//!
//! The committed-note ECIES box (`cell/src/note_encryption.rs`) seals a note's
//! opening `(value, asset_type, blinding)` under a per-note key with
//! `ChaCha20Poly1305::new(key).encrypt(nonce, pt)` and opens it with `.decrypt`,
//! the Poly1305 tag authenticating the ciphertext (any tamper fails closed). The
//! Lean §8 `SealKernel` (`Dregg2/Crypto/PortalFloor.lean`, primitive #7: X25519 +
//! AEAD authenticity) names that `aeadOpen` oracle. THIS module wires the same
//! crate's seal/open so the executor PD can open an encrypted note on-device: an
//! authentic ciphertext yields its plaintext, a tampered one (or wrong key/nonce)
//! is rejected by the tag.
//!
//! `no_std`: chacha20poly1305 0.10 with `default-features = false, features =
//! ["alloc"]` is a pure-Rust no_std build (RustCrypto). No `std`, no `rand` (the
//! nonce is supplied by the caller, exactly as the ECIES box derives it).

use aead::{Aead, KeyInit};
use chacha20poly1305::{ChaCha20Poly1305, Key, Nonce};

/// AEAD seal: encrypt `pt` under `key` (32 bytes) with `nonce` (12 bytes),
/// producing `ciphertext || tag` (Poly1305 tag appended, +16 bytes). Writes the
/// result to `out` (which must hold at least `pt_len + 16` bytes) and returns the
/// number of bytes written, or `-1` on a buffer-too-small / arity error.
///
/// Mirrors `note_encryption::encrypt`'s `ChaCha20Poly1305::new(key).encrypt(nonce, pt)`.
///
/// # Safety
/// `key` → 32 readable bytes; `nonce` → 12 readable bytes; `pt` → `pt_len`
/// readable bytes (or null iff `pt_len==0`); `out` → `out_cap` writable bytes.
pub unsafe fn seal(
    key: *const u8,
    nonce: *const u8,
    pt: *const u8,
    pt_len: usize,
    out: *mut u8,
    out_cap: usize,
) -> isize {
    if key.is_null() || nonce.is_null() || out.is_null() {
        return -1;
    }
    let key_bytes = core::slice::from_raw_parts(key, 32);
    let nonce_bytes = core::slice::from_raw_parts(nonce, 12);
    let plaintext: &[u8] = if pt.is_null() || pt_len == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(pt, pt_len)
    };

    let cipher = ChaCha20Poly1305::new(Key::from_slice(key_bytes));
    let n = Nonce::from_slice(nonce_bytes);
    let ct = match cipher.encrypt(n, plaintext) {
        Ok(ct) => ct,
        Err(_) => return -1,
    };
    if ct.len() > out_cap {
        return -1;
    }
    core::ptr::copy_nonoverlapping(ct.as_ptr(), out, ct.len());
    ct.len() as isize
}

/// AEAD open: decrypt-and-authenticate `ct` (`ciphertext || tag`) under `key` (32
/// bytes) with `nonce` (12 bytes). On success writes the recovered plaintext to
/// `out` (which must hold at least `ct_len - 16` bytes) and returns its length; on
/// a failed tag (wrong key / tampered ciphertext / wrong nonce), a too-short
/// ciphertext, or a buffer-too-small, returns `-1` — FAIL-CLOSED, never a forged
/// authentication.
///
/// Mirrors `note_encryption::decrypt`'s `ChaCha20Poly1305::new(key).decrypt(nonce, ct)`.
///
/// # Safety
/// `key` → 32 readable bytes; `nonce` → 12 readable bytes; `ct` → `ct_len`
/// readable bytes (or null iff `ct_len==0`); `out` → `out_cap` writable bytes.
pub unsafe fn open(
    key: *const u8,
    nonce: *const u8,
    ct: *const u8,
    ct_len: usize,
    out: *mut u8,
    out_cap: usize,
) -> isize {
    if key.is_null() || nonce.is_null() || out.is_null() {
        return -1;
    }
    // A valid box is at least the 16-byte Poly1305 tag.
    if ct.is_null() || ct_len < 16 {
        return -1;
    }
    let key_bytes = core::slice::from_raw_parts(key, 32);
    let nonce_bytes = core::slice::from_raw_parts(nonce, 12);
    let ciphertext = core::slice::from_raw_parts(ct, ct_len);

    let cipher = ChaCha20Poly1305::new(Key::from_slice(key_bytes));
    let n = Nonce::from_slice(nonce_bytes);
    let pt = match cipher.decrypt(n, ciphertext) {
        Ok(pt) => pt,
        Err(_) => return -1, // tag mismatch — reject, never a spurious authenticate
    };
    if pt.len() > out_cap {
        return -1;
    }
    core::ptr::copy_nonoverlapping(pt.as_ptr(), out, pt.len());
    pt.len() as isize
}

/// AEAD authenticate-only: returns `1` iff `ct` opens under `(key, nonce)` (the
/// `aeadOpen` oracle's boolean shape — verify a sealed ciphertext without needing
/// the plaintext out), `0` otherwise. FAIL-CLOSED.
///
/// # Safety
/// As `open`, minus the output buffer.
pub unsafe fn authenticate(key: *const u8, nonce: *const u8, ct: *const u8, ct_len: usize) -> u8 {
    if key.is_null() || nonce.is_null() || ct.is_null() || ct_len < 16 {
        return 0;
    }
    let key_bytes = core::slice::from_raw_parts(key, 32);
    let nonce_bytes = core::slice::from_raw_parts(nonce, 12);
    let ciphertext = core::slice::from_raw_parts(ct, ct_len);
    let cipher = ChaCha20Poly1305::new(Key::from_slice(key_bytes));
    let n = Nonce::from_slice(nonce_bytes);
    match cipher.decrypt(n, ciphertext) {
        Ok(_) => 1,
        Err(_) => 0,
    }
}
