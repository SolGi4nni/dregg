//! Audited-primitive backend for the crypto FFI seam: AES-GCM AEAD and RSA
//! PKCS#1 v1.5 signature verification.
//!
//! The crypto seam (`ffi/crypto_shim.c`, `Crypto.lean`) prefers the F*-verified
//! HACL*/EverCrypt AES-GCM. That path is Vale x86-64 assembly and reports
//! `UnsupportedAlgorithm` on targets without AES-NI+CLMUL (ARM, and any non-x86
//! host). RFC 9001 §5.2 nonetheless MANDATES AES-128-GCM for QUIC Initial
//! packets, so a server must still be able to seal/open AES-GCM to interoperate.
//!
//! This crate supplies that capability where the verified path cannot run. It is
//! a thin C-ABI wrapper over `aws-lc-rs` (the AWS-LC / BoringSSL-derived crypto
//! that rustls uses): well-audited, constant-time, and hardware-accelerated on
//! ARMv8. It is deliberately NOT part of the machine-checked TCB — it is an
//! AUDITED-primitive backend. See `CRYPTO-FFI-README.md` for the trust ledger.
//!
//! It also supplies `drorb_rsa_fallback_pkcs1_sha256_verify`: RSASSA-PKCS1-v1_5 /
//! SHA-256 signature verification (`sha256WithRSAEncryption`), the padding MOST
//! real RSA CA chains sign with — including Let's Encrypt's RSA intermediates
//! (R10/R11) and ISRG Root X1. HACL*/EverCrypt ships RSA-PSS only, so the
//! verified TLS client's X.509 path builder reaches this audited aws-lc verify
//! for a PKCS#1 v1.5 link (over each certificate's TBSCertificate) — the same
//! audited-crypto trust status as the AES-GCM fallback above, NOT part of the
//! machine-checked TCB. aws-lc's `EVP_DigestVerify` (RSA/PKCS1v1.5) — never
//! openssl. See `CRYPTO-FFI-README.md`.
//!
//! It also supplies `drorb_pbkdf2_fallback_verify` / `drorb_pbkdf2_fallback_hash`:
//! PBKDF2-HMAC-SHA256 password verification and hash generation for the
//! `basic_auth` gate. This is AWS-LC's `PKCS5_PBKDF2_HMAC` (via
//! `aws_lc_rs::pbkdf2`) — the SAME audited backend as the AES-GCM/RSA paths above,
//! NOT the pure-Rust `bcrypt`/RustCrypto `blowfish` this crate used to carry. The
//! stored format is `pbkdf2_sha256$<iterations>$<salt_hex>$<dk_hex>` (a
//! self-describing modular string): a 16-byte per-hash random salt (from AWS-LC's
//! CSPRNG), a high OWASP-current iteration count (600 000) driving the work factor,
//! and a 32-byte derived key. Verification re-derives at the stored iteration
//! count + salt and compares in CONSTANT TIME (`aws_lc_rs::pbkdf2::verify`, which
//! calls AWS-LC's `verify_slices_are_equal`). AUDITED primitive — never openssl,
//! never bcrypt. See `CRYPTO-FFI-README.md`.
//!
//! ## ABI
//!
//! All buffers are borrowed raw pointer+length pairs. The AEAD algorithm is
//! selected by key length: 16 → AES-128-GCM, 32 → AES-256-GCM. The nonce is the
//! 12-byte IETF GCM nonce. Output is `ciphertext ‖ tag` (tag = 16 bytes), the
//! same split-off layout the shim uses for the EverCrypt path.
//!
//! Return codes: `0` = success; any nonzero = failure (bad size, or on open, an
//! authentication failure — the two are not distinguished, matching the seam's
//! "wrong key/tag ⇒ none" contract). On failure the output buffer is untouched.

use aws_lc_rs::aead::{AES_128_GCM, AES_256_GCM, Aad, LessSafeKey, NONCE_LEN, Nonce, UnboundKey};
use aws_lc_rs::cipher::{AES_128, AES_256, EncryptingKey, UnboundCipherKey};
use aws_lc_rs::pbkdf2;
use aws_lc_rs::signature::{RSA_PKCS1_2048_8192_SHA256, RsaPublicKeyComponents};
use core::num::NonZeroU32;

/// PBKDF2-HMAC-SHA256 derived-key length (bytes) — one SHA-256 block.
const PBKDF2_DK_LEN: usize = 32;
/// PBKDF2 salt length (bytes) — meets the FIPS 198 / OWASP `>= 16` floor.
const PBKDF2_SALT_LEN: usize = 16;

/// AEAD tag length (bytes) for AES-GCM as this seam uses it.
const TAG_LEN: usize = 16;

/// AES block length (bytes) — the header-protection sample/mask block size.
const AES_BLOCK_LEN: usize = 16;

const RC_OK: i32 = 0;
const RC_BAD_SIZE: i32 = 1;
const RC_AUTH_FAIL: i32 = 2;
const RC_INTERNAL: i32 = 3;

/// Pick the AEAD algorithm from the key length. `None` for any unsupported size.
fn alg_for_key(key_len: usize) -> Option<&'static aws_lc_rs::aead::Algorithm> {
    match key_len {
        16 => Some(&AES_128_GCM),
        32 => Some(&AES_256_GCM),
        _ => None,
    }
}

/// Reconstitute a borrowed slice from a raw pointer+length, tolerating the empty
/// case (a null pointer with length 0 is valid — associated data / plaintext may
/// legitimately be empty).
///
/// # Safety
/// `ptr` must be valid for `len` bytes, or `len` must be 0.
unsafe fn as_slice<'a>(ptr: *const u8, len: usize) -> &'a [u8] {
    if len == 0 {
        &[]
    } else {
        unsafe { core::slice::from_raw_parts(ptr, len) }
    }
}

/// AES-GCM seal. Selects AES-128 or AES-256 by `key_len` (16 or 32).
///
/// Writes `msg_len + 16` bytes (`ciphertext ‖ tag`) into `out`, which the caller
/// must have sized to `msg_len + 16`. Returns 0 on success.
///
/// # Safety
/// Every pointer must be valid for its stated length; `out` for `msg_len + 16`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn drorb_aes_fallback_seal(
    key: *const u8,
    key_len: usize,
    nonce: *const u8,
    nonce_len: usize,
    ad: *const u8,
    ad_len: usize,
    msg: *const u8,
    msg_len: usize,
    out: *mut u8,
) -> i32 {
    let Some(alg) = alg_for_key(key_len) else {
        return RC_BAD_SIZE;
    };
    if nonce_len != NONCE_LEN {
        return RC_BAD_SIZE;
    }

    let key_bytes = unsafe { as_slice(key, key_len) };
    let nonce_bytes = unsafe { as_slice(nonce, nonce_len) };
    let ad_bytes = unsafe { as_slice(ad, ad_len) };
    let msg_bytes = unsafe { as_slice(msg, msg_len) };

    let Ok(unbound) = UnboundKey::new(alg, key_bytes) else {
        return RC_INTERNAL;
    };
    let sealing = LessSafeKey::new(unbound);

    let mut nonce_arr = [0u8; NONCE_LEN];
    nonce_arr.copy_from_slice(nonce_bytes);
    let nonce = Nonce::assume_unique_for_key(nonce_arr);

    // in_out starts as the plaintext; seal appends the tag in place.
    let mut in_out = msg_bytes.to_vec();
    if sealing
        .seal_in_place_append_tag(nonce, Aad::from(ad_bytes), &mut in_out)
        .is_err()
    {
        return RC_INTERNAL;
    }

    debug_assert_eq!(in_out.len(), msg_len + TAG_LEN);
    let out_slice = unsafe { core::slice::from_raw_parts_mut(out, msg_len + TAG_LEN) };
    out_slice.copy_from_slice(&in_out);
    RC_OK
}

/// AES-GCM open. Selects AES-128 or AES-256 by `key_len` (16 or 32).
///
/// `ct` is `ciphertext ‖ tag` of length `ct_len` (>= 16). On a valid tag, writes
/// `ct_len - 16` plaintext bytes into `out` (caller-sized to `ct_len - 16`) and
/// returns 0. Returns nonzero on a bad size or authentication failure; `out` is
/// left untouched in that case.
///
/// # Safety
/// Every pointer must be valid for its stated length; `out` for `ct_len - 16`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn drorb_aes_fallback_open(
    key: *const u8,
    key_len: usize,
    nonce: *const u8,
    nonce_len: usize,
    ad: *const u8,
    ad_len: usize,
    ct: *const u8,
    ct_len: usize,
    out: *mut u8,
) -> i32 {
    let Some(alg) = alg_for_key(key_len) else {
        return RC_BAD_SIZE;
    };
    if nonce_len != NONCE_LEN || ct_len < TAG_LEN {
        return RC_BAD_SIZE;
    }

    let key_bytes = unsafe { as_slice(key, key_len) };
    let nonce_bytes = unsafe { as_slice(nonce, nonce_len) };
    let ad_bytes = unsafe { as_slice(ad, ad_len) };
    let ct_bytes = unsafe { as_slice(ct, ct_len) };

    let Ok(unbound) = UnboundKey::new(alg, key_bytes) else {
        return RC_INTERNAL;
    };
    let opening = LessSafeKey::new(unbound);

    let mut nonce_arr = [0u8; NONCE_LEN];
    nonce_arr.copy_from_slice(nonce_bytes);
    let nonce = Nonce::assume_unique_for_key(nonce_arr);

    // open_in_place verifies the tag and returns the plaintext prefix in place.
    let mut in_out = ct_bytes.to_vec();
    let plain = match opening.open_in_place(nonce, Aad::from(ad_bytes), &mut in_out) {
        Ok(p) => p,
        Err(_) => return RC_AUTH_FAIL,
    };

    let plain_len = ct_len - TAG_LEN;
    debug_assert_eq!(plain.len(), plain_len);
    let out_slice = unsafe { core::slice::from_raw_parts_mut(out, plain_len) };
    out_slice.copy_from_slice(plain);
    RC_OK
}

/// AES-ECB single-block encryption — the QUIC header-protection primitive for the
/// AES cipher suites (RFC 9001 §5.4.3: `mask = AES-ECB(hp_key, sample)`).
///
/// Encrypts exactly one 16-byte block in raw ECB (no padding, no IV): out =
/// AES(key, block). The key length selects the cipher (16 = AES-128, 32 =
/// AES-256; QUIC Initials use AES-128). Header protection consumes the first 5
/// bytes of the result as the mask. Same trust status as the AES-GCM fallback —
/// a portable, well-audited backend used where the verified EverCrypt/Vale AES is
/// unavailable (no AES-NI, e.g. arm64); NOT part of the machine-checked TCB.
///
/// Returns 0 on success (16 bytes written to `out`); nonzero on a bad key/block
/// size or an internal error, leaving `out` untouched.
///
/// # Safety
/// `key` valid for `key_len`; `block` and `out` each valid for 16 bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn drorb_aes_ecb_fallback(
    key: *const u8,
    key_len: usize,
    block: *const u8,
    block_len: usize,
    out: *mut u8,
) -> i32 {
    let alg = match key_len {
        16 => &AES_128,
        32 => &AES_256,
        _ => return RC_BAD_SIZE,
    };
    if block_len != AES_BLOCK_LEN {
        return RC_BAD_SIZE;
    }

    let key_bytes = unsafe { as_slice(key, key_len) };
    let block_bytes = unsafe { as_slice(block, block_len) };

    let Ok(unbound) = UnboundCipherKey::new(alg, key_bytes) else {
        return RC_INTERNAL;
    };
    let Ok(enc) = EncryptingKey::ecb(unbound) else {
        return RC_INTERNAL;
    };

    // Raw single-block ECB: no padding, no IV; encrypts the 16-byte block in place.
    let mut in_out = block_bytes.to_vec();
    if enc.encrypt(&mut in_out).is_err() {
        return RC_INTERNAL;
    }
    if in_out.len() != AES_BLOCK_LEN {
        return RC_INTERNAL;
    }

    let out_slice = unsafe { core::slice::from_raw_parts_mut(out, AES_BLOCK_LEN) };
    out_slice.copy_from_slice(&in_out);
    RC_OK
}

/// Strip leading zero bytes from a big-endian integer. aws-lc's
/// `RsaPublicKeyComponents::build_rsa` REJECTS a component whose first byte is
/// `0x00`, but a DER `INTEGER` modulus carries exactly such a `0x00` sign octet
/// (its high bit is set). The verified client hands the modulus/exponent through
/// as they appear in the certificate SPKI, so normalize here.
fn strip_leading_zeros(b: &[u8]) -> &[u8] {
    let mut i = 0;
    while i < b.len() && b[i] == 0 {
        i += 1;
    }
    &b[i..]
}

/// RSASSA-PKCS1-v1_5 / SHA-256 signature verification — `sha256WithRSAEncryption`
/// (OID 1.2.840.113549.1.1.11), the padding MOST real RSA CA chains sign with
/// (Let's Encrypt's RSA intermediates R10/R11 and ISRG Root X1 included).
///
/// `n`/`e` are the big-endian RSA modulus and public exponent as carried in the
/// certificate SPKI (a leading DER `0x00` sign octet is tolerated — stripped
/// here); `sig` is the raw signature (`ceil(modBits/8)` bytes); `msg` is the raw
/// signed content (the TBSCertificate — aws-lc hashes it with SHA-256 internally).
///
/// Returns `1` iff `sig` is a valid PKCS#1 v1.5 SHA-256 signature over `msg`
/// under `(n, e)`; `0` on an empty/zero component, an out-of-range modulus
/// (aws-lc's `RSA_PKCS1_2048_8192_SHA256` enforces 2048..=8192 bits), or a failed
/// check. Fail-CLOSED — never panics. Backed by audited aws-lc
/// (`EVP_DigestVerify`, the `aws_lc_0_42_0` namespace — never openssl); the RSA
/// analog of the AES-GCM fallback, NOT part of the machine-checked TCB. See
/// `CRYPTO-FFI-README.md`.
///
/// # Safety
/// Each pointer must be valid for its stated length, or the length must be 0.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn drorb_rsa_fallback_pkcs1_sha256_verify(
    n: *const u8,
    n_len: usize,
    e: *const u8,
    e_len: usize,
    sig: *const u8,
    sig_len: usize,
    msg: *const u8,
    msg_len: usize,
) -> u8 {
    let n_bytes = strip_leading_zeros(unsafe { as_slice(n, n_len) });
    let e_bytes = strip_leading_zeros(unsafe { as_slice(e, e_len) });
    let sig_bytes = unsafe { as_slice(sig, sig_len) };
    let msg_bytes = unsafe { as_slice(msg, msg_len) };

    if n_bytes.is_empty() || e_bytes.is_empty() {
        return 0;
    }

    let comps = RsaPublicKeyComponents {
        n: n_bytes,
        e: e_bytes,
    };
    match comps.verify(&RSA_PKCS1_2048_8192_SHA256, msg_bytes, sig_bytes) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}

/// Lowercase-hex encode `bytes` (no separators). Used for the salt/dk fields of
/// the stored PBKDF2 string.
fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(HEX[(b >> 4) as usize] as char);
        s.push(HEX[(b & 0x0f) as usize] as char);
    }
    s
}

/// Decode an even-length lowercase/uppercase-hex string. `None` on any non-hex
/// byte or an odd length — the stored field is malformed, fail closed.
fn hex_decode(s: &str) -> Option<Vec<u8>> {
    let bytes = s.as_bytes();
    if bytes.is_empty() || bytes.len() % 2 != 0 {
        return None;
    }
    let val = |c: u8| -> Option<u8> {
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            b'A'..=b'F' => Some(c - b'A' + 10),
            _ => None,
        }
    };
    let mut out = Vec::with_capacity(bytes.len() / 2);
    let mut i = 0;
    while i < bytes.len() {
        out.push((val(bytes[i])? << 4) | val(bytes[i + 1])?);
        i += 2;
    }
    Some(out)
}

/// Parse a `pbkdf2_sha256$<iterations>$<salt_hex>$<dk_hex>` stored string and
/// verify `pw` against it via AWS-LC PBKDF2-HMAC-SHA256. Any structural error is
/// a fail-closed `false`.
fn pbkdf2_verify(pw: &[u8], stored: &str) -> bool {
    let mut parts = stored.split('$');
    let (scheme, iters_s, salt_h, dk_h) =
        match (parts.next(), parts.next(), parts.next(), parts.next()) {
            (Some(a), Some(b), Some(c), Some(d)) => (a, b, c, d),
            _ => return false,
        };
    // Exactly four `$`-fields — reject any trailing segment.
    if parts.next().is_some() || scheme != "pbkdf2_sha256" {
        return false;
    }
    let iterations = match iters_s.parse::<u32>().ok().and_then(NonZeroU32::new) {
        Some(n) => n,
        None => return false,
    };
    let salt = match hex_decode(salt_h) {
        Some(s) => s,
        None => return false,
    };
    let dk = match hex_decode(dk_h) {
        Some(d) => d,
        None => return false,
    };
    // `pbkdf2::verify` re-derives at (iterations, salt) and compares in CONSTANT
    // TIME (AWS-LC `verify_slices_are_equal`). Fails closed on any mismatch.
    pbkdf2::verify(pbkdf2::PBKDF2_HMAC_SHA256, iterations, &salt, pw, &dk).is_ok()
}

/// PBKDF2-HMAC-SHA256 password verification — the AUDITED adaptive-KDF
/// `basic_auth` backend (AWS-LC, replacing the former pure-Rust bcrypt).
///
/// `password` is the raw presented password bytes; `hash` is the stored ASCII
/// string `pbkdf2_sha256$<iterations>$<salt_hex>$<dk_hex>`. The stored iteration
/// count (e.g. `600000`) and 16-byte random salt are parsed out and used to
/// re-derive the 32-byte PBKDF2 key of `password`, which is compared against the
/// stored derived key in CONSTANT TIME (`aws_lc_rs::pbkdf2::verify` →
/// AWS-LC `verify_slices_are_equal`).
///
/// This is a genuine adaptive KDF: the iteration count drives that many HMAC-SHA256
/// rounds, so verification takes measurable time (a real work factor), and each
/// stored hash carries its own CSPRNG salt (no precomputation / rainbow tables).
/// Unlike a bare SHA-256, that is what makes an offline crack of a leaked hash
/// expensive.
///
/// Returns `1` iff `password` verifies against `hash`; `0` on a wrong password, a
/// malformed / non-ASCII / non-`pbkdf2_sha256` stored string, or any parse error —
/// fail-CLOSED, never panics.
///
/// Backing / trust posture: AWS-LC `PKCS5_PBKDF2_HMAC` via `aws_lc_rs::pbkdf2` —
/// the SAME audited primitive as this crate's AES-GCM/RSA paths, NOT the old
/// pure-Rust bcrypt. No openssl, no bcrypt/blowfish. Not part of the
/// machine-checked TCB (an audited-primitive backend). See `CRYPTO-FFI-README.md`.
///
/// # Safety
/// Each pointer must be valid for its stated length, or the length must be 0.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn drorb_pbkdf2_fallback_verify(
    password: *const u8,
    password_len: usize,
    hash: *const u8,
    hash_len: usize,
) -> u8 {
    let pw = unsafe { as_slice(password, password_len) };
    let hash_bytes = unsafe { as_slice(hash, hash_len) };
    // The stored hash is an ASCII modular string; a non-UTF-8 stored value is not
    // a valid hash — fail closed.
    let stored = match core::str::from_utf8(hash_bytes) {
        Ok(s) => s,
        Err(_) => return 0,
    };
    if pbkdf2_verify(pw, stored) { 1 } else { 0 }
}

/// PBKDF2-HMAC-SHA256 hash generation — the operator/helper side of the
/// `basic_auth` credential store.
///
/// Derives a fresh stored hash for `password` at `iterations` rounds, using a
/// 16-byte salt drawn from AWS-LC's CSPRNG (`aws_lc_rs::rand::fill`) and a 32-byte
/// PBKDF2-HMAC-SHA256 derived key, and writes the ASCII string
/// `pbkdf2_sha256$<iterations>$<salt_hex>$<dk_hex>` into `out` (capacity `out_cap`).
/// Returns the number of bytes written, or `0` on a zero iteration count, a CSPRNG
/// failure, or `out_cap` too small (nothing is written in that case). Never panics.
///
/// # Safety
/// `password` must be valid for `password_len` bytes (or `password_len == 0`);
/// `out` must be valid for `out_cap` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn drorb_pbkdf2_fallback_hash(
    password: *const u8,
    password_len: usize,
    iterations: u32,
    out: *mut u8,
    out_cap: usize,
) -> usize {
    let pw = unsafe { as_slice(password, password_len) };
    let iters = match NonZeroU32::new(iterations) {
        Some(n) => n,
        None => return 0,
    };
    let mut salt = [0u8; PBKDF2_SALT_LEN];
    if aws_lc_rs::rand::fill(&mut salt).is_err() {
        return 0;
    }
    let mut dk = [0u8; PBKDF2_DK_LEN];
    pbkdf2::derive(pbkdf2::PBKDF2_HMAC_SHA256, iters, &salt, pw, &mut dk);
    let s = format!(
        "pbkdf2_sha256${}${}${}",
        iterations,
        hex_encode(&salt),
        hex_encode(&dk)
    );
    let bytes = s.as_bytes();
    if bytes.len() > out_cap {
        return 0;
    }
    unsafe { core::ptr::copy_nonoverlapping(bytes.as_ptr(), out, bytes.len()) };
    bytes.len()
}

/// Fill `out[..len]` with cryptographically-secure random bytes from AWS-LC's
/// CSPRNG (`aws_lc_rs::rand::fill`) — the SAME audited entropy source that seeds
/// the PBKDF2 salt above. The control plane mints pre-auth key secrets with this,
/// NEVER the `rand` crate's PRNG. Returns `len` on success, `0` on failure or a
/// null/zero request (fail-closed). NOT part of the machine-checked TCB.
///
/// # Safety
/// `out` must be non-null and point to at least `len` writable bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn drorb_rand_fallback_bytes(out: *mut u8, len: usize) -> usize {
    if out.is_null() || len == 0 {
        return 0;
    }
    let buf = unsafe { core::slice::from_raw_parts_mut(out, len) };
    match aws_lc_rs::rand::fill(buf) {
        Ok(()) => len,
        Err(_) => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Seal then open via the C ABI; assert the plaintext round-trips and that a
    /// single flipped ciphertext byte fails authentication.
    fn roundtrip(key: &[u8], nonce: &[u8], ad: &[u8], msg: &[u8]) {
        let mut sealed = vec![0u8; msg.len() + TAG_LEN];
        let rc = unsafe {
            drorb_aes_fallback_seal(
                key.as_ptr(),
                key.len(),
                nonce.as_ptr(),
                nonce.len(),
                ad.as_ptr(),
                ad.len(),
                msg.as_ptr(),
                msg.len(),
                sealed.as_mut_ptr(),
            )
        };
        assert_eq!(rc, RC_OK, "seal failed");

        let mut opened = vec![0u8; msg.len()];
        let rc = unsafe {
            drorb_aes_fallback_open(
                key.as_ptr(),
                key.len(),
                nonce.as_ptr(),
                nonce.len(),
                ad.as_ptr(),
                ad.len(),
                sealed.as_ptr(),
                sealed.len(),
                opened.as_mut_ptr(),
            )
        };
        assert_eq!(rc, RC_OK, "open failed");
        assert_eq!(&opened, msg, "plaintext mismatch");

        // Tamper: flip one ciphertext byte, expect an auth failure.
        let mut bad = sealed.clone();
        bad[0] ^= 0xff;
        let mut opened2 = vec![0u8; msg.len()];
        let rc = unsafe {
            drorb_aes_fallback_open(
                key.as_ptr(),
                key.len(),
                nonce.as_ptr(),
                nonce.len(),
                ad.as_ptr(),
                ad.len(),
                bad.as_ptr(),
                bad.len(),
                opened2.as_mut_ptr(),
            )
        };
        assert_ne!(rc, RC_OK, "tampered ciphertext must NOT open");
    }

    #[test]
    fn aes128_roundtrip_and_tamper() {
        let key = [0x02u8; 16];
        let nonce = [0u8; 12];
        let ad = b"quic-initial";
        roundtrip(&key, &nonce, ad, b"AES-128-GCM through aws-lc-rs");
    }

    #[test]
    fn aes256_roundtrip_and_tamper() {
        let key = [0x02u8; 32];
        let nonce = [0u8; 12];
        let ad = b"quic-initial";
        roundtrip(&key, &nonce, ad, b"AES-256-GCM through aws-lc-rs");
    }

    /// NIST GCM known-answer: AES-128, all-zero key/IV, empty plaintext, empty
    /// AAD ⇒ tag 58e2fccefa7e3061367f1d57a4e7455a (NIST GCM test case 1).
    #[test]
    fn aes128_nist_case1_tag() {
        let key = [0u8; 16];
        let nonce = [0u8; 12];
        let mut sealed = vec![0u8; TAG_LEN];
        let rc = unsafe {
            drorb_aes_fallback_seal(
                key.as_ptr(),
                16,
                nonce.as_ptr(),
                12,
                core::ptr::null(),
                0,
                core::ptr::null(),
                0,
                sealed.as_mut_ptr(),
            )
        };
        assert_eq!(rc, RC_OK);
        let expect = [
            0x58, 0xe2, 0xfc, 0xce, 0xfa, 0x7e, 0x30, 0x61, 0x36, 0x7f, 0x1d, 0x57, 0xa4, 0xe7,
            0x45, 0x5a,
        ];
        assert_eq!(sealed, expect, "NIST GCM case-1 tag mismatch");
    }

    /// FIPS-197 Appendix C.1 AES-128 ECB known-answer: key 000102…0f, plaintext
    /// 00112233…ff ⇒ ciphertext 69c4e0d86a7b0430d8cdb78070b4c55a. This is the raw
    /// AES block function QUIC header protection (RFC 9001 §5.4.3) runs on.
    #[test]
    fn aes128_ecb_fips197_c1() {
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];
        let block = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff,
        ];
        let mut out = [0u8; 16];
        let rc = unsafe {
            drorb_aes_ecb_fallback(key.as_ptr(), 16, block.as_ptr(), 16, out.as_mut_ptr())
        };
        assert_eq!(rc, RC_OK);
        let expect = [
            0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4,
            0xc5, 0x5a,
        ];
        assert_eq!(out, expect, "FIPS-197 C.1 AES-128 ECB block mismatch");
    }

    /// FIPS-197 Appendix C.3 AES-256 ECB known-answer: key 000102…1f, plaintext
    /// 00112233…ff ⇒ ciphertext 8ea2b7ca516745bfeafc49904b496089.
    #[test]
    fn aes256_ecb_fips197_c3() {
        let key: [u8; 32] = core::array::from_fn(|i| i as u8);
        let block = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff,
        ];
        let mut out = [0u8; 16];
        let rc = unsafe {
            drorb_aes_ecb_fallback(key.as_ptr(), 32, block.as_ptr(), 16, out.as_mut_ptr())
        };
        assert_eq!(rc, RC_OK);
        let expect = [
            0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf, 0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49,
            0x60, 0x89,
        ];
        assert_eq!(out, expect, "FIPS-197 C.3 AES-256 ECB block mismatch");
    }

    /// AES-256 NIST GCM known-answer: all-zero key/IV, empty plaintext/AAD ⇒ tag
    /// 530f8afbc74536b9a963b4f1c4cb738b.
    #[test]
    fn aes256_nist_tag() {
        let key = [0u8; 32];
        let nonce = [0u8; 12];
        let mut sealed = vec![0u8; TAG_LEN];
        let rc = unsafe {
            drorb_aes_fallback_seal(
                key.as_ptr(),
                32,
                nonce.as_ptr(),
                12,
                core::ptr::null(),
                0,
                core::ptr::null(),
                0,
                sealed.as_mut_ptr(),
            )
        };
        assert_eq!(rc, RC_OK);
        let expect = [
            0x53, 0x0f, 0x8a, 0xfb, 0xc7, 0x45, 0x36, 0xb9, 0xa9, 0x63, 0xb4, 0xf1, 0xc4, 0xcb,
            0x73, 0x8b,
        ];
        assert_eq!(sealed, expect, "NIST GCM AES-256 tag mismatch");
    }

    /// RSA PKCS#1 v1.5 / SHA-256 verify round-trip through the C ABI: generate a
    /// 2048-bit key, sign a message with `sha256WithRSAEncryption`, extract the
    /// public `(n, e)`, and confirm the shim accepts the genuine signature,
    /// rejects a one-byte-tampered signature, rejects the signature over a
    /// different message, and fail-closes on empty components. This is the same
    /// audited aws-lc primitive the verified TLS client's X.509 path builder
    /// reaches for a PKCS#1 v1.5 CA link.
    #[test]
    fn rsa_pkcs1_sha256_verify_roundtrip_and_reject() {
        use aws_lc_rs::rand::SystemRandom;
        use aws_lc_rs::rsa::KeySize;
        use aws_lc_rs::signature::{KeyPair, RSA_PKCS1_SHA256, RsaKeyPair};

        let kp = RsaKeyPair::generate(KeySize::Rsa2048).expect("keygen");
        let n = kp
            .public_key()
            .modulus()
            .big_endian_without_leading_zero()
            .to_vec();
        let e = kp
            .public_key()
            .exponent()
            .big_endian_without_leading_zero()
            .to_vec();

        let msg = b"drorb verified TLS client: PKCS#1 v1.5 CA link";
        let mut sig = vec![0u8; kp.public_modulus_len()];
        let rng = SystemRandom::new();
        kp.sign(&RSA_PKCS1_SHA256, &rng, msg, &mut sig)
            .expect("sign");

        let ok = unsafe {
            drorb_rsa_fallback_pkcs1_sha256_verify(
                n.as_ptr(),
                n.len(),
                e.as_ptr(),
                e.len(),
                sig.as_ptr(),
                sig.len(),
                msg.as_ptr(),
                msg.len(),
            )
        };
        assert_eq!(ok, 1, "genuine PKCS#1 v1.5 signature must verify");

        // A DER modulus carries a 0x00 sign octet; the shim must strip it and
        // still accept (mirrors the certificate SPKI byte shape).
        let mut n_der = vec![0u8];
        n_der.extend_from_slice(&n);
        let ok_der = unsafe {
            drorb_rsa_fallback_pkcs1_sha256_verify(
                n_der.as_ptr(),
                n_der.len(),
                e.as_ptr(),
                e.len(),
                sig.as_ptr(),
                sig.len(),
                msg.as_ptr(),
                msg.len(),
            )
        };
        assert_eq!(ok_der, 1, "leading 0x00 sign octet must be tolerated");

        // Tampered signature: flip one byte, expect rejection.
        let mut bad = sig.clone();
        bad[0] ^= 0xff;
        let rej = unsafe {
            drorb_rsa_fallback_pkcs1_sha256_verify(
                n.as_ptr(),
                n.len(),
                e.as_ptr(),
                e.len(),
                bad.as_ptr(),
                bad.len(),
                msg.as_ptr(),
                msg.len(),
            )
        };
        assert_eq!(rej, 0, "tampered signature must NOT verify");

        // Wrong message: same signature, different content, expect rejection.
        let wrong = unsafe {
            drorb_rsa_fallback_pkcs1_sha256_verify(
                n.as_ptr(),
                n.len(),
                e.as_ptr(),
                e.len(),
                sig.as_ptr(),
                sig.len(),
                b"different message".as_ptr(),
                b"different message".len(),
            )
        };
        assert_eq!(
            wrong, 0,
            "signature over a different message must NOT verify"
        );

        // Empty modulus: fail-closed.
        let empty = unsafe {
            drorb_rsa_fallback_pkcs1_sha256_verify(
                core::ptr::null(),
                0,
                e.as_ptr(),
                e.len(),
                sig.as_ptr(),
                sig.len(),
                msg.as_ptr(),
                msg.len(),
            )
        };
        assert_eq!(empty, 0, "empty modulus must fail closed");
    }

    /// PBKDF2 gen+verify via the C ABI: a freshly generated hash for a password
    /// verifies for the correct password, rejects a wrong one, and a malformed
    /// stored string fails closed. Generated at a low iteration count for test
    /// speed; the deployed config uses 600 000.
    #[test]
    fn pbkdf2_gen_and_verify_via_abi() {
        let mut buf = [0u8; 256];
        let n = unsafe {
            drorb_pbkdf2_fallback_hash(
                b"orbtender-2026".as_ptr(),
                b"orbtender-2026".len(),
                4096,
                buf.as_mut_ptr(),
                buf.len(),
            )
        };
        assert!(n > 0, "hash generation must succeed");
        let stored = &buf[..n];
        let stored_str = core::str::from_utf8(stored).unwrap();
        assert!(
            stored_str.starts_with("pbkdf2_sha256$4096$"),
            "expected pbkdf2_sha256 modular string, got {stored_str}"
        );

        let ok = unsafe {
            drorb_pbkdf2_fallback_verify(
                b"orbtender-2026".as_ptr(),
                b"orbtender-2026".len(),
                stored.as_ptr(),
                stored.len(),
            )
        };
        assert_eq!(ok, 1, "correct password must verify");

        let bad = unsafe {
            drorb_pbkdf2_fallback_verify(
                b"wrongpass".as_ptr(),
                b"wrongpass".len(),
                stored.as_ptr(),
                stored.len(),
            )
        };
        assert_eq!(bad, 0, "wrong password must reject");

        let junk = b"not-a-pbkdf2-hash";
        let junk_r =
            unsafe { drorb_pbkdf2_fallback_verify(b"x".as_ptr(), 1, junk.as_ptr(), junk.len()) };
        assert_eq!(junk_r, 0, "malformed stored hash must fail closed");
    }
}
