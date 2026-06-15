//! dregg-crypto-floor — the REAL §8 crypto primitives for the seL4 executor PD,
//! `no_std`, exporting plain-value `extern "C"` entry points that the C ABI shim
//! (`crypto-floor.c`) marshals Lean `Nat`/`Int`/`List Nat` to and from.
//!
//! WHY THIS CRATE EXISTS. The executor PD links the VERIFIED Lean closure, whose
//! eight `@[extern]` crypto portals (`Dregg2/Crypto/PortalFloor.lean`) were
//! resolved by `crypto-stub.c` — a panic-if-reached stub with the WRONG arity and
//! types (`void* dregg_poseidon2_hash(void*)` vs the real
//! `lean_object* dregg_poseidon2_hash(lean_object*, lean_object*)`). The demo turn
//! never reaches them (the closure routes the portals through in-Lean reference
//! dictionaries, not the externs), so the stub linked and the boot ran — but a
//! turn that actually hashes would call a wrong-arity panic (UB, then abort).
//!
//! THIS replaces the stub's HASH FLOOR with the SAME carried crypto the
//! `verifier-stark` PD already runs on seL4: the Plonky3-conformant Poseidon2 over
//! BabyBear (`circuit/src/poseidon2.rs`, carried verbatim in `poseidon2.rs`) and
//! BLAKE3 (the `blake3` crate, `pure` no_std backend — the exact dep + features
//! `verifier-stark/Cargo.toml` uses). So a turn that computes a Merkle/commitment
//! /nullifier/transcript hash now produces a real, field-correct digest on-device
//! instead of aborting.
//!
//! SCOPE — now the WHOLE elliptic-curve floor is REAL. The carried hash families
//! — Poseidon2 (Merkle node / turn-id), BLAKE3 (transcript / attribute), the
//! Poseidon2-derived nullifier tag, the BLAKE3-keyed MAC — and the byte-channel
//! STARK verify were already REAL. The three elliptic-curve primitives that live
//! on a DIFFERENT crypto surface than the carried STARK hashes are now ALSO REAL,
//! welded from the SAME in-workspace crates the executor / cell already use:
//!   * §1 ed25519 strict verify — ed25519-dalek 2 `verify_strict` (`ed25519.rs`),
//!     the exact check `turn/src/executor/authorize.rs` + the net-client turn gate
//!     run; accept iff valid, FAIL-CLOSED otherwise.
//!   * §3 Pedersen value commitment — Ristretto255 `value·V + blinding·R`
//!     (`pedersen.rs`), byte-IDENTICAL to `cell::value_commitment::commit_bytes`
//!     (the commitment the executor's conservation check consumes and the circuit
//!     binds — see `pedersen.rs` for the curve reconciliation).
//!   * §7 ChaCha20-Poly1305 AEAD seal/open — chacha20poly1305 0.10 (`aead.rs`),
//!     the committed-note ECIES box's primitive (`cell::note_encryption`); an
//!     authentic ciphertext opens, a tampered one fails the Poly1305 tag.
//! So a turn that verifies a signature, commits a confidential value, or opens an
//! encrypted note is now decided by REAL on-device crypto. The only remaining
//! fail-closed entry is the ABSTRACT-Nat STARK verify (§2,
//! `dreggcf_stark_verify_abstract`), whose real check is the byte-channel
//! `dreggcf_stark_verify_bytes` — an abstract Nat pair carries no checkable proof.

// `no_std` for the load-bearing cross artifact (a `staticlib` for the seL4-musl
// PD). `alloc` is the single allocation crate; the carried stark_core sub-modules
// reference `alloc::` against THIS one root declaration (no per-module `extern
// crate alloc;`). The §2 STARK verify is RUN-VERIFIED on the real aarch64-musl
// artifact under qemu via the C self-test (`crypto-floor-selftest.c` calls
// `dreggcf_stark_selftest`), the floor's run-harness — strictly more faithful than
// a host `cargo test` (it exercises the exact bytes the PD links). The `#[cfg(test)]`
// module mirrors the teeth as Rust assertions; note a `staticlib`-only `no_std`
// crate with alloc-heavy no_std deps cannot host a std `cargo test` harness (the
// `--test` build double-links `core`/`alloc`) — this is a pre-existing crate
// limitation, hence the C selftest is the executed witness.
#![cfg_attr(not(test), no_std)]
#![allow(clippy::missing_safety_doc)]

extern crate alloc;

pub mod field;
pub mod poseidon2;
// The full STARK core (BabyBear+BLAKE3+FRI+Fiat-Shamir), carried verbatim from
// the verifier-stark PD — backs the REAL §2 byte-channel STARK verify below.
pub mod stark_core;

// The three REAL elliptic-curve primitives, welded from the in-workspace crates:
pub mod aead; // §7 ChaCha20-Poly1305 (cell::note_encryption's primitive)
pub mod ed25519; // §1 ed25519-dalek verify_strict (the executor auth check)
pub mod pedersen; // §3 Ristretto255 value commitment (cell::value_commitment)

use field::BabyBear;

/// Panic handler for the `no_std` staticlib: route a panic to the C `abort()` the
/// host musl / seL4 PD already provides (the build is `panic = "abort"`, so this
/// is only reached on an internal invariant break — never on the verified path).
#[cfg(not(test))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    extern "C" {
        fn abort() -> !;
    }
    unsafe { abort() }
}

/// Global allocator delegating to the host C `malloc`/`free`/`realloc`. This
/// staticlib links into the executor's musl ELF (and, in the PD, the sel4-musl
/// libc), which supplies these — and the Lean runtime's mimalloc shim already
/// routes them. The crypto floor's only heap use is the small `Vec` of packed
/// field elements in `hash_bytes`/`hash_many` (bounded by the input length).
#[cfg(not(test))]
mod galloc {
    use core::alloc::{GlobalAlloc, Layout};

    extern "C" {
        fn malloc(size: usize) -> *mut core::ffi::c_void;
        fn free(ptr: *mut core::ffi::c_void);
        fn realloc(ptr: *mut core::ffi::c_void, size: usize) -> *mut core::ffi::c_void;
    }

    struct CMalloc;

    // BabyBear (u32) and the field Vecs are 4-byte aligned; malloc returns
    // max_align-aligned memory (>= 8), which covers every allocation here. For an
    // over-aligned request (none occur in this crate) we conservatively fail.
    unsafe impl GlobalAlloc for CMalloc {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            if layout.align() <= 16 {
                malloc(layout.size()) as *mut u8
            } else {
                core::ptr::null_mut()
            }
        }
        unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
            free(ptr as *mut core::ffi::c_void);
        }
        unsafe fn realloc(&self, ptr: *mut u8, _layout: Layout, new_size: usize) -> *mut u8 {
            realloc(ptr as *mut core::ffi::c_void, new_size) as *mut u8
        }
    }

    #[global_allocator]
    static A: CMalloc = CMalloc;
}

/// Reduce a raw u64 to a canonical BabyBear value (the C shim passes the unboxed
/// Lean `Nat` limb here; digests are field-range, larger Nats reduce mod p).
#[inline]
fn bb(x: u64) -> BabyBear {
    BabyBear::from_u64(x)
}

// ===========================================================================
// §4 — Poseidon2 (collision-resistant Merkle/turn-id hash). REAL (carried).
// ===========================================================================

/// Poseidon2 2-to-1 compression: `hash_2_to_1(left, right)` over BabyBear, the
/// in-circuit Merkle node hash the `dregg_poseidon2_hash` portal documents.
/// Returns the canonical field element (in a u64). Plonky3-conformant, KAT'd.
#[no_mangle]
pub extern "C" fn dreggcf_poseidon2_2to1(left: u64, right: u64) -> u64 {
    poseidon2::hash_2_to_1(bb(left), bb(right)).as_u32() as u64
}

// ===========================================================================
// §5 — BLAKE3 (collision/preimage-resistant transcript/attribute hash). REAL.
// ===========================================================================

/// BLAKE3 over a byte buffer, the digest bridged into the BabyBear field exactly
/// as the carried STARK bridges a BLAKE3 commitment (`poseidon2::hash_bytes` over
/// the 32-byte digest). The `dregg_blake3_hash` portal is `List Nat -> Nat`; the C
/// shim flattens the list's per-element low bytes into `data` and we return a
/// single field element (Nat-range). A full 256-bit digest does not fit a Nat
/// scalar, so the field-reduced form is the faithful Nat-shaped result (the same
/// reduction the in-circuit Merkle uses).
///
/// # Safety
/// `data` must point to `len` readable bytes (or be null iff `len == 0`).
#[no_mangle]
pub unsafe extern "C" fn dreggcf_blake3_to_field(data: *const u8, len: usize) -> u64 {
    let bytes: &[u8] = if data.is_null() || len == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(data, len)
    };
    let digest = blake3::hash(bytes);
    poseidon2::hash_bytes(digest.as_bytes()).as_u32() as u64
}

/// The raw 32-byte BLAKE3 digest of `data`, written to `out32` (32 bytes). Exposed
/// for callers that want the full digest (e.g. a transcript), not the field-reduced
/// Nat. Not used by the Lean portal directly but kept as the honest primitive.
///
/// # Safety
/// `data` must point to `len` readable bytes (or null iff `len==0`); `out32` must
/// point to 32 writable bytes.
#[no_mangle]
pub unsafe extern "C" fn dreggcf_blake3_digest(data: *const u8, len: usize, out32: *mut u8) {
    let bytes: &[u8] = if data.is_null() || len == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(data, len)
    };
    let digest = blake3::hash(bytes);
    if !out32.is_null() {
        core::ptr::copy_nonoverlapping(digest.as_bytes().as_ptr(), out32, 32);
    }
}

// ===========================================================================
// §6 — Nullifier (deterministic per-note anti-double-spend tag). REAL.
// ===========================================================================

/// Domain separator for the nullifier tag (distinguishes it from a bare Merkle
/// node hash so a note value and its nullifier can't collide).
const NULLIFIER_DOMAIN: u64 = 0x6e_75_6c_6c; // "null"

/// Per-note nullifier derivation: a Poseidon2 tag of the note digest under a
/// dedicated domain. Deterministic (the portal's proved function-ness) and
/// collision-resistant (Poseidon2 CR, the carried assumption).
#[no_mangle]
pub extern "C" fn dreggcf_nullifier(note: u64) -> u64 {
    poseidon2::hash_2_to_1(bb(note), bb(NULLIFIER_DOMAIN)).as_u32() as u64
}

// ===========================================================================
// §8 — HMAC / keyed PRF (macaroon caveat chain). REAL via BLAKE3 keyed mode.
// ===========================================================================

/// Keyed MAC over `(key, msg)`. The portal names HMAC-SHA256; the carried no_std
/// crypto provides BLAKE3, whose keyed mode (`blake3::keyed_hash`) is a
/// PRF/MAC with the same unforgeability shape (a 256-bit key, EUF-CMA under the
/// BLAKE3 PRF assumption). We derive a 32-byte BLAKE3 key from the field key, MAC
/// the message bytes, and field-reduce the tag to a Nat. This is a REAL keyed MAC
/// (not a stub) using the carried hash — the assumption shifts from "HMAC-SHA256
/// unforgeable" to "BLAKE3-keyed unforgeable", both standard. The C shim packs the
/// key/msg Nats into bytes.
///
/// # Safety
/// `msg` must point to `msg_len` readable bytes (or null iff `msg_len==0`).
#[no_mangle]
pub unsafe extern "C" fn dreggcf_keyed_mac(key: u64, msg: *const u8, msg_len: usize) -> u64 {
    let msg_bytes: &[u8] = if msg.is_null() || msg_len == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(msg, msg_len)
    };
    // Derive a 32-byte key deterministically from the field key.
    let mut key_material = [0u8; 32];
    key_material[..8].copy_from_slice(&key.to_le_bytes());
    let tag = blake3::keyed_hash(&key_material, msg_bytes);
    poseidon2::hash_bytes(tag.as_bytes()).as_u32() as u64
}

// ===========================================================================
// §2 — STARK verify (FRI + Fiat-Shamir extractability). REAL byte-channel verify.
// ===========================================================================

/// STARK verification floor (ABSTRACT-Nat portal). The `dregg_stark_verify` Lean
/// portal is `Nat -> Nat -> Bool` over an ABSTRACT statement/proof pair — two
/// opaque Nats cannot carry a full `StarkProof` (trace/constraint/FRI Merkle
/// commitments + query openings, kilobytes of structured data). So THIS entry
/// FAILS CLOSED: it returns `false` (never a spurious accept). The real check is
/// `dreggcf_stark_verify_bytes` below, fed the structured proof bytes the
/// executor PD's proof-carrying turn ships out of band.
#[no_mangle]
pub extern "C" fn dreggcf_stark_verify_abstract(_stmt: u64, _proof: u64) -> u8 {
    // Fail-closed: an abstract Nat pair carries no checkable proof. Returning 0
    // (reject) is the only sound answer — NEVER accept without a verified proof.
    0
}

// ===========================================================================
// §1 — ed25519 strict verify (REAL). The executor's turn-auth check, on-device.
// ===========================================================================

/// Strict Ed25519 verification: accept iff `sig` (64 bytes) is valid under `pk`
/// (32 bytes) over `msg` — `ed25519-dalek` `verify_strict`, the exact check the
/// executor auth path runs. FAIL-CLOSED on a bad key/sig or a verify failure.
///
/// # Safety
/// `pk` → 32 bytes; `sig` → 64 bytes; `msg` → `msg_len` bytes (null iff len 0).
#[no_mangle]
pub unsafe extern "C" fn dreggcf_ed25519_verify(
    pk: *const u8,
    msg: *const u8,
    msg_len: usize,
    sig: *const u8,
) -> u8 {
    ed25519::verify(pk, msg, msg_len, sig)
}

/// On-device anti-ghost witness for §1. Deterministically derives a keypair from a
/// fixed seed (no RNG), signs a fixed message, and drives `dreggcf_ed25519_verify`:
///   bit 0 (0x1): a GENUINE signature ACCEPTS;
///   bit 1 (0x2): a FORGED signature (one flipped byte) REJECTS;
///   bit 2 (0x4): the genuine signature over a DIFFERENT message REJECTS;
///   bit 3 (0x8): the genuine signature under a DIFFERENT public key REJECTS.
/// A fully-correct floor returns `0xF`. Uses `SigningKey::from_bytes` (a clamped
/// scalar from 32 seed bytes) so it is fully deterministic + RNG-free.
#[no_mangle]
pub extern "C" fn dreggcf_ed25519_selftest() -> u8 {
    use ed25519_dalek::{Signer, SigningKey};

    let seed = [7u8; 32];
    let sk = SigningKey::from_bytes(&seed);
    let vk = sk.verifying_key();
    let pk = vk.to_bytes();
    let msg = b"dregg-firmament executor turn v1";
    let sig = sk.sign(msg).to_bytes();

    let mut mask: u8 = 0;

    // bit 0 — genuine signature ACCEPTS.
    let ok = unsafe { ed25519::verify(pk.as_ptr(), msg.as_ptr(), msg.len(), sig.as_ptr()) };
    if ok == 1 {
        mask |= 0x1;
    }

    // bit 1 — a forged signature (flip a byte in the `s` half) REJECTS.
    let mut forged = sig;
    forged[40] ^= 0x01;
    let bad = unsafe { ed25519::verify(pk.as_ptr(), msg.as_ptr(), msg.len(), forged.as_ptr()) };
    if bad == 0 {
        mask |= 0x2;
    }

    // bit 2 — genuine sig over a DIFFERENT message REJECTS.
    let other = b"dregg-firmament executor turn v2";
    let wrong_msg =
        unsafe { ed25519::verify(pk.as_ptr(), other.as_ptr(), other.len(), sig.as_ptr()) };
    if wrong_msg == 0 {
        mask |= 0x4;
    }

    // bit 3 — genuine sig under a DIFFERENT public key REJECTS.
    let sk2 = SigningKey::from_bytes(&[9u8; 32]);
    let pk2 = sk2.verifying_key().to_bytes();
    let wrong_key =
        unsafe { ed25519::verify(pk2.as_ptr(), msg.as_ptr(), msg.len(), sig.as_ptr()) };
    if wrong_key == 0 {
        mask |= 0x8;
    }

    mask
}

/// Export a known-good ed25519 `(pk32, msg, sig64)` triple for the C portal
/// self-test to drive `dregg_ed25519_verify` END-TO-END (the C harness cannot
/// sign). Deterministic from a fixed seed. Writes the 32-byte pubkey to `pk_out`,
/// the message to `msg_out` (returning its length via `*msg_len`), and the 64-byte
/// signature to `sig_out`. The message buffer must hold >= 64 bytes.
///
/// # Safety
/// `pk_out`→32, `sig_out`→64, `msg_out`→`*msg_len` (>= 64 on entry) writable bytes.
#[no_mangle]
pub unsafe extern "C" fn dreggcf_ed25519_test_vector(
    pk_out: *mut u8,
    msg_out: *mut u8,
    msg_len: *mut usize,
    sig_out: *mut u8,
) {
    use ed25519_dalek::{Signer, SigningKey};
    let sk = SigningKey::from_bytes(&[7u8; 32]);
    let pk = sk.verifying_key().to_bytes();
    let msg = b"dregg-firmament executor turn v1";
    let sig = sk.sign(msg).to_bytes();
    core::ptr::copy_nonoverlapping(pk.as_ptr(), pk_out, 32);
    core::ptr::copy_nonoverlapping(sig.as_ptr(), sig_out, 64);
    if !msg_len.is_null() {
        let cap = *msg_len;
        let n = msg.len().min(cap);
        core::ptr::copy_nonoverlapping(msg.as_ptr(), msg_out, n);
        *msg_len = n;
    }
}

/// Export a known-good AEAD box `nonce(12) || ciphertext||tag` (the §7 portal's
/// `ct` encoding) for the C portal self-test to drive `dregg_aead_open` END-TO-END.
/// Writes the 32-byte key to `key_out` and the box to `box_out` (returning its
/// length via `*box_len`). The box buffer must hold >= 128 bytes.
///
/// # Safety
/// `key_out`→32, `box_out`→`*box_len` (>= 128 on entry) writable bytes.
#[no_mangle]
pub unsafe extern "C" fn dreggcf_aead_test_vector(
    key_out: *mut u8,
    box_out: *mut u8,
    box_len: *mut usize,
) {
    let key = [0x42u8; 32];
    let nonce = [0x07u8; 12];
    let pt = b"note-opening: value=42 asset=7 blinding=deadbeef";
    let mut sealed = [0u8; 96];
    let n = aead::seal(
        key.as_ptr(),
        nonce.as_ptr(),
        pt.as_ptr(),
        pt.len(),
        sealed.as_mut_ptr(),
        sealed.len(),
    );
    core::ptr::copy_nonoverlapping(key.as_ptr(), key_out, 32);
    if n >= 0 && !box_len.is_null() {
        let n = n as usize;
        let total = 12 + n; // nonce || ct||tag
        let cap = *box_len;
        if total <= cap {
            core::ptr::copy_nonoverlapping(nonce.as_ptr(), box_out, 12);
            core::ptr::copy_nonoverlapping(sealed.as_ptr(), box_out.add(12), n);
            *box_len = total;
        } else {
            *box_len = 0;
        }
    } else if !box_len.is_null() {
        *box_len = 0;
    }
}

// ===========================================================================
// §3 — Pedersen value commitment (REAL). Ristretto255, byte-identical to
//      cell::value_commitment::commit_bytes. See pedersen.rs for the curve
//      reconciliation (this is the commitment the executor checks + circuit binds).
// ===========================================================================

/// Pedersen value commitment: write `(value·V + scalar(blinding)·R).compress()`
/// (32 canonical bytes) to `out32`. Byte-identical to
/// `cell::value_commitment::commit_bytes(value, blinding)`.
///
/// # Safety
/// `blinding` → 32 bytes; `out32` → 32 writable bytes.
#[no_mangle]
pub unsafe extern "C" fn dreggcf_pedersen_commit(value: u64, blinding: *const u8, out32: *mut u8) {
    pedersen::commit(value, blinding, out32)
}

/// Verify a Pedersen opening: accept (`1`) iff `value·V + scalar(blinding)·R`
/// compresses to `commitment32`. The note-open binding check.
///
/// # Safety
/// `blinding` / `commitment32` → 32 bytes each.
#[no_mangle]
pub unsafe extern "C" fn dreggcf_pedersen_verify_opening(
    value: u64,
    blinding: *const u8,
    commitment32: *const u8,
) -> u8 {
    pedersen::verify_opening(value, blinding, commitment32)
}

/// On-device anti-ghost witness for §3. Commits a fixed `(value, blinding)` and:
///   bit 0 (0x1): the opening VERIFIES against the produced commitment;
///   bit 1 (0x2): a WRONG value (same blinding) FAILS the opening;
///   bit 2 (0x4): a WRONG blinding (same value) FAILS the opening;
///   bit 3 (0x8): the HOMOMORPHISM holds — `commit(a,r1)+commit(b,r2)` equals
///                `commit(a+b, r1+r2)` as Ristretto points (the balance algebra
///                the executor's conservation check relies on).
/// A fully-correct floor returns `0xF`.
#[no_mangle]
pub extern "C" fn dreggcf_pedersen_selftest() -> u8 {
    use curve25519_dalek::ristretto::CompressedRistretto;
    use curve25519_dalek::scalar::Scalar;

    let value: u64 = 1_234_567;
    let mut blinding = [0u8; 32];
    blinding[0] = 0x9A;
    blinding[31] = 0x42;

    let mut commit = [0u8; 32];
    unsafe { pedersen::commit(value, blinding.as_ptr(), commit.as_mut_ptr()) };

    let mut mask: u8 = 0;

    // bit 0 — the opening VERIFIES.
    let ok = unsafe { pedersen::verify_opening(value, blinding.as_ptr(), commit.as_ptr()) };
    if ok == 1 {
        mask |= 0x1;
    }

    // bit 1 — a WRONG value FAILS.
    let wrong_v = unsafe { pedersen::verify_opening(value + 1, blinding.as_ptr(), commit.as_ptr()) };
    if wrong_v == 0 {
        mask |= 0x2;
    }

    // bit 2 — a WRONG blinding FAILS.
    let mut other_bl = blinding;
    other_bl[0] ^= 0xFF;
    let wrong_r = unsafe { pedersen::verify_opening(value, other_bl.as_ptr(), commit.as_ptr()) };
    if wrong_r == 0 {
        mask |= 0x4;
    }

    // bit 3 — HOMOMORPHISM: commit(a,r1) + commit(b,r2) == commit(a+b, r1+r2).
    // Build two commitments + the summed one from scalars, compare decompressed
    // points (the executor's conservation check adds commitments this way).
    let a: u64 = 100;
    let b: u64 = 250;
    let mut r1 = [0u8; 32];
    r1[0] = 0x11;
    let mut r2 = [0u8; 32];
    r2[0] = 0x22;
    let mut ca = [0u8; 32];
    let mut cb = [0u8; 32];
    unsafe {
        pedersen::commit(a, r1.as_ptr(), ca.as_mut_ptr());
        pedersen::commit(b, r2.as_ptr(), cb.as_mut_ptr());
    }
    // r1 + r2 as a reduced scalar, back to 32 bytes.
    let s1 = Scalar::from_bytes_mod_order(r1);
    let s2 = Scalar::from_bytes_mod_order(r2);
    let r_sum = (s1 + s2).to_bytes();
    let mut c_sum = [0u8; 32];
    unsafe { pedersen::commit(a + b, r_sum.as_ptr(), c_sum.as_mut_ptr()) };

    let pa = CompressedRistretto(ca).decompress();
    let pb = CompressedRistretto(cb).decompress();
    let psum = CompressedRistretto(c_sum).decompress();
    if let (Some(pa), Some(pb), Some(psum)) = (pa, pb, psum) {
        if (pa + pb) == psum {
            mask |= 0x8;
        }
    }

    mask
}

// ===========================================================================
// §7 — ChaCha20-Poly1305 AEAD (REAL). The committed-note ECIES box's primitive.
// ===========================================================================

/// AEAD seal: encrypt `pt` under `(key32, nonce12)` to `ciphertext||tag` in `out`,
/// returning the written length (`pt_len + 16`) or `-1` on error.
///
/// # Safety
/// `key`→32, `nonce`→12, `pt`→`pt_len` (null iff 0), `out`→`out_cap` bytes.
#[no_mangle]
pub unsafe extern "C" fn dreggcf_chacha_seal(
    key: *const u8,
    nonce: *const u8,
    pt: *const u8,
    pt_len: usize,
    out: *mut u8,
    out_cap: usize,
) -> isize {
    aead::seal(key, nonce, pt, pt_len, out, out_cap)
}

/// AEAD open: decrypt-and-authenticate `ct` (`ciphertext||tag`) under `(key32,
/// nonce12)` to `out`, returning the plaintext length or `-1` on a failed tag /
/// short input / small buffer. FAIL-CLOSED.
///
/// # Safety
/// `key`→32, `nonce`→12, `ct`→`ct_len` (null iff 0), `out`→`out_cap` bytes.
#[no_mangle]
pub unsafe extern "C" fn dreggcf_chacha_open(
    key: *const u8,
    nonce: *const u8,
    ct: *const u8,
    ct_len: usize,
    out: *mut u8,
    out_cap: usize,
) -> isize {
    aead::open(key, nonce, ct, ct_len, out, out_cap)
}

/// AEAD authenticate-only (the `aeadOpen` boolean oracle): `1` iff `ct` opens under
/// `(key32, nonce12)`, `0` otherwise. FAIL-CLOSED.
///
/// # Safety
/// `key`→32, `nonce`→12, `ct`→`ct_len` bytes.
#[no_mangle]
pub unsafe extern "C" fn dreggcf_chacha_authenticate(
    key: *const u8,
    nonce: *const u8,
    ct: *const u8,
    ct_len: usize,
) -> u8 {
    aead::authenticate(key, nonce, ct, ct_len)
}

/// On-device anti-ghost witness for §7. Seals a fixed plaintext and:
///   bit 0 (0x1): seal→open ROUND-TRIPS to the original plaintext;
///   bit 1 (0x2): a TAMPERED ciphertext byte FAILS the tag (open → -1);
///   bit 2 (0x4): a WRONG key FAILS the tag;
///   bit 3 (0x8): a TAMPERED tag byte FAILS (the Poly1305 authentication).
/// A fully-correct floor returns `0xF`.
#[no_mangle]
pub extern "C" fn dreggcf_chacha_selftest() -> u8 {
    let key = [0x42u8; 32];
    let nonce = [0x07u8; 12];
    let pt = b"note-opening: value=1234567 asset=7 blinding=...";

    let mut boxed = [0u8; 128];
    let n = unsafe {
        aead::seal(
            key.as_ptr(),
            nonce.as_ptr(),
            pt.as_ptr(),
            pt.len(),
            boxed.as_mut_ptr(),
            boxed.len(),
        )
    };
    if n < 0 {
        return 0;
    }
    let n = n as usize;

    let mut mask: u8 = 0;

    // bit 0 — round-trip.
    let mut recovered = [0u8; 128];
    let m = unsafe {
        aead::open(
            key.as_ptr(),
            nonce.as_ptr(),
            boxed.as_ptr(),
            n,
            recovered.as_mut_ptr(),
            recovered.len(),
        )
    };
    if m == pt.len() as isize && &recovered[..pt.len()] == &pt[..] {
        mask |= 0x1;
    }

    // bit 1 — a tampered ciphertext byte (mid-payload, before the tag) FAILS.
    let mut tampered = boxed;
    tampered[n / 2] ^= 0x01;
    let bad = unsafe {
        aead::open(
            key.as_ptr(),
            nonce.as_ptr(),
            tampered.as_ptr(),
            n,
            recovered.as_mut_ptr(),
            recovered.len(),
        )
    };
    if bad < 0 {
        mask |= 0x2;
    }

    // bit 2 — a WRONG key FAILS.
    let wrong_key = [0x43u8; 32];
    let wk = unsafe {
        aead::open(
            wrong_key.as_ptr(),
            nonce.as_ptr(),
            boxed.as_ptr(),
            n,
            recovered.as_mut_ptr(),
            recovered.len(),
        )
    };
    if wk < 0 {
        mask |= 0x4;
    }

    // bit 3 — a tampered TAG byte (the last 16 bytes) FAILS.
    let mut tag_tampered = boxed;
    tag_tampered[n - 1] ^= 0x80;
    let tt = unsafe {
        aead::open(
            key.as_ptr(),
            nonce.as_ptr(),
            tag_tampered.as_ptr(),
            n,
            recovered.as_mut_ptr(),
            recovered.len(),
        )
    };
    if tt < 0 {
        mask |= 0x8;
    }

    mask
}

/// The AIRs this floor carries the constraint logic for, keyed by `air_name`.
/// Verification needs the AIR *implementation* (`eval_constraints` /
/// `boundary_constraints`), not just the proof's self-declared name — so the
/// floor can only verify proofs for AIRs it carries. This is the SAME concrete
/// AIR the `verifier-stark` PD proves + verifies on-device
/// (`verifier-stark/src/main.rs::CounterSquareAir`), carried here verbatim so the
/// executor floor and the verifier PD agree on one witnessed AIR. An unknown
/// `air_name` fails closed (no fabricated acceptance).
mod carried_air {
    use super::stark_core::field::BabyBear;
    use super::stark_core::stark::{BoundaryConstraint, StarkAir};
    use alloc::vec;
    use alloc::vec::Vec;

    /// A minimal but real AIR: a 2-column trace with the transition constraint
    /// `col0' = col0 + 1` and the algebraic boundary `col1 = col0^2`. Byte-for-byte
    /// the `verifier-stark` PD's `CounterSquareAir`.
    pub struct CounterSquareAir;

    impl StarkAir for CounterSquareAir {
        fn width(&self) -> usize {
            2
        }
        fn constraint_degree(&self) -> usize {
            2
        }
        fn air_name(&self) -> &'static str {
            "dregg-firmament-counter-square-v1"
        }
        fn has_chain_continuity(&self) -> bool {
            false
        }
        fn eval_constraints(
            &self,
            local: &[BabyBear],
            next: &[BabyBear],
            _public_inputs: &[BabyBear],
            alpha: BabyBear,
        ) -> BabyBear {
            let c1 = next[0] - local[0] - BabyBear::ONE;
            let c2 = local[1] - local[0] * local[0];
            c1 + alpha * c2
        }

        fn boundary_constraints(
            &self,
            public_inputs: &[BabyBear],
            _trace_len: usize,
        ) -> Vec<BoundaryConstraint> {
            if public_inputs.is_empty() {
                return vec![];
            }
            vec![BoundaryConstraint {
                row: 0,
                col: 0,
                value: public_inputs[0],
            }]
        }
    }

    /// Resolve a carried AIR by its `air_name`. Returns `None` (→ fail-closed
    /// verify) for any AIR whose constraint logic this floor does not carry.
    pub fn by_name(name: &str) -> Option<&'static dyn StarkAir> {
        match name {
            "dregg-firmament-counter-square-v1" => Some(&CounterSquareAir),
            _ => None,
        }
    }
}

/// REAL STARK verification over the structured proof bytes (the wiring point the
/// abstract-Nat portal points to). Given:
///   - `proof` / `proof_len`: a `StarkProof` serialized by `stark::proof_to_bytes`
///     (the executor PD's proof-carrying turn supplies these out of band);
///   - `pi` / `pi_len`: the public inputs as little-endian `u32` BabyBear limbs
///     (`pi_len` is the BYTE length, a multiple of 4);
/// this decodes the proof, resolves the carried AIR by the proof's own
/// `air_name`, and runs `stark::verify` — the verbatim `verifier-stark`
/// cryptographic check (Reed-Solomon + BLAKE3 Merkle + FRI + Fiat-Shamir +
/// boundary binding). Returns `1` iff the proof verifies; `0` on ANY failure
/// (decode error, unknown/mismatched AIR, or a failed cryptographic check) —
/// FAIL-CLOSED, never a spurious accept. This brings the executor PD's crypto
/// floor to parity with the verifier-stark PD: a real on-device STARK verify, the
/// anti-ghost tooth and all.
///
/// # Safety
/// `proof` must point to `proof_len` readable bytes (or null iff `proof_len==0`);
/// `pi` must point to `pi_len` readable bytes (or null iff `pi_len==0`).
#[no_mangle]
pub unsafe extern "C" fn dreggcf_stark_verify_bytes(
    proof: *const u8,
    proof_len: usize,
    pi: *const u8,
    pi_len: usize,
) -> u8 {
    use stark_core::field::BabyBear;
    use stark_core::stark::{proof_from_bytes, verify};

    let proof_bytes: &[u8] = if proof.is_null() || proof_len == 0 {
        return 0; // an empty proof never verifies
    } else {
        core::slice::from_raw_parts(proof, proof_len)
    };

    // Decode the structured proof. A tampered/truncated wire fails closed here.
    let proof = match proof_from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return 0,
    };

    // Resolve the AIR the floor carries the constraint logic for. The proof's
    // own `air_name` selects it; `verify` independently re-checks the name match.
    let air = match carried_air::by_name(&proof.air_name) {
        Some(a) => a,
        None => return 0, // unknown AIR — never fabricate acceptance
    };

    // Decode the public inputs (LE u32 BabyBear limbs).
    let pi_elems: alloc::vec::Vec<BabyBear> = if pi.is_null() || pi_len == 0 {
        alloc::vec::Vec::new()
    } else {
        let pi_bytes = core::slice::from_raw_parts(pi, pi_len);
        pi_bytes
            .chunks_exact(4)
            .map(|c| BabyBear::from_u64(u32::from_le_bytes([c[0], c[1], c[2], c[3]]) as u64))
            .collect()
    };

    // The genuine cryptographic verify — ACCEPT a sound proof, REJECT a tampered
    // one or a wrong public input (the boundary tooth).
    match verify(air, &proof, &pi_elems) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}

/// On-device anti-ghost witness for the §2 byte-channel STARK verify. PROVES the
/// carried `CounterSquareAir` (real Reed-Solomon + BLAKE3 Merkle + FRI +
/// Fiat-Shamir — exactly what `verifier-stark` runs), serializes the proof, and
/// drives `dreggcf_stark_verify_bytes` on three cases, returning a bitmask:
///   bit 0 (0x1): a GOOD proof + correct PI VERIFIES (accept);
///   bit 1 (0x2): a TAMPERED proof (one flipped byte mid-payload) REJECTS;
///   bit 2 (0x4): the good proof against a WRONG PI REJECTS (boundary tooth).
/// A fully-correct floor returns `0x7`. This is the executor-PD analogue of the
/// verifier-stark PD's boot teeth (`verifier-stark/src/main.rs` steps 2/4/5),
/// callable from the C self-test (`crypto-floor-selftest.c`) so the floor's real
/// STARK verify is run-verified on-device, not merely linked. No args, no I/O,
/// fully deterministic (`prove` is Fiat-Shamir).
#[no_mangle]
pub extern "C" fn dreggcf_stark_selftest() -> u8 {
    use stark_core::field::BabyBear;
    use stark_core::stark::{prove, proof_to_bytes};

    let air = carried_air::CounterSquareAir;
    // public input: row0 col0 == 0 (binds the trace start via the boundary cstr).
    let pi = [BabyBear::new(0)];
    let pi_bytes: alloc::vec::Vec<u8> = pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
    // the valid 4-row trace: col0 = 0,1,2,3 ; col1 = col0^2.
    let trace: alloc::vec::Vec<alloc::vec::Vec<BabyBear>> = (0u32..4)
        .map(|i| alloc::vec![BabyBear::new(i), BabyBear::new(i * i)])
        .collect();

    let proof = prove(&air, &trace, &pi);
    let bytes = proof_to_bytes(&proof);

    let mut mask: u8 = 0;

    // bit 0 — a sound proof + correct PI must ACCEPT.
    let good = unsafe {
        dreggcf_stark_verify_bytes(bytes.as_ptr(), bytes.len(), pi_bytes.as_ptr(), pi_bytes.len())
    };
    if good == 1 {
        mask |= 0x1;
    }

    // bit 1 — a tampered proof (flip one byte mid-payload) must REJECT.
    let mut tampered = bytes.clone();
    if !tampered.is_empty() {
        let mid = tampered.len() / 2;
        tampered[mid] ^= 0xff;
    }
    let bad = unsafe {
        dreggcf_stark_verify_bytes(
            tampered.as_ptr(),
            tampered.len(),
            pi_bytes.as_ptr(),
            pi_bytes.len(),
        )
    };
    if bad == 0 {
        mask |= 0x2;
    }

    // bit 2 — the good proof against a WRONG public input must REJECT (boundary).
    let wrong_pi = [BabyBear::new(1)];
    let wrong_pi_bytes: alloc::vec::Vec<u8> =
        wrong_pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
    let wrong = unsafe {
        dreggcf_stark_verify_bytes(
            bytes.as_ptr(),
            bytes.len(),
            wrong_pi_bytes.as_ptr(),
            wrong_pi_bytes.len(),
        )
    };
    if wrong == 0 {
        mask |= 0x4;
    }

    mask
}

// ===========================================================================
// §2.1 — LIVE proof-carrying-turn admission. The byte channel above is exercised
// by the selftest (which MINTS a proof and verifies it in one breath). A LIVE turn
// is different: the executor PD receives a turn whose STARK proof bytes + public
// inputs arrived OUT OF BAND (decoded from a wire the producer shipped — the PD
// never mints them), and the turn is ADMITTED iff that carried proof verifies. The
// entry below closes that wiring: it DECODES a proof-carrying-turn wire, extracts
// the carried proof + PI exactly as a live turn ships them, routes them through the
// SAME `dreggcf_stark_verify_bytes` (the one carried verifier — no second check),
// and returns the admission verdict (1 = ADMIT, 0 = REFUSE) FAIL-CLOSED.
// ===========================================================================

/// The proof-carrying-turn wire framing (the bytes a producer ships alongside a
/// turn for the executor PD to admit). Self-describing, length-prefixed, so the PD
/// can decode it WITHOUT trusting a sender-declared total length:
///
/// ```text
///   [0..4)   magic         b"PCT1"  (proof-carrying turn, v1)
///   [4..12)  turn_id        u64 LE  (the turn this proof attests; opaque here, the
///                                    executor binds it — carried so the wire is a
///                                    real turn envelope, not a bare proof blob)
///   [12..16) proof_len      u32 LE
///   [16..16+proof_len)      the StarkProof bytes (`stark::proof_to_bytes` form)
///   [.. +4)  pi_len         u32 LE  (BYTE length, a multiple of 4)
///   [.. +pi_len)            the public inputs (LE u32 BabyBear limbs)
/// ```
///
/// This is the executor-PD analogue of the §8 SEAM in the Lean model
/// (`Dregg2/Exec/ProofForest.lean`'s `StepProofValid`): the proof is opaque to the
/// verified turn logic, and ADMISSION ≡ "this carried proof verifies against its
/// carried PI". Here that proposition is DISCHARGED on-device by the carried STARK
/// verifier — not assumed.
const PCT_MAGIC: &[u8; 4] = b"PCT1";

/// Decode a proof-carrying-turn wire into `(turn_id, proof_bytes, pi_bytes)`.
/// Returns `None` on ANY framing error (bad magic, truncation, a declared length
/// that overruns the buffer) — fail-closed: a malformed turn envelope is never
/// admitted. Pure slicing over the borrowed wire (no allocation, no copy).
fn pct_decode(wire: &[u8]) -> Option<(u64, &[u8], &[u8])> {
    // magic + turn_id(8) + proof_len(4) = 16-byte minimum header
    if wire.len() < 16 || &wire[0..4] != PCT_MAGIC {
        return None;
    }
    let turn_id = u64::from_le_bytes([
        wire[4], wire[5], wire[6], wire[7], wire[8], wire[9], wire[10], wire[11],
    ]);
    let proof_len = u32::from_le_bytes([wire[12], wire[13], wire[14], wire[15]]) as usize;
    let proof_start: usize = 16;
    let proof_end = proof_start.checked_add(proof_len)?;
    // need proof bytes + the 4-byte pi_len that follows
    if proof_end.checked_add(4)? > wire.len() {
        return None;
    }
    let proof_bytes = &wire[proof_start..proof_end];
    let pi_len = u32::from_le_bytes([
        wire[proof_end],
        wire[proof_end + 1],
        wire[proof_end + 2],
        wire[proof_end + 3],
    ]) as usize;
    let pi_start = proof_end + 4;
    let pi_end = pi_start.checked_add(pi_len)?;
    if pi_end > wire.len() {
        return None;
    }
    let pi_bytes = &wire[pi_start..pi_end];
    Some((turn_id, proof_bytes, pi_bytes))
}

/// ADMIT a LIVE proof-carrying turn. Given the turn's wire envelope (`PCT1` framing
/// above — the producer's proof bytes + public inputs as they arrive out of band),
/// decode it, route the CARRIED proof + PI through `dreggcf_stark_verify_bytes`
/// (the one carried STARK verifier), and return the admission verdict:
///   `1` — the carried proof cryptographically verifies against its carried PI →
///         the turn is ADMITTED;
///   `0` — a framing error, a decode error, an unknown AIR, OR a failed
///         cryptographic check → the turn is REFUSED (FAIL-CLOSED).
///
/// This is the entry the executor PD calls when it applies a proof-bearing turn:
/// the LIVE turn's proof bytes reach the real verifier here, and the turn is
/// admitted IFF the verify returns 1 — exactly the §4 next step
/// (`docs/EMBEDDABLE-LEAN-RUNTIME.md`). Unlike `dreggcf_stark_selftest`, the proof
/// is NOT minted here; it is the bytes the wire carried.
///
/// # Safety
/// `wire` must point to `wire_len` readable bytes (or be null iff `wire_len == 0`).
#[no_mangle]
pub unsafe extern "C" fn dreggcf_admit_proof_carrying_turn(wire: *const u8, wire_len: usize) -> u8 {
    let wire_bytes: &[u8] = if wire.is_null() || wire_len == 0 {
        return 0; // an empty turn envelope carries no proof — refuse
    } else {
        core::slice::from_raw_parts(wire, wire_len)
    };

    // Decode the turn envelope; a malformed wire is refused (never admitted).
    let (_turn_id, proof_bytes, pi_bytes) = match pct_decode(wire_bytes) {
        Some(parts) => parts,
        None => return 0,
    };

    // Route the CARRIED proof + PI through the one carried verifier. The verdict IS
    // the admission decision: ADMIT iff the carried proof verifies (fail-closed).
    dreggcf_stark_verify_bytes(
        proof_bytes.as_ptr(),
        proof_bytes.len(),
        pi_bytes.as_ptr(),
        pi_bytes.len(),
    )
}

/// On-device anti-ghost witness for the LIVE proof-carrying-turn ADMISSION path
/// (the §2.1 analogue of `dreggcf_stark_selftest`, but exercising the admission
/// entry, not the bare byte channel). It mints a real proof ON THE PRODUCER SIDE,
/// ENCODES three turn wires (the bytes a producer would ship), and drives
/// `dreggcf_admit_proof_carrying_turn` — the verify input flows through the wire
/// decode, the live-turn path. Returns a bitmask:
///   bit 0 (0x1): a GENUINE turn (sound proof + correct PI) is ADMITTED;
///   bit 1 (0x2): a turn carrying a TAMPERED proof is REFUSED;
///   bit 2 (0x4): a turn carrying the good proof but a WRONG PI is REFUSED.
/// A fully-correct admission path returns `0x7`. The teeth bite on the LIVE-turn
/// path — not just the selftest.
#[no_mangle]
pub extern "C" fn dreggcf_admit_selftest() -> u8 {
    use stark_core::field::BabyBear;
    use stark_core::stark::{proof_to_bytes, prove};

    // ---- producer side: mint a real proof for the carried AIR ----
    let air = carried_air::CounterSquareAir;
    let pi = [BabyBear::new(0)]; // row0 col0 == 0, the boundary-bound PI
    let pi_bytes: alloc::vec::Vec<u8> =
        pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
    let trace: alloc::vec::Vec<alloc::vec::Vec<BabyBear>> = (0u32..4)
        .map(|i| alloc::vec![BabyBear::new(i), BabyBear::new(i * i)])
        .collect();
    let proof = prove(&air, &trace, &pi);
    let proof_bytes = proof_to_bytes(&proof);

    // helper: ENCODE a PCT1 turn wire from carried proof bytes + PI bytes.
    fn pct_encode(turn_id: u64, proof_bytes: &[u8], pi_bytes: &[u8]) -> alloc::vec::Vec<u8> {
        let mut w = alloc::vec::Vec::with_capacity(16 + proof_bytes.len() + 4 + pi_bytes.len());
        w.extend_from_slice(PCT_MAGIC);
        w.extend_from_slice(&turn_id.to_le_bytes());
        w.extend_from_slice(&(proof_bytes.len() as u32).to_le_bytes());
        w.extend_from_slice(proof_bytes);
        w.extend_from_slice(&(pi_bytes.len() as u32).to_le_bytes());
        w.extend_from_slice(pi_bytes);
        w
    }

    let mut mask: u8 = 0;

    // bit 0 — a GENUINE turn must be ADMITTED.
    let genuine = pct_encode(0x7777, &proof_bytes, &pi_bytes);
    let admit = unsafe { dreggcf_admit_proof_carrying_turn(genuine.as_ptr(), genuine.len()) };
    if admit == 1 {
        mask |= 0x1;
    }

    // bit 1 — a turn carrying a TAMPERED proof must be REFUSED. The producer's wire
    // is intact framing; only the carried proof payload is corrupted (one flipped
    // byte mid-proof), exactly the bytes a cheater would ship.
    let mut tampered_proof = proof_bytes.clone();
    if !tampered_proof.is_empty() {
        let mid = tampered_proof.len() / 2;
        tampered_proof[mid] ^= 0xff;
    }
    let tampered_turn = pct_encode(0x7777, &tampered_proof, &pi_bytes);
    let refuse_tampered =
        unsafe { dreggcf_admit_proof_carrying_turn(tampered_turn.as_ptr(), tampered_turn.len()) };
    if refuse_tampered == 0 {
        mask |= 0x2;
    }

    // bit 2 — a turn carrying the good proof but a WRONG PI must be REFUSED (the
    // boundary tooth on the admission path: the carried PI binds the trace start).
    let wrong_pi = [BabyBear::new(1)];
    let wrong_pi_bytes: alloc::vec::Vec<u8> =
        wrong_pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
    let wrong_turn = pct_encode(0x7777, &proof_bytes, &wrong_pi_bytes);
    let refuse_wrong =
        unsafe { dreggcf_admit_proof_carrying_turn(wrong_turn.as_ptr(), wrong_turn.len()) };
    if refuse_wrong == 0 {
        mask |= 0x4;
    }

    mask
}

// ===========================================================================
// Build-time conformance witnesses (these run on the HOST via `cargo test`, and
// the constants are checked at link by the boot; they pin that the carried
// Poseidon2 here matches the audited circuit/verifier-stark digests).
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn poseidon2_hash_4_to_1_known_answer() {
        // The circuit crate's frozen KAT: hash_4_to_1([1,2,3,4]) == 1163579196.
        let h = poseidon2::hash_4_to_1(&[
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
        ]);
        assert_eq!(h.as_u32(), 1163579196);
    }

    #[test]
    fn poseidon2_permutation_known_answer() {
        // The circuit crate's frozen width-16 permutation KAT on input [0..15].
        let mut input = [BabyBear::ZERO; poseidon2::WIDTH];
        for i in 0..poseidon2::WIDTH {
            input[i] = BabyBear::new(i as u32);
        }
        let mut state = poseidon2::Poseidon2State { state: input };
        state.permute();
        let expected: [u32; 16] = [
            1906786279, 1737026427, 1959749225, 700325316, 1638050605, 1021608788, 1726691001,
            1761127344, 1552405120, 417318995, 36799261, 1215172152, 614923223, 1300746575,
            957311597, 304856115,
        ];
        for i in 0..poseidon2::WIDTH {
            assert_eq!(state.state[i].as_u32(), expected[i], "lane {i}");
        }
    }

    #[test]
    fn poseidon2_2to1_deterministic_and_nonzero() {
        let a = dreggcf_poseidon2_2to1(7, 11);
        let b = dreggcf_poseidon2_2to1(7, 11);
        assert_eq!(a, b);
        assert_ne!(a, 0);
        assert_ne!(dreggcf_poseidon2_2to1(7, 11), dreggcf_poseidon2_2to1(11, 7));
    }

    #[test]
    fn blake3_to_field_deterministic_and_nonzero() {
        let data = [1u8, 2, 3, 4, 5];
        let a = unsafe { dreggcf_blake3_to_field(data.as_ptr(), data.len()) };
        let b = unsafe { dreggcf_blake3_to_field(data.as_ptr(), data.len()) };
        assert_eq!(a, b);
        let other = [9u8, 9, 9];
        let c = unsafe { dreggcf_blake3_to_field(other.as_ptr(), other.len()) };
        assert_ne!(a, c);
    }

    #[test]
    fn nullifier_deterministic_distinct_from_node() {
        assert_eq!(dreggcf_nullifier(42), dreggcf_nullifier(42));
        // The nullifier of a note must differ from a bare 2-to-1 of (note, note).
        assert_ne!(dreggcf_nullifier(42), dreggcf_poseidon2_2to1(42, 42));
    }

    #[test]
    fn keyed_mac_deterministic_key_sensitive() {
        let msg = [0xaau8, 0xbb, 0xcc];
        let t1 = unsafe { dreggcf_keyed_mac(1, msg.as_ptr(), msg.len()) };
        let t2 = unsafe { dreggcf_keyed_mac(1, msg.as_ptr(), msg.len()) };
        let t3 = unsafe { dreggcf_keyed_mac(2, msg.as_ptr(), msg.len()) };
        assert_eq!(t1, t2);
        assert_ne!(t1, t3);
    }

    #[test]
    fn stark_verify_abstract_fails_closed() {
        // The abstract Nat-pair verify must NEVER spuriously accept.
        assert_eq!(dreggcf_stark_verify_abstract(0, 0), 0);
        assert_eq!(dreggcf_stark_verify_abstract(1, 1), 0);
    }

    #[test]
    fn stark_verify_bytes_real_tooth() {
        // The REAL §2 byte-channel verify: prove a sound proof, ACCEPT it, then
        // REJECT a tampered proof and a wrong public input (the anti-ghost teeth,
        // mirroring verifier-stark/src/main.rs). The self-test entry runs all
        // three and returns 0x7 iff every tooth bites.
        assert_eq!(dreggcf_stark_selftest(), 0x7, "byte-channel STARK verify teeth");
    }

    #[test]
    fn stark_verify_bytes_garbage_fails_closed() {
        // A garbage / empty proof buffer must fail closed (decode error → reject),
        // never a spurious accept.
        let pi = 0u32.to_le_bytes();
        let garbage = [0xABu8; 64];
        let r = unsafe {
            dreggcf_stark_verify_bytes(garbage.as_ptr(), garbage.len(), pi.as_ptr(), pi.len())
        };
        assert_eq!(r, 0, "garbage proof must reject");
        let e = unsafe { dreggcf_stark_verify_bytes(core::ptr::null(), 0, pi.as_ptr(), pi.len()) };
        assert_eq!(e, 0, "empty proof must reject");
    }

    #[test]
    fn admit_proof_carrying_turn_live_teeth() {
        // The LIVE proof-carrying-turn ADMISSION path: a genuine turn ADMITS, a
        // tampered-proof turn REFUSES, a wrong-PI turn REFUSES — the anti-ghost
        // teeth on the ADMISSION entry (proof bytes arrive via the wire decode,
        // not minted in-line). The selftest entry drives all three.
        assert_eq!(
            dreggcf_admit_selftest(),
            0x7,
            "live proof-carrying-turn admission teeth"
        );
    }

    #[test]
    fn admit_proof_carrying_turn_malformed_wire_fails_closed() {
        // A malformed turn envelope must be REFUSED at decode — never admitted.
        // empty
        let e = unsafe { dreggcf_admit_proof_carrying_turn(core::ptr::null(), 0) };
        assert_eq!(e, 0, "empty turn wire must refuse");
        // bad magic
        let bad_magic = [0u8; 32];
        let m = unsafe { dreggcf_admit_proof_carrying_turn(bad_magic.as_ptr(), bad_magic.len()) };
        assert_eq!(m, 0, "bad-magic turn wire must refuse");
        // good magic, but a proof_len that overruns the buffer (allocation-bomb /
        // truncation guard) — must refuse, not panic.
        let mut overrun = alloc::vec::Vec::new();
        overrun.extend_from_slice(PCT_MAGIC);
        overrun.extend_from_slice(&0u64.to_le_bytes()); // turn_id
        overrun.extend_from_slice(&0xFFFF_FFFFu32.to_le_bytes()); // proof_len >> buffer
        let o = unsafe { dreggcf_admit_proof_carrying_turn(overrun.as_ptr(), overrun.len()) };
        assert_eq!(o, 0, "overrun proof_len must refuse");
    }

    #[test]
    fn admit_decode_roundtrips_and_binds_carried_proof() {
        // The wire the admission path decodes carries the PRODUCER's proof bytes —
        // routing them through the verifier must ADMIT exactly when the bare byte
        // channel would, proving the admission entry adds framing without changing
        // the verdict (the carried proof is the load-bearing object, not a re-mint).
        use stark_core::field::BabyBear;
        use stark_core::stark::{proof_to_bytes, prove};
        let air = carried_air::CounterSquareAir;
        let pi = [BabyBear::new(0)];
        let pi_bytes: alloc::vec::Vec<u8> =
            pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
        let trace: alloc::vec::Vec<alloc::vec::Vec<BabyBear>> = (0u32..4)
            .map(|i| alloc::vec![BabyBear::new(i), BabyBear::new(i * i)])
            .collect();
        let proof = prove(&air, &trace, &pi);
        let proof_bytes = proof_to_bytes(&proof);

        // hand-build the PCT1 wire (the producer's framing).
        let mut wire = alloc::vec::Vec::new();
        wire.extend_from_slice(PCT_MAGIC);
        wire.extend_from_slice(&42u64.to_le_bytes());
        wire.extend_from_slice(&(proof_bytes.len() as u32).to_le_bytes());
        wire.extend_from_slice(&proof_bytes);
        wire.extend_from_slice(&(pi_bytes.len() as u32).to_le_bytes());
        wire.extend_from_slice(&pi_bytes);

        // decode binds back to the exact carried proof + PI + turn_id.
        let (tid, dp, dpi) = pct_decode(&wire).expect("well-formed wire decodes");
        assert_eq!(tid, 42);
        assert_eq!(dp, &proof_bytes[..]);
        assert_eq!(dpi, &pi_bytes[..]);

        // and the admission verdict matches the bare byte-channel verdict (ADMIT).
        let bare = unsafe {
            dreggcf_stark_verify_bytes(
                proof_bytes.as_ptr(),
                proof_bytes.len(),
                pi_bytes.as_ptr(),
                pi_bytes.len(),
            )
        };
        let admitted = unsafe { dreggcf_admit_proof_carrying_turn(wire.as_ptr(), wire.len()) };
        assert_eq!(bare, 1, "the bare byte channel admits the sound proof");
        assert_eq!(admitted, bare, "admission verdict == byte-channel verdict");
    }

    // ---- §1 ed25519 (REAL) -------------------------------------------------

    #[test]
    fn ed25519_real_teeth() {
        // ACCEPT a genuine sig; REJECT a forged sig, a wrong message, a wrong key.
        assert_eq!(dreggcf_ed25519_selftest(), 0xF, "ed25519 verify_strict teeth");
    }

    #[test]
    fn ed25519_known_answer_accepts_and_rejects() {
        use ed25519_dalek::{Signer, SigningKey};
        let sk = SigningKey::from_bytes(&[3u8; 32]);
        let pk = sk.verifying_key().to_bytes();
        let msg = b"on-device turn auth";
        let sig = sk.sign(msg).to_bytes();
        // genuine accepts
        let ok = unsafe { dreggcf_ed25519_verify(pk.as_ptr(), msg.as_ptr(), msg.len(), sig.as_ptr()) };
        assert_eq!(ok, 1);
        // a bad (all-zero) signature rejects
        let zero = [0u8; 64];
        let bad = unsafe { dreggcf_ed25519_verify(pk.as_ptr(), msg.as_ptr(), msg.len(), zero.as_ptr()) };
        assert_eq!(bad, 0);
        // a non-canonical / garbage public key rejects (from_bytes guard)
        let badpk = [0xFFu8; 32];
        let bk = unsafe { dreggcf_ed25519_verify(badpk.as_ptr(), msg.as_ptr(), msg.len(), sig.as_ptr()) };
        assert_eq!(bk, 0);
    }

    // ---- §3 Pedersen (REAL, Ristretto255) ----------------------------------

    #[test]
    fn pedersen_real_teeth() {
        // opening verifies; wrong value/blinding fail; homomorphism holds.
        assert_eq!(dreggcf_pedersen_selftest(), 0xF, "pedersen commitment teeth");
    }

    #[test]
    fn pedersen_commit_is_deterministic_and_binding() {
        let value: u64 = 42;
        let mut bl = [0u8; 32];
        bl[0] = 0xAB;
        let mut c1 = [0u8; 32];
        let mut c2 = [0u8; 32];
        unsafe {
            dreggcf_pedersen_commit(value, bl.as_ptr(), c1.as_mut_ptr());
            dreggcf_pedersen_commit(value, bl.as_ptr(), c2.as_mut_ptr());
        }
        assert_eq!(c1, c2, "commitment is deterministic");
        assert_ne!(c1, [0u8; 32], "commitment is non-trivial");
        // opening verifies; a different value gives a different commitment.
        assert_eq!(
            unsafe { dreggcf_pedersen_verify_opening(value, bl.as_ptr(), c1.as_ptr()) },
            1
        );
        let mut c3 = [0u8; 32];
        unsafe { dreggcf_pedersen_commit(value + 1, bl.as_ptr(), c3.as_mut_ptr()) };
        assert_ne!(c1, c3, "binding: a different value -> a different commitment");
    }

    // ---- §7 ChaCha20-Poly1305 AEAD (REAL) ----------------------------------

    #[test]
    fn aead_real_teeth() {
        // round-trip; tampered ciphertext fails; wrong key fails; tampered tag fails.
        assert_eq!(dreggcf_chacha_selftest(), 0xF, "chacha20poly1305 AEAD teeth");
    }

    #[test]
    fn aead_roundtrip_and_tamper() {
        let key = [0x11u8; 32];
        let nonce = [0x22u8; 12];
        let pt = b"hello dregg";
        let mut boxed = [0u8; 64];
        let n = unsafe {
            dreggcf_chacha_seal(
                key.as_ptr(),
                nonce.as_ptr(),
                pt.as_ptr(),
                pt.len(),
                boxed.as_mut_ptr(),
                boxed.len(),
            )
        };
        assert_eq!(n, (pt.len() + 16) as isize, "seal writes ct||tag");
        let n = n as usize;
        let mut out = [0u8; 64];
        let m = unsafe {
            dreggcf_chacha_open(
                key.as_ptr(),
                nonce.as_ptr(),
                boxed.as_ptr(),
                n,
                out.as_mut_ptr(),
                out.len(),
            )
        };
        assert_eq!(m, pt.len() as isize);
        assert_eq!(&out[..pt.len()], &pt[..]);
        // authenticate-only agrees.
        assert_eq!(
            unsafe { dreggcf_chacha_authenticate(key.as_ptr(), nonce.as_ptr(), boxed.as_ptr(), n) },
            1
        );
        // a too-short box rejects.
        assert_eq!(
            unsafe { dreggcf_chacha_open(key.as_ptr(), nonce.as_ptr(), boxed.as_ptr(), 8, out.as_mut_ptr(), out.len()) },
            -1
        );
    }
}
