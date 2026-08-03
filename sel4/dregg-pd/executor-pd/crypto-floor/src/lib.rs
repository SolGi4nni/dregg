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
//! `dreggcf_stark_verify_abstract`) — an abstract Nat pair carries no checkable
//! proof, so it returns reject.

// `no_std` for the load-bearing cross artifact (a `staticlib` for the seL4-musl
// PD). `alloc` is the single allocation crate; the sub-modules reference `alloc::`
// against THIS one root declaration (no per-module `extern crate alloc;`). The
// `#[cfg(test)]` module mirrors the teeth as Rust assertions; note a
// `staticlib`-only `no_std` crate with alloc-heavy no_std deps cannot host a std
// `cargo test` harness (the `--test` build double-links `core`/`alloc`) — this is
// a pre-existing crate limitation, hence the C selftest is the executed witness.
#![cfg_attr(not(test), no_std)]
#![allow(clippy::missing_safety_doc)]

extern crate alloc;

pub mod field;
pub mod poseidon2;

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
/// single field element.
///
/// # ⚑ CLASS (A), NAMED NOT MIGRATED — and the old justification here was WRONG
///
/// Classified 2026-08-01 in the `hash_bytes` caller sweep. This docstring used to say *"a full
/// 256-bit digest does not fit a Nat scalar, so the field-reduced form is the faithful
/// Nat-shaped result"*. **A Lean `Nat` is unbounded** — it holds 2^256 with no trouble, and
/// `lean_uint64_to_nat` in `scripts/crypto-floor.c` is what actually caps this at 64 bits. So
/// the width here is a choice of the C ABI (`uint64_t`), not a consequence of the portal type,
/// and squeezing further to 30.906891 bits via `as_u32()` is a second, unforced loss on top.
///
/// A collision costs `2^15.4534` (~44,900 evaluations, milliseconds) and a second preimage
/// `2^30.91`, so this returns a value that binds a transcript at ~31 bits while the BLAKE3 it
/// wraps binds it at 256. Whatever the confined executor compares this against is comparing
/// 31 bits.
///
/// **The fix is an ABI change, and it belongs to the executor-PD portal, not to this sweep:**
/// return the 32-byte digest through the portal (the honest primitive
/// [`dreggcf_blake3_digest`] already exists right below and is unused by the portal), or —
/// if a scalar return is structural — at minimum stop discarding the 33 bits `uint64_t`
/// already carries. Changing this crate's return type alone desynchronises
/// `scripts/crypto-floor.c` and the Lean portal declaration, which is why it is named here
/// rather than half-done.
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
/// # ⚑ CLASS (A), NAMED NOT MIGRATED — AND THIS IS THE SHARPEST ONE IN THE FILE
///
/// The BLAKE3 keyed hash is EUF-CMA at 256 bits; the last line of this function
/// (`poseidon2::hash_bytes(tag.as_bytes()).as_u32()`) hands back a **~30.906891-bit MAC tag**.
/// A truncated MAC is not a MAC at its underlying strength — it is a MAC at the truncation
/// width. Derived: a forger who can pick two messages finds a tag collision in `2^15.4534`
/// (~44,900 evaluations); a forger targeting one message's tag succeeds in `2^30.91` offline
/// evaluations, or ~`2^30.9` online guesses against a verifier with no rate limit. For a
/// macaroon CAVEAT CHAIN — which is what the portal names this for — that is the whole
/// attenuation guarantee: forge the tag, drop the caveats.
///
/// So the docstring's "the assumption shifts from HMAC-SHA256 unforgeable to BLAKE3-keyed
/// unforgeable, both standard" is true of the MAC and **not true of this function**: the
/// operative assumption after the truncation is 31-bit unforgeability, which is not standard
/// and not satisfied.
///
/// **Not migrated here for the same reason as [`dreggcf_blake3_to_field`]:** the width is set
/// by the `uint64_t` C ABI in `sel4/dregg-pd/executor-pd/scripts/crypto-floor.c` (`:221`,
/// `lean_uint64_to_nat`) and the Lean portal declaration, not by anything this crate owns — and
/// the Lean `Nat` the portal returns is unbounded, so nothing forces a scalar at all. Widening
/// the Rust return alone desynchronises the shim. Owner: the executor-PD portal.
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
// §2 — STARK verify (ABSTRACT-Nat portal, fail-closed).
// ===========================================================================

/// STARK verification floor (ABSTRACT-Nat portal). The `dregg_stark_verify` Lean
/// portal is `Nat -> Nat -> Bool` over an ABSTRACT statement/proof pair — two
/// opaque Nats cannot carry a full `StarkProof` (trace/constraint/FRI Merkle
/// commitments + query openings, kilobytes of structured data). So THIS entry
/// FAILS CLOSED: it returns `false` (never a spurious accept).
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
    let wrong_key = unsafe { ed25519::verify(pk2.as_ptr(), msg.as_ptr(), msg.len(), sig.as_ptr()) };
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
    let wrong_v =
        unsafe { pedersen::verify_opening(value + 1, blinding.as_ptr(), commit.as_ptr()) };
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

    // ---- §1 ed25519 (REAL) -------------------------------------------------

    #[test]
    fn ed25519_real_teeth() {
        // ACCEPT a genuine sig; REJECT a forged sig, a wrong message, a wrong key.
        assert_eq!(
            dreggcf_ed25519_selftest(),
            0xF,
            "ed25519 verify_strict teeth"
        );
    }

    #[test]
    fn ed25519_known_answer_accepts_and_rejects() {
        use ed25519_dalek::{Signer, SigningKey};
        let sk = SigningKey::from_bytes(&[3u8; 32]);
        let pk = sk.verifying_key().to_bytes();
        let msg = b"on-device turn auth";
        let sig = sk.sign(msg).to_bytes();
        // genuine accepts
        let ok =
            unsafe { dreggcf_ed25519_verify(pk.as_ptr(), msg.as_ptr(), msg.len(), sig.as_ptr()) };
        assert_eq!(ok, 1);
        // a bad (all-zero) signature rejects
        let zero = [0u8; 64];
        let bad =
            unsafe { dreggcf_ed25519_verify(pk.as_ptr(), msg.as_ptr(), msg.len(), zero.as_ptr()) };
        assert_eq!(bad, 0);
        // a non-canonical / garbage public key rejects (from_bytes guard)
        let badpk = [0xFFu8; 32];
        let bk = unsafe {
            dreggcf_ed25519_verify(badpk.as_ptr(), msg.as_ptr(), msg.len(), sig.as_ptr())
        };
        assert_eq!(bk, 0);
    }

    // ---- §3 Pedersen (REAL, Ristretto255) ----------------------------------

    #[test]
    fn pedersen_real_teeth() {
        // opening verifies; wrong value/blinding fail; homomorphism holds.
        assert_eq!(
            dreggcf_pedersen_selftest(),
            0xF,
            "pedersen commitment teeth"
        );
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
        assert_ne!(
            c1, c3,
            "binding: a different value -> a different commitment"
        );
    }

    // ---- §7 ChaCha20-Poly1305 AEAD (REAL) ----------------------------------

    #[test]
    fn aead_real_teeth() {
        // round-trip; tampered ciphertext fails; wrong key fails; tampered tag fails.
        assert_eq!(
            dreggcf_chacha_selftest(),
            0xF,
            "chacha20poly1305 AEAD teeth"
        );
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
            unsafe {
                dreggcf_chacha_open(
                    key.as_ptr(),
                    nonce.as_ptr(),
                    boxed.as_ptr(),
                    8,
                    out.as_mut_ptr(),
                    out.len(),
                )
            },
            -1
        );
    }
}
