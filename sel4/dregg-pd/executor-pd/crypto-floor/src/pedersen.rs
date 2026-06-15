//! §3 — Pedersen value commitment. REAL (Ristretto255, no_std).
//!
//! THE RECONCILIATION. There are two commitment surfaces in the tree:
//!   * the in-circuit Schnorr curve over BabyBear^8 (`circuit/src/schnorr_curve.rs`),
//!     used ONLY for Schnorr SIGNATURES, never value commitments; and
//!   * the host/executor confidential-value commitment over **Ristretto255**
//!     (`cell/src/value_commitment.rs`), `commit = value·V + blinding·R`.
//! The STARK circuit does NOT algebraically re-derive a value commitment — it
//! BINDS the 32 commitment bytes as a public input (`effect_action_air.rs`,
//! `SCHEMA_NOTE_SPEND` field 3: the value-commitment 32B encoded as 8 BabyBear
//! limbs) and the EXECUTOR enforces the homomorphic balance over those same
//! Ristretto commitments. So the primitive the system actually constructs, checks,
//! and binds is the Ristretto `commit_bytes` — and matching it byte-for-byte is
//! what "the same primitive the circuit verifies" means here. (A BabyBear-curve
//! commitment would bind bytes the executor never produces, so its homomorphism
//! would not close — see the schnorr_curve docs: that curve is the VALUE-path
//! SIGNATURE, not the commitment.)
//!
//! THIS module computes `commit_bytes(value, blinding) = (value·V + scalar(blinding)·R)
//! .compress()` byte-IDENTICALLY to `cell::value_commitment::commit_bytes`: the same
//! generators `V`/`R` (BLAKE3-XOF-derived, domain "dregg-pedersen generator v1" over
//! the value / randomness tags), the same `Scalar::from(value)`, the same
//! `Scalar::from_bytes_mod_order(blinding)`, the same canonical 32-byte compressed
//! Ristretto encoding. A round-trip KAT pins the equality against the carried
//! reference vector (see `lib.rs` / the host witness).
//!
//! `no_std`: curve25519-dalek 4 is `#![no_std]` with `features = ["alloc"]` (the
//! portable serial backend on this cross target); BLAKE3 is the `pure` no_std
//! backend already carried. No `std`, no `rand`.

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;

/// Derive a Ristretto generator from a domain-separation tag — VERBATIM
/// `cell::value_commitment::hash_to_generator`: BLAKE3 XOF (keyed-derive
/// "dregg-pedersen generator v1") over `domain`, 64 uniform bytes → Elligator2
/// (`from_uniform_bytes`). The byte-for-byte same generator the host produces.
fn hash_to_generator(domain: &[u8]) -> RistrettoPoint {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-pedersen generator v1");
    hasher.update(domain);
    let mut xof = hasher.finalize_xof();
    let mut uniform = [0u8; 64];
    xof.fill(&mut uniform);
    RistrettoPoint::from_uniform_bytes(&uniform)
}

/// Value generator `V = hash_to_point("dregg-value-generator")`.
#[inline]
fn value_generator() -> RistrettoPoint {
    hash_to_generator(b"dregg-value-generator")
}

/// Randomness generator `R = hash_to_point("dregg-randomness-generator")`.
/// The discrete log between `V` and `R` is unknown (random-oracle on BLAKE3).
#[inline]
fn randomness_generator() -> RistrettoPoint {
    hash_to_generator(b"dregg-randomness-generator")
}

/// Compute the Pedersen value commitment `value·V + scalar(blinding)·R` and write
/// its canonical 32-byte compressed Ristretto encoding to `out32`.
///
/// Byte-identical to `cell::value_commitment::commit_bytes(value, blinding)` — the
/// commitment the executor's conservation check consumes and the circuit binds.
/// The blinding bytes are reduced mod the group order (`Scalar::from_bytes_mod_order`),
/// matching `scalar_from_blinding_bytes`, so any 32 raw bytes are a valid blinding.
///
/// # Safety
/// `blinding` must point to 32 readable bytes; `out32` to 32 writable bytes.
pub unsafe fn commit(value: u64, blinding: *const u8, out32: *mut u8) {
    if blinding.is_null() || out32.is_null() {
        return;
    }
    let mut bl = [0u8; 32];
    bl.copy_from_slice(core::slice::from_raw_parts(blinding, 32));

    let v = Scalar::from(value);
    let r = Scalar::from_bytes_mod_order(bl);
    let point = v * value_generator() + r * randomness_generator();
    let compressed = point.compress().to_bytes();
    core::ptr::copy_nonoverlapping(compressed.as_ptr(), out32, 32);
}

/// Verify that `commitment32` opens to `(value, blinding)` — i.e. recompute the
/// commitment and compare the 32 canonical bytes. This is the binding-check the
/// note-open path needs: given a claimed opening, accept iff it matches the carried
/// commitment. Returns `1` iff the recomputed commitment equals `commitment32`.
///
/// # Safety
/// `blinding` / `commitment32` must each point to 32 readable bytes.
pub unsafe fn verify_opening(
    value: u64,
    blinding: *const u8,
    commitment32: *const u8,
) -> u8 {
    if blinding.is_null() || commitment32.is_null() {
        return 0;
    }
    let mut recomputed = [0u8; 32];
    commit(value, blinding, recomputed.as_mut_ptr());
    let claimed = core::slice::from_raw_parts(commitment32, 32);
    // Constant-time-ish byte compare (no early-out leak of the prefix length).
    let mut diff: u8 = 0;
    for i in 0..32 {
        diff |= recomputed[i] ^ claimed[i];
    }
    (diff == 0) as u8
}
