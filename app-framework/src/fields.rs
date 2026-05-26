//! Canonical field-element encoding helpers for `SetField` effects.
//!
//! These three functions define the canonical wire format for the three
//! most common `FieldElement` construction patterns used across all
//! starbridge apps.  Centralising them here guarantees cross-app
//! compatibility: nameservice and identity share field elements at
//! runtime and must agree byte-for-byte on their encoding.
//!
//! # Encoding convention
//!
//! | Helper | Convention |
//! |--------|-----------|
//! | [`field_from_bytes`] | BLAKE3 hash of the input bytes → 32-byte digest |
//! | [`field_from_u64`] | Big-endian u64 in the trailing 8 bytes, leading 24 bytes zero |
//! | [`hex_encode_32`] | Lowercase hex of a 32-byte array (64 ASCII chars) |
//!
//! `field_from_u64`'s big-endian, right-aligned layout matches the
//! `field_from_u64_be` convention used in `dregg_cell::program` so that
//! integer-typed `StateConstraint` operands compare correctly against
//! field values produced here.

use dregg_cell::state::FieldElement;

/// Hash arbitrary bytes into a 32-byte [`FieldElement`] suitable for
/// `SetField` effect data.
///
/// Uses BLAKE3; the output is the raw 32-byte digest, not domain-separated.
/// Callers that need domain separation should pass a prefixed slice, e.g.
/// `field_from_bytes(b"my-domain:" || payload)`.
#[must_use]
pub fn field_from_bytes(bytes: &[u8]) -> FieldElement {
    *blake3::hash(bytes).as_bytes()
}

/// Encode a `u64` as a big-endian-padded 32-byte [`FieldElement`].
///
/// The value is stored in the trailing 8 bytes with the leading 24 bytes
/// set to zero.  This matches the `field_from_u64_be` convention used in
/// `dregg_cell::program` so that integer-typed constraint operands are
/// comparable to field values produced here.
#[must_use]
pub fn field_from_u64(value: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&value.to_be_bytes());
    out
}

/// Hex-encode a 32-byte array as a 64-character lowercase ASCII string.
///
/// Used primarily for producing `factory_vk_hex` / `child_program_vk_hex`
/// entries in inspector-descriptor JSON blobs.
#[must_use]
pub fn hex_encode_32(bytes: &[u8; 32]) -> String {
    crate::hex::bytes32_to_hex(bytes)
}
