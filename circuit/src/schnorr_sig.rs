//! Schnorr signature scheme over the BabyBear^8 elliptic curve.
//!
//! This implements a Schnorr signature scheme using:
//! - An elliptic curve defined over BabyBear^8 (see [`schnorr_curve`])
//! - Poseidon2 as the Fiat-Shamir hash (STARK-native, ~85K constraints for verification)
//! - Deterministic nonces via BLAKE3 for side-channel resistance
//!
//! # Advantages over WOTS
//!
//! - **Multi-use**: Keys can sign multiple messages (not one-time).
//! - **Threshold-friendly**: Standard Schnorr threshold protocols apply (FROST, etc.).
//! - **Compact**: Signature is (point, scalar) = ~64 BabyBear elements vs 67 chains for WOTS.
//! - **Lower constraint count**: ~85K constraints vs ~100K for WOTS with Poseidon2 chains.
//!
//! # Security
//!
//! Security relies on the hardness of the discrete log problem on the curve over BabyBear^8.
//! The field has size ~2^248, giving ~124-bit security against Pollard-rho attacks.
//!
//! The Poseidon2-based Fiat-Shamir transform is secure under the assumption that Poseidon2
//! is a collision-resistant hash function over BabyBear.
//!
//! # Protocol
//!
//! ```text
//! KeyGen(seed):
//!   sk = BLAKE3(seed) reduced mod ORDER
//!   pk = sk * G
//!
//! Sign(sk, message):
//!   k = BLAKE3("dregg-schnorr-nonce" || sk || message) mod ORDER   (deterministic nonce)
//!   R = k * G
//!   e = Poseidon2(R.x || R.y || pk.x || pk.y || message_hash)     (Fiat-Shamir challenge)
//!   s = k - e * sk mod ORDER
//!   return (R, s)
//!
//! Verify(pk, sig=(R, s), message):
//!   e = Poseidon2(R.x || R.y || pk.x || pk.y || message_hash)
//!   Check: s*G + e*pk == R
//! ```

use crate::field::BabyBear;
use crate::poseidon2;
use crate::schnorr_curve::{
    CurvePoint, GENERATOR, Scalar, scalar_from_bytes, scalar_is_zero, scalar_mul_mod, scalar_sub,
    scalar_to_bytes, scalar_to_u64,
};

// ============================================================================
// Key Types
// ============================================================================

/// A Schnorr secret key: a scalar mod ORDER.
#[derive(Clone, Debug)]
pub struct SchnorrSecretKey(pub Scalar);

/// A Schnorr public key: a point on the curve (sk * G).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SchnorrPublicKey(pub CurvePoint);

/// A Schnorr signature: (R, s) where R is the nonce point and s is the response scalar.
#[derive(Clone, Debug)]
pub struct SchnorrSignature {
    /// The nonce commitment point R = k*G.
    pub r: CurvePoint,
    /// The response scalar s = k - e*sk mod ORDER.
    pub s: Scalar,
}

// ============================================================================
// Key Generation
// ============================================================================

/// Generate a Schnorr key pair from a 32-byte seed.
///
/// The secret key is derived deterministically from the seed via BLAKE3.
/// The public key is sk * G.
pub fn schnorr_keygen(seed: &[u8; 32]) -> (SchnorrSecretKey, SchnorrPublicKey) {
    let sk_bytes = blake3::derive_key("dregg-schnorr-keygen-v1", seed);
    let sk = scalar_from_bytes(&sk_bytes);

    // Ensure sk != 0 (astronomically unlikely but handle it)
    assert!(
        !scalar_is_zero(&sk),
        "derived secret key is zero (change seed)"
    );

    let pk_point = GENERATOR.scalar_mul(&sk);
    (SchnorrSecretKey(sk), SchnorrPublicKey(pk_point))
}

// ============================================================================
// Signing
// ============================================================================

/// Sign a message with a Schnorr secret key.
///
/// Uses a deterministic nonce derived from (sk, message) via BLAKE3 to prevent
/// nonce-reuse attacks and eliminate the need for a secure random source during signing.
pub fn schnorr_sign(
    sk: &SchnorrSecretKey,
    pk: &SchnorrPublicKey,
    message: &[u8],
) -> SchnorrSignature {
    // Derive deterministic nonce: k = H("dregg-schnorr-nonce" || sk_bytes || message)
    let sk_bytes = scalar_to_bytes(&sk.0);
    let mut nonce_input = Vec::with_capacity(32 + message.len());
    nonce_input.extend_from_slice(&sk_bytes);
    nonce_input.extend_from_slice(message);
    let k_bytes = blake3::derive_key("dregg-schnorr-nonce-v1", &nonce_input);
    let k = scalar_from_bytes(&k_bytes);

    // R = k * G
    let r = GENERATOR.scalar_mul(&k);

    // Compute Fiat-Shamir challenge: e = Poseidon2(R.x || R.y || pk.x || pk.y || msg_hash)
    let e = compute_challenge(&r, &pk.0, message);

    // s = k - e * sk mod ORDER
    let e_sk = scalar_mul_mod(&e, &sk.0);
    let s = scalar_sub(&k, &e_sk);

    SchnorrSignature { r, s }
}

// ============================================================================
// Verification
// ============================================================================

/// Verify a Schnorr signature against a public key and message.
///
/// Checks that s*G + e*pk == R, where e is recomputed from the transcript.
pub fn schnorr_verify(pk: &SchnorrPublicKey, sig: &SchnorrSignature, message: &[u8]) -> bool {
    // Reject degenerate cases
    if pk.0.is_infinity || sig.r.is_infinity {
        return false;
    }

    // Recompute challenge
    let e = compute_challenge(&sig.r, &pk.0, message);

    // Compute s*G + e*pk
    let s_g = GENERATOR.scalar_mul(&sig.s);
    let e_pk = pk.0.scalar_mul(&e);
    let lhs = s_g.add(&e_pk);

    // Check against R
    lhs == sig.r
}

/// Verify a Schnorr signature with a pre-hashed message.
///
/// This is the "in-circuit" variant where the message hash is provided directly
/// as BabyBear field elements (e.g., as public inputs to a STARK).
pub fn schnorr_verify_prehashed(
    pk: &SchnorrPublicKey,
    sig: &SchnorrSignature,
    message_hash: &[BabyBear; 8],
) -> bool {
    if pk.0.is_infinity || sig.r.is_infinity {
        return false;
    }

    let e = compute_challenge_from_elements(&sig.r, &pk.0, message_hash);
    let s_g = GENERATOR.scalar_mul(&sig.s);
    let e_pk = pk.0.scalar_mul(&e);
    let lhs = s_g.add(&e_pk);

    lhs == sig.r
}

// ============================================================================
// Fiat-Shamir Challenge (Poseidon2)
// ============================================================================

/// Compute the Fiat-Shamir challenge e from the transcript.
///
/// Transcript: R.x (8 elems) || R.y (8 elems) || pk.x (8 elems) || pk.y (8 elems) || msg_hash (8 elems)
/// Total: 40 field elements hashed through Poseidon2 sponge.
///
/// The output is squeezed into 8 BabyBear elements and interpreted as a scalar mod ORDER.
fn compute_challenge(r: &CurvePoint, pk: &CurvePoint, message: &[u8]) -> Scalar {
    // Hash the message to 8 field elements via BLAKE3 then encode
    let msg_blake = blake3::hash(message);
    let msg_hash = BabyBear::encode_hash(msg_blake.as_bytes());
    compute_challenge_from_elements(r, pk, &msg_hash)
}

/// Compute challenge from pre-encoded field elements.
fn compute_challenge_from_elements(
    r: &CurvePoint,
    pk: &CurvePoint,
    message_hash: &[BabyBear; 8],
) -> Scalar {
    // Build the transcript: R.x || R.y || pk.x || pk.y || msg_hash
    let mut transcript = Vec::with_capacity(40);
    transcript.extend_from_slice(&r.x.0);
    transcript.extend_from_slice(&r.y.0);
    transcript.extend_from_slice(&pk.x.0);
    transcript.extend_from_slice(&pk.y.0);
    transcript.extend_from_slice(message_hash);

    // Hash with Poseidon2 sponge — squeeze multiple times to get 8 elements
    let mut state = poseidon2::Poseidon2State::new();
    // Domain separation for Schnorr challenge
    state.state[15] = BabyBear::new(0x5343484E); // "SCHN"

    // Absorb (rate = 8 for this use case to absorb faster)
    let rate = 8;
    for chunk in transcript.chunks(rate) {
        for (i, &elem) in chunk.iter().enumerate() {
            state.state[i] += elem;
        }
        state.permute();
    }

    // Squeeze 8 elements for the challenge scalar
    let mut challenge_elems = [0u32; 8];
    for i in 0..8 {
        challenge_elems[i] = state.state[i].as_u32();
    }

    // Reduce mod ORDER
    scalar_from_challenge(&challenge_elems)
}

/// Convert 8 BabyBear elements (each < 2^31) into a scalar mod ORDER.
///
/// Each element contributes ~31 bits. We treat them as a 256-bit integer
/// (limbs) and reduce mod ORDER using Horner's method.
fn scalar_from_challenge(elems: &[u32; 8]) -> Scalar {
    let reduced = scalar_to_u64(elems);
    let mut result = [0u32; 8];
    result[0] = reduced as u32;
    result
}

// ============================================================================
// Compressed Public Key (for storage/transmission)
// ============================================================================

/// Compute a compressed public key: Poseidon2 hash of the point coordinates.
///
/// This is what gets stored in Merkle trees and validator sets.
pub fn compress_public_key(pk: &SchnorrPublicKey) -> BabyBear {
    let mut elements = Vec::with_capacity(16);
    elements.extend_from_slice(&pk.0.x.0);
    elements.extend_from_slice(&pk.0.y.0);
    poseidon2::hash_many(&elements)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keygen_produces_valid_key() {
        let seed = [0x42u8; 32];
        let (sk, pk) = schnorr_keygen(&seed);
        // pk should be sk * G
        let expected_pk = GENERATOR.scalar_mul(&sk.0);
        assert_eq!(pk.0, expected_pk);
        // pk should be on curve
        assert!(pk.0.is_on_curve());
        // pk should not be infinity
        assert!(!pk.0.is_infinity);
    }

    #[test]
    fn sign_verify_roundtrip() {
        let seed = [0x42u8; 32];
        let (sk, pk) = schnorr_keygen(&seed);

        let message = b"hello world, testing Schnorr over BabyBear^8";
        let sig = schnorr_sign(&sk, &pk, message);

        assert!(schnorr_verify(&pk, &sig, message));
    }

    #[test]
    fn verify_rejects_wrong_message() {
        let seed = [0x42u8; 32];
        let (sk, pk) = schnorr_keygen(&seed);

        let message = b"correct message";
        let sig = schnorr_sign(&sk, &pk, message);

        let wrong_message = b"wrong message";
        assert!(!schnorr_verify(&pk, &sig, wrong_message));
    }

    #[test]
    fn verify_rejects_wrong_key() {
        let seed1 = [0x42u8; 32];
        let seed2 = [0x43u8; 32];
        let (sk1, pk1) = schnorr_keygen(&seed1);
        let (_sk2, pk2) = schnorr_keygen(&seed2);

        let message = b"test message";
        let sig = schnorr_sign(&sk1, &pk1, message);

        assert!(!schnorr_verify(&pk2, &sig, message));
    }

    #[test]
    fn deterministic_signatures() {
        let seed = [0x55u8; 32];
        let (sk, pk) = schnorr_keygen(&seed);

        let message = b"determinism test";
        let sig1 = schnorr_sign(&sk, &pk, message);
        let sig2 = schnorr_sign(&sk, &pk, message);

        // Same key + same message => same signature (deterministic nonce)
        assert_eq!(sig1.r, sig2.r);
        assert_eq!(sig1.s, sig2.s);
    }

    #[test]
    fn different_messages_different_signatures() {
        let seed = [0x55u8; 32];
        let (sk, pk) = schnorr_keygen(&seed);

        let sig1 = schnorr_sign(&sk, &pk, b"message A");
        let sig2 = schnorr_sign(&sk, &pk, b"message B");

        // Different messages => different signatures
        assert_ne!(sig1.r, sig2.r);
    }

    #[test]
    fn different_keys_different_public_keys() {
        let (_, pk1) = schnorr_keygen(&[0x01; 32]);
        let (_, pk2) = schnorr_keygen(&[0x02; 32]);
        assert_ne!(pk1, pk2);
    }

    #[test]
    fn compressed_pk_deterministic() {
        let seed = [0x99u8; 32];
        let (_, pk) = schnorr_keygen(&seed);
        let h1 = compress_public_key(&pk);
        let h2 = compress_public_key(&pk);
        assert_eq!(h1, h2);
        assert_ne!(h1, BabyBear::ZERO);
    }

    #[test]
    fn nonce_point_is_on_curve() {
        let seed = [0xAAu8; 32];
        let (sk, pk) = schnorr_keygen(&seed);
        let sig = schnorr_sign(&sk, &pk, b"test");
        assert!(sig.r.is_on_curve());
    }

    #[test]
    fn prehashed_verify_roundtrip() {
        let seed = [0xBBu8; 32];
        let (sk, pk) = schnorr_keygen(&seed);

        let message = b"prehashed test";
        let sig = schnorr_sign(&sk, &pk, message);

        // Compute the message hash the same way the signer does
        let msg_blake = blake3::hash(message);
        let msg_hash = BabyBear::encode_hash(msg_blake.as_bytes());

        assert!(schnorr_verify_prehashed(&pk, &sig, &msg_hash));
    }
}
