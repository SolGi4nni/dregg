//! Canonical action-binding commitment for STARK proofs.
//!
//! This module defines the single authoritative function for computing the
//! binding commitment that ties a STARK proof to the (action, resource) pair
//! it authorizes. All three layers (prover, wire verifier, turn verifier) MUST
//! use this function to ensure they agree on what the proof is bound to.
//!
//! The binding domain is `(action, resource)` — the semantically meaningful
//! parts of an authorization request. Anti-replay fields (nonce, timestamp)
//! are NOT part of the binding because they change between requests for the
//! same authorization and the proof cannot be bound to values that don't exist
//! at proving time.
//!
//! # Security
//!
//! The binding commitment uses 4 BabyBear field elements (124 bits), providing
//! a birthday bound of ~2^62. This follows the same pattern as
//! `AccumulatedHash` in ivc.rs. A single BabyBear element (~31 bits) would only
//! give ~2^15.5 collision resistance, which is uncomfortably low even though
//! exploiting a collision requires a valid token for the colliding action.

use crate::field::BabyBear;
use crate::poseidon2;
use serde::{Deserialize, Serialize};

/// Domain separation tag for action binding commitments.
const ACTION_BINDING_DSK: &str = "dregg-action-binding-v1";

/// Domain separation tag for presentation tag commitments.
const PRESENTATION_TAG_DSK: &str = "dregg-presentation-tag-v1";

/// Number of BabyBear elements in an action binding commitment.
/// 4 elements * 31 bits each = 124 bits of collision resistance,
/// requiring ~2^62 work for a birthday attack (well beyond practical).
pub const ACTION_BINDING_WIDTH: usize = 4;

/// Number of BabyBear elements in a presentation tag.
/// 4 elements * 31 bits each = 124 bits of collision resistance,
/// birthday bound ~2^62. A single element (~31 bits) only provides ~2^15.5
/// collision resistance, creating a linkability risk at ~46K presentations.
pub const PRESENTATION_TAG_WIDTH: usize = 4;

/// A 124-bit hash digest over BabyBear, providing ~62-bit birthday collision resistance.
/// Used wherever a single BabyBear element's ~15.5-bit birthday bound is insufficient.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct WideHash(pub [BabyBear; 4]);

impl WideHash {
    pub const WIDTH: usize = 4;
    pub const ZERO: Self = Self([BabyBear::ZERO; 4]);

    /// Compute a wide hash from inputs with domain separation.
    ///
    /// Absorbs domain separator (via BLAKE3) + inputs through Poseidon2 sponge,
    /// then squeezes 4 elements for 124-bit collision resistance.
    pub fn from_poseidon2(domain: &str, inputs: &[BabyBear]) -> Self {
        use crate::poseidon2::Poseidon2State;

        let mut state = Poseidon2State::new();
        // Domain separation: encode BLAKE3(domain) in capacity
        let dsk_hash = *blake3::hash(domain.as_bytes()).as_bytes();
        state.state[4] = BabyBear::new(
            u32::from_le_bytes([dsk_hash[0], dsk_hash[1], dsk_hash[2], dsk_hash[3]])
                % crate::field::BABYBEAR_P,
        );
        // Encode input length in second capacity position
        state.state[5] = BabyBear::new(inputs.len() as u32);

        // Absorb inputs in rate-4 chunks
        let rate = 4;
        for chunk in inputs.chunks(rate) {
            for (i, &elem) in chunk.iter().enumerate() {
                state.state[i] += elem;
            }
            state.permute();
        }

        // Squeeze 4 elements (124-bit security)
        Self([
            state.state[0],
            state.state[1],
            state.state[2],
            state.state[3],
        ])
    }

    pub fn is_zero(&self) -> bool {
        self.0 == [BabyBear::ZERO; 4]
    }

    pub fn as_slice(&self) -> &[BabyBear; 4] {
        &self.0
    }

    /// Compress to single element (for contexts that need narrow representation).
    /// Returns `BabyBear::ZERO` when the hash is zero (preserves zero-identity).
    pub fn to_narrow(&self) -> BabyBear {
        if self.is_zero() {
            BabyBear::ZERO
        } else {
            poseidon2::hash_many(&self.0)
        }
    }
}

impl std::ops::Index<usize> for WideHash {
    type Output = BabyBear;
    fn index(&self, index: usize) -> &BabyBear {
        &self.0[index]
    }
}

impl<'a> IntoIterator for &'a WideHash {
    type Item = &'a BabyBear;
    type IntoIter = std::slice::Iter<'a, BabyBear>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

/// A multi-element action binding commitment providing 124-bit security.
///
/// A single BabyBear element only provides ~31 bits, making birthday attacks
/// trivial at 2^15.5 (~46K attempts). Using 4 elements raises this to 2^62.
pub type ActionBinding = [BabyBear; ACTION_BINDING_WIDTH];

/// A multi-element presentation tag providing 124-bit collision resistance.
///
/// Previously a single BabyBear element (~31 bits), which had a non-negligible
/// collision probability at the birthday bound (~46K presentations). Widened to
/// 4 elements (124 bits) so that collision probability remains negligible even
/// at billions of presentations.
pub type PresentationTag = [BabyBear; PRESENTATION_TAG_WIDTH];

/// Compute a deterministic action-binding commitment from `(action, resource)`.
///
/// This is the canonical binding domain for STARK proofs. The result is 4
/// BabyBear field elements (124-bit collision resistance) that are:
/// - Included as public inputs of the STARK proof by the prover
/// - Recomputed by verifiers from the request fields and checked against the proof
///
/// # Binding semantics
///
/// - `action`: The operation being performed (e.g., "read", "write", "admin").
///   Maps to `AuthRequest.action` (token layer), `AuthorizationRequest.action` (wire),
///   and `Action.method` decoded as a string (turn layer).
///
/// - `resource`: The target of the operation (e.g., "api/v1/users", a cell ID).
///   Canonically derived as `app_id.or(service).unwrap_or("")` from the token
///   layer's `AuthRequest`. Maps to `AuthorizationRequest.resource` on the wire.
///   For bridge-mint proofs, the resource is `hex(destination_federation)`.
///
/// # Security
///
/// The commitment uses 4 BabyBear elements (124 bits of collision resistance,
/// birthday bound ~2^62). The BLAKE3 keyed hash provides domain separation from
/// other protocol uses of the same strings, and Poseidon2 squeezing ensures the
/// values are in-circuit verifiable.
pub fn compute_action_binding(action: &str, resource: &str) -> ActionBinding {
    use crate::poseidon2::Poseidon2State;

    // Derive the domain separation key from the DSK string.
    let dsk = *blake3::hash(ACTION_BINDING_DSK.as_bytes()).as_bytes();

    // Compute BLAKE3 keyed hash of (action || 0x00 || resource).
    let mut buf = Vec::with_capacity(action.len() + 1 + resource.len());
    buf.extend_from_slice(action.as_bytes());
    buf.push(0x00); // unambiguous separator
    buf.extend_from_slice(resource.as_bytes());

    let digest = blake3::keyed_hash(&dsk, &buf);

    // Encode the 32-byte digest as 8 BabyBear elements.
    let limbs = BabyBear::encode_hash(digest.as_bytes());

    // Absorb all 8 limbs through Poseidon2 sponge and squeeze 4 elements.
    let mut state = Poseidon2State::new();
    // Domain separation: encode input length in capacity
    state.state[4] = BabyBear::new(8);
    // Absorb first 4 limbs
    state.state[0] = limbs[0];
    state.state[1] = limbs[1];
    state.state[2] = limbs[2];
    state.state[3] = limbs[3];
    state.permute();
    // Absorb remaining 4 limbs
    state.state[0] += limbs[4];
    state.state[1] += limbs[5];
    state.state[2] += limbs[6];
    state.state[3] += limbs[7];
    state.permute();

    // Squeeze 4 elements (124-bit security)
    [
        state.state[0],
        state.state[1],
        state.state[2],
        state.state[3],
    ]
}

/// Compute the legacy single-element action binding (31-bit security).
///
/// **DEPRECATED**: This function provides only ~2^15.5 collision resistance.
/// Use [`compute_action_binding`] (which returns 4 elements) instead.
///
/// This remains available for contexts that need a single summary element
/// (e.g., the narrow accumulated hash in the STARK AIR trace). It is NOT
/// suitable as the sole binding commitment.
pub fn compute_action_binding_narrow(action: &str, resource: &str) -> BabyBear {
    let wide = compute_action_binding(action, resource);
    // Compress 4 elements down to 1 via Poseidon2 for legacy compatibility.
    poseidon2::hash_many(&wide)
}

/// Compute a wide presentation tag with 124-bit collision resistance.
///
/// The presentation tag blinds the `final_root` for unlinkability: same credential
/// produces a different tag every time it is shown (because `presentation_randomness`
/// is fresh per presentation).
///
/// Inputs:
/// - `final_root`: the end-of-chain state root (private)
/// - `presentation_randomness`: fresh randomness per presentation (private)
/// - `verifier_nonce`: challenge from the verifier (public)
///
/// Returns 4 BabyBear elements squeezed from a Poseidon2 sponge, providing
/// 124-bit collision resistance (birthday bound ~2^62).
pub fn compute_presentation_tag(
    final_root: BabyBear,
    presentation_randomness: BabyBear,
    verifier_nonce: BabyBear,
) -> PresentationTag {
    use crate::poseidon2::Poseidon2State;

    let mut state = Poseidon2State::new();
    // Domain separation: encode purpose and input count in capacity
    let dsk_hash = *blake3::hash(PRESENTATION_TAG_DSK.as_bytes()).as_bytes();
    state.state[4] = BabyBear::new(
        u32::from_le_bytes([dsk_hash[0], dsk_hash[1], dsk_hash[2], dsk_hash[3]])
            % (crate::field::BABYBEAR_P),
    );

    // Absorb the 3 inputs into the rate portion
    state.state[0] = final_root;
    state.state[1] = presentation_randomness;
    state.state[2] = verifier_nonce;
    state.permute();

    // Squeeze 4 elements (124-bit security)
    [
        state.state[0],
        state.state[1],
        state.state[2],
        state.state[3],
    ]
}

/// Compute the legacy single-element presentation tag (31-bit security).
///
/// **DEPRECATED**: This function provides only ~2^15.5 collision resistance.
/// Use [`compute_presentation_tag`] (which returns 4 elements) instead.
///
/// This remains available for composition commitment computation and other
/// contexts that need a single summary element.
pub fn compute_presentation_tag_narrow(
    final_root: BabyBear,
    presentation_randomness: BabyBear,
    verifier_nonce: BabyBear,
) -> BabyBear {
    let wide = compute_presentation_tag(final_root, presentation_randomness, verifier_nonce);
    // Compress 4 elements down to 1 via Poseidon2 for legacy compatibility.
    poseidon2::hash_many(&wide)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic() {
        let a = compute_action_binding("read", "api/v1/users");
        let b = compute_action_binding("read", "api/v1/users");
        assert_eq!(a, b);
    }

    #[test]
    fn returns_four_elements() {
        let binding = compute_action_binding("read", "api/v1/users");
        assert_eq!(binding.len(), ACTION_BINDING_WIDTH);
        // All elements should be non-zero (extremely unlikely to have a zero element
        // from Poseidon2, but we mainly check the structure)
        assert_eq!(binding.len(), 4);
    }

    #[test]
    fn different_action_different_commitment() {
        let a = compute_action_binding("read", "api/v1/users");
        let b = compute_action_binding("write", "api/v1/users");
        assert_ne!(a, b);
    }

    #[test]
    fn different_resource_different_commitment() {
        let a = compute_action_binding("read", "api/v1/users");
        let b = compute_action_binding("read", "api/v1/posts");
        assert_ne!(a, b);
    }

    #[test]
    fn separator_prevents_ambiguity() {
        // "read\x00api" != "rea\x00dapi" due to unambiguous separator
        let a = compute_action_binding("read", "api");
        let b = compute_action_binding("rea", "dapi");
        // Extremely unlikely to collide but the separator makes it structurally impossible
        // to confuse action/resource boundaries.
        assert_ne!(a, b);
    }

    #[test]
    fn empty_strings_valid() {
        // Should not panic
        let binding = compute_action_binding("", "");
        assert_eq!(binding.len(), 4);
    }

    #[test]
    fn narrow_is_deterministic_compression_of_wide() {
        let wide = compute_action_binding("admin", "system");
        let narrow = compute_action_binding_narrow("admin", "system");
        // The narrow version should be the Poseidon2 hash of the wide elements
        let expected = poseidon2::hash_many(&wide);
        assert_eq!(narrow, expected);
    }

    // =========================================================================
    // Presentation tag tests
    // =========================================================================

    #[test]
    fn presentation_tag_deterministic() {
        let root = BabyBear::new(12345);
        let rand = BabyBear::new(67890);
        let nonce = BabyBear::new(11111);
        let a = compute_presentation_tag(root, rand, nonce);
        let b = compute_presentation_tag(root, rand, nonce);
        assert_eq!(a, b);
    }

    #[test]
    fn presentation_tag_returns_four_elements() {
        let tag = compute_presentation_tag(BabyBear::new(1), BabyBear::new(2), BabyBear::new(3));
        assert_eq!(tag.len(), PRESENTATION_TAG_WIDTH);
    }

    #[test]
    fn presentation_tag_different_randomness_different_tag() {
        let root = BabyBear::new(42);
        let nonce = BabyBear::new(99);
        let a = compute_presentation_tag(root, BabyBear::new(111), nonce);
        let b = compute_presentation_tag(root, BabyBear::new(222), nonce);
        assert_ne!(
            a, b,
            "Different randomness must produce different tags (unlinkability)"
        );
    }

    #[test]
    fn presentation_tag_different_nonce_different_tag() {
        let root = BabyBear::new(42);
        let rand = BabyBear::new(777);
        let a = compute_presentation_tag(root, rand, BabyBear::new(1));
        let b = compute_presentation_tag(root, rand, BabyBear::new(2));
        assert_ne!(a, b, "Different verifier nonce must produce different tags");
    }

    #[test]
    fn presentation_tag_different_root_different_tag() {
        let rand = BabyBear::new(777);
        let nonce = BabyBear::new(99);
        let a = compute_presentation_tag(BabyBear::new(100), rand, nonce);
        let b = compute_presentation_tag(BabyBear::new(200), rand, nonce);
        assert_ne!(a, b, "Different final_root must produce different tags");
    }

    #[test]
    fn presentation_tag_narrow_is_compression_of_wide() {
        let root = BabyBear::new(55555);
        let rand = BabyBear::new(88888);
        let nonce = BabyBear::new(11111);
        let wide = compute_presentation_tag(root, rand, nonce);
        let narrow = compute_presentation_tag_narrow(root, rand, nonce);
        let expected = poseidon2::hash_many(&wide);
        assert_eq!(narrow, expected);
    }
}
