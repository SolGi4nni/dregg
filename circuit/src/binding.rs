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
//! The binding commitment uses 8 BabyBear field elements (~248 bits of preimage),
//! providing a birthday collision bound of ~2^124 — matching the system's own
//! 128-bit FRI soundness and clearing the 120-bit floor.
//!
//! Width matters here because the action binding is **collision-exposed**, not
//! merely second-preimage-protected. The attacker controls BOTH preimages: it
//! picks a benign `(action_A, resource_A)` (for which an issuer willingly grants
//! a token) and a malicious `(action_B, resource_B)`, and searches for a birthday
//! collision `binding(A) == binding(B)`. A token legitimately issued for A is then
//! presentable wherever a verifier authorizes B (the verifier recomputes
//! `compute_action_binding(B)` and the committed binding matches) — a privilege
//! escalation. At a 4-felt width the search costs only ~2^62, HALF the FRI
//! soundness and below the floor; at 8 felts it costs ~2^124.
//!
//! The same reasoning applies to `WideHash` wherever an attacker controls the
//! hashed preimage (`revealed_facts_commitment`, `composition_commitment`,
//! presentation tags) — all are widened to 8 felts. A use where one side is fixed
//! by a prior commitment the adversary cannot choose would be second-preimage-only
//! (~2^248, fine at any width), but the binding/commitment surface here is not
//! that case, so it carries the full collision-resistant width.

use crate::field::BabyBear;
use crate::poseidon2;
use serde::{Deserialize, Serialize};

/// Domain separation tag for action binding commitments.
const ACTION_BINDING_DSK: &str = "dregg-action-binding-v1";

/// Domain separation tag for presentation tag commitments.
const PRESENTATION_TAG_DSK: &str = "dregg-presentation-tag-v1";

/// Number of BabyBear elements in an action binding commitment.
/// 8 elements * ~31 bits each = ~248 bits of preimage, giving a birthday
/// collision bound of ~2^124 (matching the 128-bit FRI soundness, above the
/// 120-bit floor). The action binding is collision-exposed (the attacker chooses
/// both `(action, resource)` preimages), so the full collision-resistant width
/// is required here, not just second-preimage protection.
pub const ACTION_BINDING_WIDTH: usize = 8;

/// Number of BabyBear elements in a presentation tag.
/// 8 elements * ~31 bits each = ~248 bits of preimage, birthday bound ~2^124.
/// A narrower tag exposes a linkability collision (two presentations colliding to
/// the same blinded tag); 8 felts keep that probability negligible at any
/// realistic presentation count.
pub const PRESENTATION_TAG_WIDTH: usize = 8;

/// A ~248-bit hash digest over BabyBear, providing ~124-bit birthday collision
/// resistance (matching the 128-bit FRI soundness, above the 120-bit floor).
/// Used wherever an adversary controls the hashed preimage and a collision would
/// be load-bearing (action/composition/revealed-facts bindings).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct WideHash(pub [BabyBear; 8]);

impl Default for WideHash {
    fn default() -> Self {
        Self::ZERO
    }
}

impl WideHash {
    pub const WIDTH: usize = 8;
    pub const ZERO: Self = Self([BabyBear::ZERO; 8]);

    /// Compute a wide hash from inputs with domain separation.
    ///
    /// Absorbs domain separator (via BLAKE3) + inputs through Poseidon2 sponge,
    /// then squeezes 8 elements for ~124-bit birthday collision resistance.
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

        // Squeeze 8 elements (~124-bit birthday security): rate-4 block,
        // permute, rate-4 block again (mirrors `poseidon2::hash_many_8`).
        let mut out = [BabyBear::ZERO; 8];
        out[0] = state.state[0];
        out[1] = state.state[1];
        out[2] = state.state[2];
        out[3] = state.state[3];
        state.permute();
        out[4] = state.state[0];
        out[5] = state.state[1];
        out[6] = state.state[2];
        out[7] = state.state[3];
        Self(out)
    }

    pub fn is_zero(&self) -> bool {
        self.0 == [BabyBear::ZERO; 8]
    }

    pub fn as_slice(&self) -> &[BabyBear; 8] {
        &self.0
    }

    /// Decompose into the canonical 4-felt on-wire representation.
    ///
    /// A `WideHash` IS its eight BabyBear elements: the felt representation is the
    /// array itself, matching the squeeze in [`WideHash::from_poseidon2`] and the
    /// `ACTION_BINDING_WIDTH`/`PRESENTATION_TAG_WIDTH` 8-felt commitment encoding.
    /// This is the exact inverse of [`WideHash::from_felts`]: for any `h`,
    /// `WideHash::from_felts(&h.to_felts()) == Ok(h)`.
    pub fn to_felts(&self) -> [BabyBear; Self::WIDTH] {
        self.0
    }

    /// Reconstruct from the canonical felt representation.
    ///
    /// The exact inverse of [`WideHash::to_felts`]. Requires exactly `WIDTH` (8)
    /// elements — the same width the on-wire commitment carries — and errors
    /// otherwise so a malformed felt buffer fails closed rather than silently
    /// truncating or zero-padding.
    pub fn from_felts(felts: &[BabyBear]) -> Result<Self, String> {
        if felts.len() != Self::WIDTH {
            return Err(format!(
                "WideHash::from_felts expects {} felts, got {}",
                Self::WIDTH,
                felts.len()
            ));
        }
        let mut arr = [BabyBear::ZERO; Self::WIDTH];
        arr.copy_from_slice(felts);
        Ok(Self(arr))
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

/// A multi-element action binding commitment providing ~124-bit birthday security.
///
/// The action binding is collision-exposed (the attacker chooses both
/// `(action, resource)` preimages), so it carries the full collision-resistant
/// width: 8 elements (~248-bit preimage, birthday bound ~2^124, matching the
/// 128-bit FRI soundness). A 4-felt width would expose a ~2^62 collision — below
/// the 120-bit floor — and a single element would be trivially attackable.
pub type ActionBinding = [BabyBear; ACTION_BINDING_WIDTH];

/// A multi-element presentation tag providing ~124-bit collision resistance.
///
/// A narrower tag exposes a linkability collision; 8 elements (~248-bit preimage,
/// birthday bound ~2^124) keep that probability negligible at any realistic
/// presentation count.
pub type PresentationTag = [BabyBear; PRESENTATION_TAG_WIDTH];

/// Compute a deterministic action-binding commitment from `(action, resource)`.
///
/// This is the canonical binding domain for STARK proofs. The result is 8
/// BabyBear field elements (~124-bit birthday collision resistance) that are:
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
/// The commitment uses 8 BabyBear elements (~248 bits of preimage, birthday
/// collision bound ~2^124, matching the 128-bit FRI soundness and above the
/// 120-bit floor). The action binding is collision-exposed (the attacker chooses
/// both preimages), so the full collision-resistant width is required. The BLAKE3
/// keyed hash provides domain separation from other protocol uses of the same
/// strings, and Poseidon2 squeezing ensures the values are in-circuit verifiable.
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

    // Absorb all 8 limbs through Poseidon2 sponge and squeeze 8 elements.
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

    // Squeeze 8 elements (~124-bit birthday security): rate-4 block, permute,
    // rate-4 block again (mirrors `WideHash::from_poseidon2`).
    let mut out = [BabyBear::ZERO; ACTION_BINDING_WIDTH];
    out[0] = state.state[0];
    out[1] = state.state[1];
    out[2] = state.state[2];
    out[3] = state.state[3];
    state.permute();
    out[4] = state.state[0];
    out[5] = state.state[1];
    out[6] = state.state[2];
    out[7] = state.state[3];
    out
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
/// Returns 8 BabyBear elements squeezed from a Poseidon2 sponge, providing
/// ~124-bit birthday collision resistance.
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

    // Squeeze 8 elements (~124-bit birthday security): rate-4 block, permute,
    // rate-4 block again.
    let mut out = [BabyBear::ZERO; PRESENTATION_TAG_WIDTH];
    out[0] = state.state[0];
    out[1] = state.state[1];
    out[2] = state.state[2];
    out[3] = state.state[3];
    state.permute();
    out[4] = state.state[0];
    out[5] = state.state[1];
    out[6] = state.state[2];
    out[7] = state.state[3];
    out
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
    fn wide_hash_to_felts_from_felts_round_trip() {
        // to_felts is the exact inverse of from_felts.
        let h = WideHash::from_poseidon2("dregg-test-widehash", &[BabyBear::new(7), BabyBear::new(11)]);
        let felts = h.to_felts();
        assert_eq!(felts.len(), WideHash::WIDTH);
        // The collision-resistant width is 8 felts (~124-bit birthday).
        assert_eq!(WideHash::WIDTH, 8);
        assert_eq!(WideHash::from_felts(&felts).expect("8-felt buffer decodes"), h);

        // The felt decomposition is literally the underlying array.
        assert_eq!(&felts, h.as_slice());

        // ZERO round-trips too.
        assert_eq!(
            WideHash::from_felts(&WideHash::ZERO.to_felts()).expect("zero decodes"),
            WideHash::ZERO
        );

        // Wrong width fails closed (no truncate / zero-pad).
        assert!(WideHash::from_felts(&[BabyBear::ZERO; 3]).is_err());
        assert!(WideHash::from_felts(&[BabyBear::ZERO; 5]).is_err());
    }

    #[test]
    fn returns_collision_resistant_width() {
        let binding = compute_action_binding("read", "api/v1/users");
        assert_eq!(binding.len(), ACTION_BINDING_WIDTH);
        // 8 felts ≈ 124-bit birthday collision resistance (matching the 128-bit FRI
        // soundness, above the 120-bit floor). The action binding is collision-exposed
        // (adversary chooses both preimages), so the full width is load-bearing.
        assert_eq!(binding.len(), 8);
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
        assert_eq!(binding.len(), ACTION_BINDING_WIDTH);
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
