//! Hash + PRG primitives (all blake3), with unambiguous domain separation.
//!
//! Two distinct roles, both instantiated with blake3:
//!
//! * **`H` — the collision-resistant Merkle hash.** This is the primitive
//!   UNIQUENESS reduces to. blake3 is a 256-bit collision-resistant hash; a
//!   second output verifying for a fixed `(pk, epoch)` would force a blake3
//!   collision (see [`crate::vrf`]). Every `H` call is length- and
//!   domain-prefixed so no two logically distinct inputs share an encoding
//!   (injective framing ⇒ no encoding-ambiguity collisions).
//!
//! * **`PRG` — the pseudorandom generator.** blake3's keyed mode / XOF, used to
//!   (a) evolve the forward-secure seed chain and (b) derive the VRF output. A
//!   seed is a 32-byte key; the label domain-separates the derivations.
//!
//! No secret-dependent branching lives here, but this reference is not audited
//! for constant-time behaviour — see the crate-level HONEST BOUNDARY.

/// Length of a hash / seed / output, in bytes (blake3's native 256-bit width).
pub const OUT_LEN: usize = 32;

/// A fixed-width 32-byte digest / seed.
pub type Bytes32 = [u8; OUT_LEN];

// ---- Domain-separation tags -------------------------------------------------
// Distinct one-byte prefixes keep the H-images of different structural roles
// disjoint. A leaf hash can never collide with an internal node hash by role.
const DOM_LEAF: u8 = 0x01;
const DOM_NODE: u8 = 0x02;

/// **`H` for a Merkle LEAF.** Binds the VRF output `y` and its opening `r` to a
/// specific epoch: `H(0x01 ‖ epoch ‖ y ‖ r)`. Fixed-width fields make the
/// encoding injective, so a collision here is a genuine blake3 collision.
///
/// This is the crux of the fix over X-VRF: the output is bound into the leaf by
/// a full collision-resistant hash, NOT by a WOTS+ chain (which is only
/// one-way / 2nd-preimage-resistant).
pub fn hash_leaf(epoch: u64, y: &Bytes32, r: &Bytes32) -> Bytes32 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[DOM_LEAF]);
    hasher.update(&epoch.to_le_bytes());
    hasher.update(y);
    hasher.update(r);
    *hasher.finalize().as_bytes()
}

/// **`H` for an internal Merkle NODE**: `H(0x02 ‖ left ‖ right)`. Fixed 32-byte
/// children ⇒ injective encoding.
pub fn hash_node(left: &Bytes32, right: &Bytes32) -> Bytes32 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[DOM_NODE]);
    hasher.update(left);
    hasher.update(right);
    *hasher.finalize().as_bytes()
}

/// **`PRG` → 32 bytes.** Keyed blake3 over a domain `label`: `PRG_seed(label)`.
/// Used for the forward-secure chain steps and the per-epoch key/output/opening
/// derivations. Different `label`s give independent-looking streams from one
/// seed.
pub fn prg32(seed: &Bytes32, label: &[u8]) -> Bytes32 {
    let mut hasher = blake3::Hasher::new_keyed(seed);
    hasher.update(label);
    *hasher.finalize().as_bytes()
}

/// **`PRG` → `n` bytes** via blake3's XOF. Used by the statistical
/// pseudorandomness smoke test to draw a long output stream from one key.
pub fn prg_xof(seed: &Bytes32, label: &[u8], n: usize) -> Vec<u8> {
    let mut hasher = blake3::Hasher::new_keyed(seed);
    hasher.update(label);
    let mut out = vec![0u8; n];
    hasher.finalize_xof().fill(&mut out);
    out
}
