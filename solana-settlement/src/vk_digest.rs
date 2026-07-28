//! The VK commitment: a pin that is a FUNCTION OF THE KEY.
//!
//! ## What was wrong
//!
//! Until 2026-07-28 every chain in this repo pinned its "verifying-key
//! commitment" as `keccak256("dregg-settlement-vk-dev-setup")` -- a hash of a
//! LABEL (`solana-settlement/src/lib.rs::dev_ceremony_vk_hash`,
//! `chain/script/DeploySettlement.s.sol::DEFAULT_VK_HASH`,
//! `cosmos-settlement/tests/settlement.rs`). That value is
//! `0x18f57474785bdd93ff7feb573dfadff69516035997115f2854c93f0f31e1ff76` for the
//! dev key, for an MPC key, for a key an attacker generated, and for every key
//! anyone will ever generate: the string does not mention the key. So the one
//! artifact whose whole job is to notice a verifying key changed **could not
//! notice**, and a VK regeneration left all three chains' pins byte-identical.
//!
//! ## What it is now
//!
//! [`compute`] is keccak256 over a domain-tagged canonical serialization of the
//! ACTUAL key material in [`crate::vk`]:
//!
//! ```text
//! VK_DIGEST = keccak256(
//!       "dregg-groth16-vk/1"        // the spec schema; a schema bump moves it too
//!    || u32be(NUM_PUBLIC_INPUTS)    // 25
//!    || u32be(PUB.len())            // 26 IC bases
//!    || ALPHA_G1                    // 64  = X || Y, 32-byte big-endian each
//!    || BETA_NEG_G2                 // 128 = X_c1 || X_c0 || Y_c1 || Y_c0 (EIP-197)
//!    || GAMMA_NEG_G2 || DELTA_NEG_G2
//!    || PEDERSEN_G_G2 || PEDERSEN_GSIGMA_G2
//!    || CONSTANT_G1                 // 64
//!    || PUB[0] .. PUB[25]           // 64 each
//! )                                 // 2458 bytes of preimage
//! ```
//!
//! The G2 points are stored pre-negated; negation is a bijection on the group, so
//! digesting the stored form binds the key exactly as tightly as digesting the
//! original would. The identical bytes are hashed by
//! `chain/contracts/DreggSettlementVK.digest()` on the EVM and emitted into
//! `cosmos-settlement/src/vk.rs`, all three from the one spec
//! `chain/codegen/dregg_vk.json`.
//!
//! The claim this module has to earn is in `tests/vk_pin.rs`: flipping ANY bit of
//! ANY verifying-key byte moves the pin, and the old label hash does not move for
//! any of them.

use solana_program::keccak;

use crate::vk;

/// Domain tag = the `schema` field of `chain/codegen/dregg_vk.json`.
pub const DIGEST_DOMAIN: &[u8] = b"dregg-groth16-vk/1";

/// A borrowed view of Groth16 verifying-key material, in the digest's pinned
/// order. Borrowed (rather than reading [`crate::vk`] directly) so a test can
/// digest a PERTURBED key and show the pin moves -- the property the old
/// label hash could not have.
pub struct VkMaterial<'a> {
    pub num_public_inputs: u32,
    pub num_ic_bases: u32,
    pub alpha_g1: &'a [u8; 64],
    pub beta_neg_g2: &'a [u8; 128],
    pub gamma_neg_g2: &'a [u8; 128],
    pub delta_neg_g2: &'a [u8; 128],
    pub pedersen_g_g2: &'a [u8; 128],
    pub pedersen_gsigma_g2: &'a [u8; 128],
    pub constant_g1: &'a [u8; 64],
    pub pub_g1: &'a [[u8; 64]],
}

/// The verifying key this program actually verifies against.
pub fn deployed() -> VkMaterial<'static> {
    VkMaterial {
        num_public_inputs: vk::NUM_PUBLIC_INPUTS as u32,
        num_ic_bases: vk::PUB.len() as u32,
        alpha_g1: &vk::ALPHA_G1,
        beta_neg_g2: &vk::BETA_NEG_G2,
        gamma_neg_g2: &vk::GAMMA_NEG_G2,
        delta_neg_g2: &vk::DELTA_NEG_G2,
        pedersen_g_g2: &vk::PEDERSEN_G_G2,
        pedersen_gsigma_g2: &vk::PEDERSEN_GSIGMA_G2,
        constant_g1: &vk::CONSTANT_G1,
        pub_g1: &vk::PUB,
    }
}

/// keccak256 over the canonical serialization of `m` (see the module docs).
pub fn digest_of(m: &VkMaterial<'_>) -> [u8; 32] {
    let n_pub = m.num_public_inputs.to_be_bytes();
    let n_ic = m.num_ic_bases.to_be_bytes();
    let mut parts: Vec<&[u8]> = Vec::with_capacity(10 + m.pub_g1.len());
    parts.push(DIGEST_DOMAIN);
    parts.push(&n_pub);
    parts.push(&n_ic);
    parts.push(m.alpha_g1);
    parts.push(m.beta_neg_g2);
    parts.push(m.gamma_neg_g2);
    parts.push(m.delta_neg_g2);
    parts.push(m.pedersen_g_g2);
    parts.push(m.pedersen_gsigma_g2);
    parts.push(m.constant_g1);
    for p in m.pub_g1 {
        parts.push(p);
    }
    keccak::hashv(&parts).0
}

/// The digest of the deployed key. Equal to the generated [`vk::VK_DIGEST`] --
/// asserted in `tests/vk_pin.rs`, which is what makes the generated constant a
/// measurement of the key rather than an assertion about it.
pub fn compute() -> [u8; 32] {
    digest_of(&deployed())
}
