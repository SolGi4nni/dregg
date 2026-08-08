//! ⚑ **READING A KIMCHI-VERIFIER-GADGET ROOT.**
//!
//! The fold built in `dregg_circuit_prove::mina_kimchi_verifier_gadget` produces a root whose
//! exposed claim is
//!
//! ```text
//!   transcript_acc(8) ‖ v'(32) ‖ zeta(32) ‖ zetaw(32) ‖ r(32) ‖ b0(32)      = 168 lanes
//! ```
//!
//! and read end to end it says, **at this tree's resolution and not at the name's**:
//!
//! > Starting from a FRESH Kimchi `fq_sponge` `(0,0,0)`, absorbing exactly the ordered tape that
//! > `transcript_acc` commits to, the squeezed prechallenge is `v′`; `ScalarChallenge(v′)`'s
//! > endomorphism lift is a ξ; and against THAT ξ, this ζ, this ζω and this evalscale `r`, the
//! > published `b0` equals `bEval ζ chals + r · bEval ζω chals` for the fifteen IPA challenges the
//! > conjunction's own rows supplied, each welded to its inverse.
//!
//! ⚠ **IT IS NOT "THIS KIMCHI PROOF IS VALID".** `dregg_circuit_prove::mina_kimchi_verifier_gadget`
//! §"WHAT THE ROOT DOES NOT SAY" lists **five** items and they are not summarised away here. Two of
//! them bind a CONSUMER of this module and so are repeated:
//!
//! * ⚑ **The root is QUANTIFIED over the tape — nothing in the circuit names a block.** What names
//!   one is comparing [`KimchiClaim::transcript_acc`] against the host mirror over that block's real
//!   tape (`dregg_circuit_prove::mina_phase2_chain_leaf::host_chain_transcript_acc`). A consumer
//!   that verifies the root and skips that comparison holds a claim about *some* tape.
//! * ⚑ **The children's VK identities are not pinned in-circuit.** `into_recursion_input` passes
//!   `expected_preprocessed_commit: None`, so a child of identical table shape and different
//!   preprocessed content is not excluded by the fold itself. [`verify_kimchi_root_bytes`]'s
//!   fingerprint check pins the ROOT's circuit and nothing below it.
//!
//! The other three are about strength: the IPA opening is not in circuit
//! (`opening_is_vacuous_when_sg_is_free`), `cipCorrect` / `plonkChecksPassed` are absent by
//! construction, and ζ / ζω / `r` are published and derived by nothing.
//!
//! # ⚑ WHY A THIRD CLAIM LENGTH, AND WHY IT IS CHECKED
//!
//! Three different roots ride the SAME `DreggRecursionConfig` and publish through the same
//! `expose_claim` table: the phase-2 chain root (200 lanes), the endo/conjunction finalize root
//! (160), and this one (168). A consumer picks a reader by LENGTH. Two roots at one length would
//! be a claim read as the wrong sentence — "a theorem true about the wrong object" — so the
//! lengths are pinned pairwise-distinct by a `const _: () = assert!(..)` below, at compile time.

use dregg_circuit::field::BabyBear;
use p3_field::PrimeField32;

use crate::chain_root::{ACC_WIDTH, CHAIN_CLAIM_LEN, EXPOSE_CLAIM_OP, SK};
use crate::config::DreggRecursionConfig;

/// Claim offset of the ordered transcript commitment carried up from the chain root.
pub const KV_ACC: usize = 0;
/// …of `v′`, the block's polyscale PRECHALLENGE — 128 bits in `SK` limbs, high 16 pinned zero.
pub const KV_VPRIME: usize = ACC_WIDTH;
/// …of ζ.
pub const KV_ZETA: usize = KV_VPRIME + SK;
/// …of ζω.
pub const KV_ZETAW: usize = KV_ZETA + SK;
/// …of the evalscale `r`.
pub const KV_R: usize = KV_ZETAW + SK;
/// …of the claimed `b0`.
pub const KV_B0: usize = KV_R + SK;
/// `transcript_acc(8) ‖ v'(32) ‖ zeta(32) ‖ zetaw(32) ‖ r(32) ‖ b0(32)`.
pub const KIMCHI_CLAIM_LEN: usize = KV_B0 + SK;

/// The claim length of the endo/conjunction finalize root this gadget consumes as its RIGHT child.
///
/// Declared here rather than imported from the prover crate on purpose: this crate must be able to
/// state the disambiguation below without depending on `dregg-circuit-prove`.
/// `dregg_circuit_prove::mina_kimchi_verifier_gadget` pins it against
/// `mina_wrap_finalize_fold::FINALIZE_CLAIM_LEN` with a `const _`, so the two sources agree or the
/// build fails.
pub const FINALIZE_CLAIM_LEN: usize = 5 * SK;

// ⚑ THE DISAMBIGUATION, AT COMPILE TIME. A consumer selects a claim reader by LENGTH; two roots
// sharing one length is a claim read as the wrong sentence, silently.
const _: () = assert!(KIMCHI_CLAIM_LEN != CHAIN_CLAIM_LEN);
const _: () = assert!(KIMCHI_CLAIM_LEN != FINALIZE_CLAIM_LEN);
const _: () = assert!(CHAIN_CLAIM_LEN != FINALIZE_CLAIM_LEN);

/// The claim a kimchi-verifier-gadget root publishes, read back host-side.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KimchiClaim {
    /// The ordered commitment to every element the block's phase-2 tape absorbed.
    pub transcript_acc: [BabyBear; ACC_WIDTH],
    /// The polyscale prechallenge, DERIVED in-circuit from the chain root's terminal squeeze.
    pub v_prime: Vec<BabyBear>,
    /// ζ — published by the conjunction, derived by nothing.
    pub zeta: Vec<BabyBear>,
    /// ζω — published by the conjunction, derived by nothing.
    pub zeta_w: Vec<BabyBear>,
    /// The evalscale `r` — published by the conjunction, derived by nothing.
    pub r: Vec<BabyBear>,
    /// The claimed `b0` the conjunction's `bCorrect` forces against `PastaIPA.bEval`.
    pub b0: Vec<BabyBear>,
}

impl KimchiClaim {
    /// `v′` as the 128-bit integer its low `V_PRIME_LIMBS` limbs encode.
    ///
    /// Returns `None` if any of the high limbs is non-zero — a `v′` with high limbs set is a
    /// DIFFERENT prechallenge in the same 32-limb slot, and reading it as 128 bits would silently
    /// truncate. The gadget pins those limbs to zero in-circuit, so a root that fails this check
    /// is not one this gadget produced.
    pub fn v_prime_u128(&self) -> Option<u128> {
        if self.v_prime.len() != SK {
            return None;
        }
        if self.v_prime[V_PRIME_LIMBS..]
            .iter()
            .any(|v| v.as_u32() != 0)
        {
            return None;
        }
        let mut acc: u128 = 0;
        for (i, limb) in self.v_prime[..V_PRIME_LIMBS].iter().enumerate() {
            let byte = limb.as_u32();
            if byte > 0xFF {
                return None;
            }
            acc |= (byte as u128) << (8 * i);
        }
        Some(acc)
    }
}

/// `v′ = LINK_V_RAW % 2^128`, and `128 / 8 = 16`.
pub const V_PRIME_LIMBS: usize = 16;

/// Read the kimchi-verifier claim a gadget root publishes.
///
/// ⚠ **This reads the proof's OWN published table, so it is only meaningful on a proof that has
/// been VERIFIED and whose circuit identity has been PINNED.** On an unverified proof the
/// `public_values` are whatever the prover wrote there.
pub fn read_kimchi_claim_from_proof(
    proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
) -> Option<KimchiClaim> {
    let claims: Vec<BabyBear> = proof
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == EXPOSE_CLAIM_OP)?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() != KIMCHI_CLAIM_LEN {
        return None;
    }
    let mut acc = [BabyBear::new(0); ACC_WIDTH];
    acc.copy_from_slice(&claims[KV_ACC..KV_ACC + ACC_WIDTH]);
    let block = |lo: usize| claims[lo..lo + SK].to_vec();
    Some(KimchiClaim {
        transcript_acc: acc,
        v_prime: block(KV_VPRIME),
        zeta: block(KV_ZETA),
        zeta_w: block(KV_ZETAW),
        r: block(KV_R),
        b0: block(KV_B0),
    })
}

/// ⚑ **VERIFY A KIMCHI-VERIFIER ROOT AND READ ITS CLAIM, IN THE ONLY ORDER THAT MEANS ANYTHING.**
///
/// 1. decode, 2. fingerprint, 3. **refuse unless the fingerprint IS the pinned anchor**,
/// 4. verify the STARK, 5. read the claim.
///
/// Step 3 before step 4 is deliberate, for the same reason
/// [`crate::chain_root::verify_chain_root_bytes`] gives: a consumer must not read a claim off a
/// proof of a DIFFERENT circuit that happens to verify.
pub fn verify_kimchi_root_bytes(
    bytes: &[u8],
    expected_vk: &crate::verify::RecursionVk,
) -> Result<KimchiClaim, String> {
    let proof = crate::verify::decode_recursive_batch_proof(bytes)?;
    let vk = crate::verify::recursion_vk_fingerprint(&proof);
    if vk != *expected_vk {
        return Err(format!(
            "recursion root VK fingerprint is {}, but this consumer's pinned anchor is {}: this \
             is a proof of a DIFFERENT circuit",
            vk.to_hex(),
            expected_vk.to_hex()
        ));
    }
    crate::verify::verify_recursive_batch_proof_with_config(&proof, &kimchi_root_config())?;
    read_kimchi_claim_from_proof(&proof).ok_or_else(|| {
        format!(
            "the recursion root publishes no {KIMCHI_CLAIM_LEN}-lane `{EXPOSE_CLAIM_OP}` claim; it \
             verifies but says nothing about a Kimchi transcript"
        )
    })
}

/// ⚑ **THE ENGINE THE KIMCHI GADGET'S FOLD RUNS AT, AND THE ONE ITS ROOT VERIFIES UNDER.**
///
/// The gadget's two children are ROOTS — a phase-2 chain root and an endo/conjunction finalize
/// root — and both are minted at [`crate::config::recursion_tower_root_config`]'s engine since the
/// leaf-wrap mint split reached these towers. `recursion_layer_over` of that engine is that engine
/// (it is the fixed point), so the gadget verifies its children at it, mints at it, and the root is
/// read back under it. One object, three roles, and they coincide here because the fixed point is
/// what a fixed point is — not because a coincidence was left standing.
///
/// ⚠ It USED to be `ir2_leaf_wrap_config()`. **The gadget root's VK rotates.**
pub fn kimchi_root_config() -> DreggRecursionConfig {
    crate::config::recursion_tower_root_config()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The claim layout has no aliasing and the three root shapes are pairwise distinguishable.
    #[test]
    fn the_kimchi_claim_layout_has_no_aliasing() {
        assert_eq!(KV_ACC, 0);
        assert_eq!(KV_VPRIME, 8);
        assert_eq!(KV_ZETA, 40);
        assert_eq!(KV_ZETAW, 72);
        assert_eq!(KV_R, 104);
        assert_eq!(KV_B0, 136);
        assert_eq!(KIMCHI_CLAIM_LEN, 168);
        // Every block is exactly one Pasta field element wide, and they tile the claim.
        assert_eq!(KV_B0 + SK, KIMCHI_CLAIM_LEN);
        // …and the three root shapes a consumer discriminates by length really are distinct.
        assert_ne!(KIMCHI_CLAIM_LEN, CHAIN_CLAIM_LEN);
        assert_ne!(KIMCHI_CLAIM_LEN, FINALIZE_CLAIM_LEN);
    }

    /// `v_prime_u128` reads the low 16 limbs little-endian and REFUSES a set high limb, which is
    /// the whole reason the gadget pins those limbs rather than ignoring them.
    #[test]
    fn v_prime_reads_low_128_bits_and_refuses_a_set_high_limb() {
        let mut c = KimchiClaim {
            transcript_acc: [BabyBear::new(0); ACC_WIDTH],
            v_prime: vec![BabyBear::new(0); SK],
            zeta: vec![BabyBear::new(0); SK],
            zeta_w: vec![BabyBear::new(0); SK],
            r: vec![BabyBear::new(0); SK],
            b0: vec![BabyBear::new(0); SK],
        };
        c.v_prime[0] = BabyBear::new(0xAB);
        c.v_prime[15] = BabyBear::new(0x01);
        assert_eq!(c.v_prime_u128(), Some(0xAB | (1u128 << 120)));

        // One set limb above the 128-bit window and the read REFUSES rather than truncating.
        c.v_prime[16] = BabyBear::new(1);
        assert_eq!(c.v_prime_u128(), None);
    }
}
