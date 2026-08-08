//! ⚑ **READING A MINA PHASE-2 CHAIN-FOLD ROOT.**
//!
//! The fold built in `dregg_circuit_prove::mina_phase2_chain_leaf` produces a root whose
//! exposed claim is `in_state(96) ‖ out_state(96) ‖ transcript_acc(8)`. Read end to end that
//! claim says: *starting from the sponge state `in_state`, absorbing exactly the tape
//! `transcript_acc` commits to, a chain of `absorbProg` executions lands on `out_state`.*
//!
//! ⚑ **A ROOT IS NOT A DESCRIPTOR, AND THAT IS WHY THIS MODULE EXISTS.** Every other proof a
//! dregg consumer checks is an IR-v2 batch over a NAMED descriptor, and its identity is
//! `effect_vm_descriptor2_semantic_fingerprint` of descriptor JSON — bytes the consumer holds.
//! A recursion root has no descriptor: its identity is [`crate::verify::recursion_vk_fingerprint`]
//! of the PROOF, extracted once from an honest fold and pinned. So a carrier that attests a root
//! needs a second SHAPE (a fingerprint pin plus a claim read), not a second value in the old one.
//!
//! This module is the READ half only. The policy — *which* fingerprint is trusted, and what the
//! claim must say — belongs to the consumer, because it is the consumer that holds the trust
//! anchor. `dregg_turn::executor::mina_head_verifier` is the first such consumer.

use dregg_circuit::field::BabyBear;
use p3_field::PrimeField32;

use crate::config::DreggRecursionConfig;

/// Limbs per Pasta field element (`PastaFieldSound.SK`).
pub const SK: usize = 32;
/// A Poseidon sponge state is three lanes.
pub const STATE_LANES: usize = 3;
/// The claim width of one whole sponge state.
pub const STATE_WIDTH: usize = STATE_LANES * SK;
/// Width of the ordered transcript commitment carried in the claim.
///
/// ⚑ Pinned against `dregg_circuit_prove::ivc_turn_chain::SEG_DIGEST_WIDTH` by a
/// `const _: () = assert!(..)` in `mina_phase2_chain_leaf.rs`. Two INDEPENDENT sources that must
/// agree is a gate; a constant checked against its own definition would be decoration.
pub const ACC_WIDTH: usize = 8;
/// Offset of the transcript accumulator inside the claim.
pub const CLAIM_ACC_LO: usize = 2 * STATE_WIDTH;
/// The claim every chain leaf and every fold node exposes.
pub const CHAIN_CLAIM_LEN: usize = 2 * STATE_WIDTH + ACC_WIDTH;
/// Mina devnet block 539508's phase-2 tape is 91 elements at rate 2 — 45 arrival permutations
/// plus the closing squeeze.
pub const CHAIN_LINKS: usize = 46;

/// The `op_type` of the non-primitive table a recursion root publishes its claim through.
pub const EXPOSE_CLAIM_OP: &str = "expose_claim";

/// The claim a chain leaf or fold node publishes, read back host-side.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainClaim {
    /// The 96 limbs of the sponge state the FIRST link of this sub-chain consumed.
    pub in_state: Vec<BabyBear>,
    /// The 96 limbs of the sponge state the LAST link of this sub-chain produced.
    pub out_state: Vec<BabyBear>,
    /// The ordered commitment to every element this sub-chain absorbed.
    pub transcript_acc: [BabyBear; ACC_WIDTH],
}

impl ChainClaim {
    /// True iff the chain started from a FRESH Kimchi sponge `(0,0,0)`.
    ///
    /// A root that starts anywhere else proves a sentence about a transcript prefix nobody
    /// checked — the prover picked the starting state.
    pub fn starts_from_a_fresh_sponge(&self) -> bool {
        self.in_state.iter().all(|v| v.as_u32() == 0)
    }

    /// Lane `i` of the outgoing sponge state, as its `SK` little-endian 8-bit limbs.
    pub fn out_lane(&self, i: usize) -> Option<&[BabyBear]> {
        self.out_state.get(i * SK..(i + 1) * SK)
    }
}

/// Read the `in_state ‖ out_state ‖ transcript_acc` claim a chain leaf or fold node publishes.
///
/// ⚠ **This reads the proof's OWN published table, so it is only meaningful on a proof that has
/// been VERIFIED and whose circuit identity has been PINNED.** On an unverified proof the
/// `public_values` are whatever the prover wrote there.
pub fn read_chain_claim_from_proof(
    proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
) -> Option<ChainClaim> {
    let claims: Vec<BabyBear> = proof
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == EXPOSE_CLAIM_OP)?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() != CHAIN_CLAIM_LEN {
        return None;
    }
    let mut acc = [BabyBear::new(0); ACC_WIDTH];
    acc.copy_from_slice(&claims[CLAIM_ACC_LO..CLAIM_ACC_LO + ACC_WIDTH]);
    Some(ChainClaim {
        in_state: claims[..STATE_WIDTH].to_vec(),
        out_state: claims[STATE_WIDTH..2 * STATE_WIDTH].to_vec(),
        transcript_acc: acc,
    })
}

/// ⚑ **THE ENGINE EVERY LAYER ABOVE A CHAIN LEAF RUNS AT** — all 45 folds and the native verify of
/// the root. The fixed point of [`crate::config::recursion_layer_over`].
///
/// ⚠ It USED to be `ir2_leaf_wrap_config()`, because this tower was left whole when the IR-v2 leaf
/// wrap's mint was split: one config played the leaf's verify role, the leaf's mint role, every
/// fold's, and the root verify's, and it played them all at the CHILD's `log_blowup 6`. A chain
/// leaf now VERIFIES its IR-v2 child at that engine (bit-for-bit unchanged — the same
/// `Ir2BatchProof` bytes, the same in-circuit verifier) and MINTS at this one, so a chain root is a
/// `(log_blowup 3, 38 query)` proof. **Every consumer's pinned chain-root VK rotates with it**,
/// including an operator's `DREGG_MINA_CHAIN_ROOT_VK`.
///
/// ⚑ RE-EXPORTED shape, not a fourth answer: `dregg_circuit_prove::mina_phase2_chain_leaf`
/// re-exports this rather than defining its own, because a prove-side and a verify-side "what
/// config is a root at" that agree today are two answers that disagree the first time one is
/// retuned — and both sides would still BUILD; only the FRI would refuse.
pub fn chain_root_config() -> DreggRecursionConfig {
    crate::config::recursion_tower_root_config()
}

/// ⚑ **VERIFY A CHAIN ROOT AND READ ITS CLAIM, IN THE ONLY ORDER THAT MEANS ANYTHING.**
///
/// 1. decode, 2. fingerprint, 3. **refuse unless the fingerprint IS the pinned anchor**,
/// 4. verify the STARK, 5. read the claim.
///
/// Step 3 before step 4 is deliberate: a root whose circuit identity is already wrong is refused
/// without spending FRI, and — more importantly — a consumer cannot accidentally read a claim
/// off a proof of a DIFFERENT circuit that happens to verify.
pub fn verify_chain_root_bytes(
    bytes: &[u8],
    expected_vk: &crate::verify::RecursionVk,
) -> Result<ChainClaim, String> {
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
    crate::verify::verify_recursive_batch_proof_with_config(&proof, &chain_root_config())?;
    read_chain_claim_from_proof(&proof).ok_or_else(|| {
        format!(
            "the recursion root publishes no {CHAIN_CLAIM_LEN}-lane `{EXPOSE_CLAIM_OP}` claim; it \
             verifies but says nothing about a Mina phase-2 transcript"
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The claim layout has no aliasing and matches the Lean-emitted chain-link pin layout.
    #[test]
    fn the_chain_claim_layout_has_no_aliasing() {
        assert_eq!(STATE_WIDTH, 96);
        assert_eq!(CLAIM_ACC_LO, 192);
        assert_eq!(CHAIN_CLAIM_LEN, 200);
        assert_eq!(CHAIN_LINKS, 46);
    }

    /// A fresh sponge is all-zero and a non-fresh one is not — the predicate the whole
    /// "the chain started nowhere in particular" refusal rests on.
    #[test]
    fn the_fresh_sponge_predicate_has_both_polarities() {
        let acc = [BabyBear::new(0); ACC_WIDTH];
        let fresh = ChainClaim {
            in_state: vec![BabyBear::new(0); STATE_WIDTH],
            out_state: vec![BabyBear::new(0); STATE_WIDTH],
            transcript_acc: acc,
        };
        assert!(fresh.starts_from_a_fresh_sponge());
        let mut warm = fresh.clone();
        warm.in_state[95] = BabyBear::new(1);
        assert!(!warm.starts_from_a_fresh_sponge());
    }

    /// Lane slicing is in range for the three lanes and out of range past them.
    #[test]
    fn out_lane_slices_the_three_lanes() {
        let c = ChainClaim {
            in_state: vec![BabyBear::new(0); STATE_WIDTH],
            out_state: (0..STATE_WIDTH as u32).map(BabyBear::new).collect(),
            transcript_acc: [BabyBear::new(0); ACC_WIDTH],
        };
        assert_eq!(c.out_lane(0).map(<[_]>::len), Some(SK));
        assert_eq!(c.out_lane(2).map(<[_]>::len), Some(SK));
        assert!(c.out_lane(3).is_none());
        assert_eq!(c.out_lane(1).unwrap()[0].as_u32(), SK as u32);
    }
}
