//! ⚑ **READING A MINA DEFERRED-IPA-ACCUMULATOR FOLD ROOT.**
//!
//! The fold built in `dregg_circuit_prove::mina_accumulator_fold` produces a root whose exposed
//! claim is `acc_in(96) ‖ acc_out(96)` — two projective Vesta points in the sound 8-bit limb
//! encoding. Read end to end it says: *starting from the point `acc_in`, a chain of sound RCB
//! complete additions — every seam of it forced by a `.transition` window gate inside a leaf, and
//! every seam BETWEEN leaves forced by a `cb.connect` inside the recursion circuit — lands on
//! `acc_out`.*
//!
//! And when `acc_out` is the point at infinity, that sentence is
//! `Ipa.Step.accumulator_check`'s conclusion: `C − ⟨s(u⃗), G⟩ = O` with `C = acc_in`.
//!
//! ## ⚑ WHY THE READER LIVES HERE AND NOT IN THE PROVER CRATE
//!
//! The same reason [`crate::chain_root`] does: a node that CONSUMES a fold root must read the claim
//! without linking `dregg-circuit-prove`, and a second copy of the layout on the verify side is the
//! "two shapes that agree today" failure in its purest form. `mina_accumulator_fold` re-exports
//! these constants rather than restating them.
//!
//! ## ⚠ WHAT A VERIFIED ROOT DOES AND DOES NOT SAY
//!
//! It says the additions chain and (via [`AccumulatorClaim::is_identity`], or in-circuit via the
//! `-final` leaf's own 64 discharge gates) that the chain vanished. It says **nothing about what
//! the addends were** — forcing them to be the scaled SRS generators is the routing half, priced in
//! `MinaAccumulatorAir` §4. A consumer that reads this claim as "the accumulator check passed for
//! this block" is asserting the routing and the claim-to-head binding on its own authority; say
//! which, and do not let the word "verified" carry them.

use dregg_circuit::field::BabyBear;
use p3_field::PrimeField32;

use crate::config::DreggRecursionConfig;

/// Limbs per Pasta field element in the sound encoding (`PastaFieldSound.SK`).
pub const SK: usize = 32;
/// A projective point is three coordinates.
pub const POINT_COORDS: usize = 3;
/// The claim width of one projective Vesta point.
pub const POINT_WIDTH: usize = POINT_COORDS * SK;
/// Offset of the OUTGOING accumulator inside the claim (`MinaAccumulatorAir.ACC_OUT_PI 0`).
pub const CLAIM_OUT_LO: usize = POINT_WIDTH;
/// The claim every accumulator leaf and every fold node exposes: `acc_in ‖ acc_out`.
pub const ACC_CLAIM_LEN: usize = 2 * POINT_WIDTH;

/// The `op_type` of the non-primitive table a recursion root publishes its claim through.
pub const EXPOSE_CLAIM_OP: &str = "expose_claim";

/// The `acc_in ‖ acc_out` claim an accumulator leaf or fold node publishes, read back host-side.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccumulatorClaim {
    /// The 96 limbs of the projective point this sub-chain started from. In the accumulator check
    /// this is the claim's challenge-polynomial commitment `C`.
    pub acc_in: Vec<BabyBear>,
    /// The 96 limbs of the projective point this sub-chain ended on.
    pub acc_out: Vec<BabyBear>,
}

impl AccumulatorClaim {
    /// Coordinate `k` (`0 = X`, `1 = Y`, `2 = Z`) of the incoming point, as its `SK` little-endian
    /// 8-bit limbs.
    pub fn in_coord(&self, k: usize) -> Option<&[BabyBear]> {
        self.acc_in.get(k * SK..(k + 1) * SK)
    }

    /// …and of the outgoing point.
    pub fn out_coord(&self, k: usize) -> Option<&[BabyBear]> {
        self.acc_out.get(k * SK..(k + 1) * SK)
    }

    /// ⚑ **IS THE TERMINAL ACCUMULATOR THE POINT AT INFINITY?**
    ///
    /// `pasta_msm::is_identity` is `z == 0 && x == 0`, and this is that predicate on the published
    /// limbs. **Both** coordinates, because the AIR carries no on-curve gate — on the projective
    /// curve `Z = 0` forces `X = 0`, but only for points that are on it.
    ///
    /// ⚠ This is a HOST read of a published claim. It is the right check to make on a root whose
    /// leaves were all `dregg-mina-accumulator-seg::v1`; a root whose LAST leaf was
    /// `dregg-mina-accumulator-final::v1` has the same fact forced by that leaf's own 64
    /// `when_last_row` boundary gates, which is strictly stronger because no host has to remember
    /// to look. Say which one a given root has.
    pub fn is_identity(&self) -> bool {
        let zero = |c: usize| {
            self.out_coord(c)
                .is_some_and(|l| l.iter().all(|v| v.as_u32() == 0))
        };
        zero(0) && zero(2)
    }

    /// The Y coordinate of the terminal point is nonzero — which is what distinguishes the genuine
    /// projective identity `(0 : y : 0)` from an all-zero triple, and an all-zero triple is not a
    /// point at all. A root claiming the identity with `Y = 0` is malformed, not discharged.
    pub fn terminal_y_is_nonzero(&self) -> bool {
        self.out_coord(1)
            .is_some_and(|l| l.iter().any(|v| v.as_u32() != 0))
    }
}

/// Read the `acc_in ‖ acc_out` claim an accumulator leaf or fold node publishes.
///
/// ⚠ **This reads the proof's OWN published table, so it is only meaningful on a proof that has
/// been VERIFIED and whose circuit identity has been PINNED.** On an unverified proof the
/// `public_values` are whatever the prover wrote there.
pub fn read_accumulator_claim_from_proof(
    proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
) -> Option<AccumulatorClaim> {
    let claims: Vec<BabyBear> = proof
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == EXPOSE_CLAIM_OP)?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() != ACC_CLAIM_LEN {
        return None;
    }
    Some(AccumulatorClaim {
        acc_in: claims[..POINT_WIDTH].to_vec(),
        acc_out: claims[CLAIM_OUT_LO..CLAIM_OUT_LO + POINT_WIDTH].to_vec(),
    })
}

/// ⚑ **THE ENGINE EVERY LAYER ABOVE A LEAF RUNS AT** — every fold and the native verify of a
/// root. It is the fixed point of [`crate::config::recursion_layer_over`], i.e.
/// `create_recursion_config()`.
///
/// ⚠ It USED to be `ir2_leaf_wrap_config()`, because a leaf wrap inherited its child's FRI engine
/// and handed it to the whole tower. A leaf wrap now VERIFIES its child at that engine
/// (bit-for-bit unchanged) and MINTS at this one, so a root is a `(log_blowup 3, 38 query)`
/// proof. **Every consumer's pinned recursion VK rotates with it.**
pub fn accumulator_root_config() -> DreggRecursionConfig {
    crate::config::recursion_tower_root_config()
}

/// ⚑ **VERIFY AN ACCUMULATOR FOLD ROOT AND READ ITS CLAIM, IN THE ONLY ORDER THAT MEANS ANYTHING.**
///
/// 1. decode, 2. fingerprint, 3. **refuse unless the fingerprint IS the pinned anchor**,
/// 4. verify the STARK, 5. read the claim.
///
/// Step 3 before step 4 is deliberate, exactly as in [`crate::chain_root::verify_chain_root_bytes`]:
/// a root whose circuit identity is already wrong is refused without spending FRI, and a consumer
/// cannot accidentally read a claim off a proof of a DIFFERENT circuit that happens to verify.
pub fn verify_accumulator_root_bytes(
    bytes: &[u8],
    expected_vk: &crate::verify::RecursionVk,
) -> Result<AccumulatorClaim, String> {
    let proof = crate::verify::decode_recursive_batch_proof(bytes)?;
    let vk = crate::verify::recursion_vk_fingerprint(&proof);
    if vk != *expected_vk {
        return Err(format!(
            "accumulator root VK fingerprint is {}, but this consumer's pinned anchor is {}: this \
             is a proof of a DIFFERENT circuit",
            vk.to_hex(),
            expected_vk.to_hex()
        ));
    }
    crate::verify::verify_recursive_batch_proof_with_config(&proof, &accumulator_root_config())?;
    read_accumulator_claim_from_proof(&proof).ok_or_else(|| {
        format!(
            "the recursion root publishes no {ACC_CLAIM_LEN}-lane `{EXPOSE_CLAIM_OP}` claim; it \
             verifies but says nothing about a Mina accumulator chain"
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn claim(out: Vec<BabyBear>) -> AccumulatorClaim {
        AccumulatorClaim {
            acc_in: vec![BabyBear::new(7); POINT_WIDTH],
            acc_out: out,
        }
    }

    /// The layout has no aliasing and the two blocks are contiguous — which is what lets a leaf
    /// expose the continuity claim as ONE slice and a fold connect it with one loop.
    #[test]
    fn the_claim_layout_has_no_aliasing() {
        assert_eq!(POINT_WIDTH, 96);
        assert_eq!(CLAIM_OUT_LO, 96);
        assert_eq!(ACC_CLAIM_LEN, 192);
    }

    /// ⚑ BOTH POLARITIES of the identity read, including the malformed all-zero triple.
    #[test]
    fn the_identity_read_is_the_deployed_predicate() {
        let mut o = vec![BabyBear::new(0); POINT_WIDTH];
        o[SK] = BabyBear::new(3); // Y lane 0 nonzero — the genuine `(0 : y : 0)`
        let c = claim(o);
        assert!(c.is_identity());
        assert!(c.terminal_y_is_nonzero());

        // an all-zero triple is NOT a projective point; the identity read alone would accept it
        let z = claim(vec![BabyBear::new(0); POINT_WIDTH]);
        assert!(z.is_identity());
        assert!(
            !z.terminal_y_is_nonzero(),
            "an all-zero triple must be distinguishable from the point at infinity"
        );

        // a nonzero X refuses, and so does a nonzero Z — each on its own
        for bad in [0usize, 2 * SK] {
            let mut o = vec![BabyBear::new(0); POINT_WIDTH];
            o[SK] = BabyBear::new(3);
            o[bad] = BabyBear::new(1);
            assert!(
                !claim(o).is_identity(),
                "a nonzero limb at {bad} must refuse the identity read"
            );
        }
    }
}
