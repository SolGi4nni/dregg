//! ⚑⚑ **THE 46-PERMUTATION Fq TRANSCRIPT OF A REAL MINA BLOCK, AS A RECURSION TREE.**
//!
//! Every note in this campaign that hit the transcript's size wall named a residual instead of
//! recursing. `MinaBlockFqTranscript` §6.1 was the last of them, and it named the fix precisely:
//!
//! > *"a chain of 46 instances welded by input/output pin equality is the shape that closes it,
//! > **and it is not built here.**"*
//!
//! It is built here. This module is the Rust HALF of that: the Lean-authored
//! `dregg-pasta-fq-chainlink::v1` descriptor (`Dregg2.Circuit.Emit.MinaPhase2Chain`) proven as a
//! recursion LEAF, and a 2-to-1 FOLD that carries the sponge state from link `j` to link `j+1`
//! **inside the recursion circuit**. Not one AIR constraint is authored in Rust: the descriptor,
//! its pins, its ROM and its witnesses all come out of Lean. House Law #1.
//!
//! ## ⚑ WHAT MAKES THIS A CLAIM AND NOT 46 PROOFS
//!
//! The residual a naive fold would leave was stated for us:
//!
//! > *"A fold that just re-pins the same public inputs 46 times closes nothing. The chain must
//! > carry state from leaf `i` to leaf `i+1` inside the recursion, so the last leaf's output is a
//! > consequence of the first leaf's input."*
//!
//! Two things are therefore carried, and both are read from each child's OWN FRI-bound public
//! targets — never from a free prover scalar:
//!
//! 1. **The state carry.** [`fold_chain_links`] `cb.connect`s the left child's 96 OUTGOING state
//!    limbs to the right child's 96 INCOMING state limbs. A prover that hands on a state the left
//!    link did not compute makes the aggregation UNSAT: there is no root. This is why the deployed
//!    seven-block descriptor could not be chained — it pinned only 2 of the 3 outgoing lanes, so a
//!    third of the handed-on state would have been free. `MinaPhase2Chain.chainPins` pins all three
//!    (`allocAt 55 = (4, 5, 0)`, `the_outgoing_lanes_are_registers_4_5_0`).
//!
//! 2. **The absorbed tape.** A chain that only connects endpoints proves *"46 honest links run from
//!    (0,0,0) to this state"* and says nothing about WHAT was absorbed — a prover could absorb 91
//!    numbers of its choosing. So each leaf commits IN-CIRCUIT to its own absorbed pair
//!    ([`seg_poseidon_commit`] over the leaf's 64 bound absorbed limbs), and each fold folds the two
//!    children's commitments into an ordered parent digest. The root's digest is compared host-side
//!    against [`host_chain_transcript_acc`] over the block's REAL tape. `Dregg2`'s
//!    `the_chain_absorbs_the_tape_in_order` is the statement that comparison is about.
//!
//! ⇒ the root claim is `in_state(96) ‖ out_state(96) ‖ transcript_acc(8)`, and read end to end it
//! says: *starting from a fresh Kimchi sponge, absorbing exactly this ordered tape, 46 emitted
//! `absorbProg` executions chain to this state* — whose first two lanes' low 128 bits are the `v′`
//! and `u′` that Mina devnet block 539508's own `proof.oracles(…)` returned.
//!
//! ## THE FOLD SHAPE
//!
//! A **left-leaning sequential** fold, `acc_{k+1} = node(acc_k, leaf_{k+1})`, mirrored host-side by
//! [`host_chain_transcript_fold`]. Sequential rather than balanced deliberately: the host mirror is
//! then a two-line loop rather than a tree the host must reproduce shape-for-shape, and a
//! shape-mismatched mirror is exactly the class of silent disagreement this repo keeps finding.
//! The node count is 45 either way.
//!
//! ## WHAT THIS DOES NOT ESTABLISH
//!
//! **Not that the transcript is a tracked head's.** The chain proves the tape absorbs to the
//! published challenges. No gate here relates a light client's `TIP_STATE` to the block whose tape
//! this is; that is `LightClientMinaAir`'s business.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2Air, MemBoundaryWitness, UMemBoundaryWitness,
    ir2_airs_and_common_for_config, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;

use p3_recursion::{BatchOnly, RecursionInput, RecursionOutput, Target};

use crate::gpu_backend::{
    prove_recursion_aggregation_auto_with_expose, prove_recursion_layer_auto_with_expose,
};
use crate::ivc_turn_chain::{
    SEG_DIGEST_WIDTH, expose_claim_instance_index, ir2_leaf_wrap_config, seg_poseidon_commit,
    seg_poseidon_commit_host,
};
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;

type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

/// The Lean-emitted chain-link descriptor. ONE descriptor serves all 46 links — the residual really
/// was witnesses and not an algebra.
const CHAINLINK_DESC_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/pasta-fq-chainlink.json");

// ⚑ THE CLAIM SHAPE AND ITS READER LIVE IN `dregg-recursion-verify`, NOT HERE. A node that
// consumes a fold ROOT must read the claim without linking this crate; a second copy of the
// layout on the verify side is the "two shapes that agree today" failure in its purest form. The
// PI layout below (which is about the LEAF's descriptor public inputs) stays, because only a
// prover needs it.
pub use dregg_recursion_verify::chain_root::{
    ACC_WIDTH, CHAIN_CLAIM_LEN, CHAIN_LINKS, CLAIM_ACC_LO, ChainClaim, SK, STATE_LANES,
    STATE_WIDTH, read_chain_claim_from_proof,
};

/// ⚑ TWO INDEPENDENT SOURCES, PINNED. `ACC_WIDTH` is the verify crate's statement of the
/// transcript-accumulator width; `SEG_DIGEST_WIDTH` is the prover's. A constant checked against
/// its own definition is decoration — this is the other kind.
const _: () = assert!(ACC_WIDTH == SEG_DIGEST_WIDTH);

/// PI offset of the INCOMING state block (`MinaPhase2Chain.inBlock`).
pub const IN_PI_LO: usize = 0;
/// PI offset of the OUTGOING state block (`MinaPhase2Chain.outBlock`).
pub const OUT_PI_LO: usize = STATE_WIDTH;
/// PI offset of the absorbed pair (`MinaPhase2Chain.absorbedBlock`).
pub const ABSORBED_PI_LO: usize = 2 * STATE_WIDTH;
/// Two absorbed elements at rate 2.
pub const ABSORBED_WIDTH: usize = 2 * SK;
/// `MinaPhase2Chain.CHAIN_PI_COUNT`.
pub const CHAIN_PI_COUNT: usize = ABSORBED_PI_LO + ABSORBED_WIDTH;

/// Parse the Lean-emitted chain-link descriptor. Rust authors none of it.
pub fn chain_link_descriptor() -> Result<EffectVmDescriptor2, String> {
    let desc = parse_vm_descriptor2(CHAINLINK_DESC_JSON)
        .map_err(|e| format!("chain-link descriptor parse failed: {e}"))?;
    if desc.public_input_count != CHAIN_PI_COUNT {
        return Err(format!(
            "chain-link descriptor declares {} PIs, expected {CHAIN_PI_COUNT}; refusing an \
             ambiguous pin layout",
            desc.public_input_count
        ));
    }
    Ok(desc)
}

/// ⚑ **THE LEAF.** Prove one Lean-emitted link as a foldable recursion leaf, exposing
/// `in_state(96) ‖ out_state(96) ‖ commit(absorbed_pair)(8)`.
///
/// Every exposed lane is read from the leaf's OWN verified `air_public_targets` — the descriptor
/// PIs the inner batch proof binds — so a prover cannot expose a state or an absorbed pair that
/// disagrees with the execution it just proved.
pub fn prove_chain_link_leaf(
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != CHAIN_PI_COUNT {
        return Err(format!(
            "a chain link carries exactly {CHAIN_PI_COUNT} public inputs, got {}",
            public_inputs.len()
        ));
    }
    let desc = chain_link_descriptor()?;

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("chain-link inner IR-v2 prove failed: {e}"))?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &inner, public_inputs, config)
            .map_err(|e| format!("chain-link verify-triple build failed: {e}"))?;

    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &inner,
            common_data: &common,
            table_public_inputs,
        };

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<Target>],
                       _vk_cap: &[Target]| {
        let main = apt
            .first()
            .expect("chain link has a main instance carrying the descriptor PIs");
        debug_assert!(
            main.len() >= CHAIN_PI_COUNT,
            "main instance must carry all {CHAIN_PI_COUNT} chain-link PI slots"
        );
        // The continuity claim: `in ‖ out` is CONTIGUOUS by the Lean pin layout, so this is one
        // slice rather than two — the layout was chosen for exactly this.
        let mut claim: Vec<Target> = (0..2 * STATE_WIDTH).map(|k| main[IN_PI_LO + k]).collect();
        // …and the transcript commitment, over the leaf's own BOUND absorbed limbs.
        let absorbed: Vec<Target> = (0..ABSORBED_WIDTH)
            .map(|k| main[ABSORBED_PI_LO + k])
            .collect();
        claim.extend_from_slice(&seg_poseidon_commit(cb, &absorbed));
        debug_assert_eq!(claim.len(), CHAIN_CLAIM_LEN);
        cb.expose_as_public_output(&claim);
    };

    prove_recursion_layer_auto_with_expose(&input, config, Some(&expose))
        .map_err(|e| format!("chain-link leaf wrap failed: {e}"))
}

/// ⚑⚑ **THE FOLD — WHERE THE STATE IS CARRIED, INSIDE THE RECURSION.**
///
/// Verifies both children in-circuit and then:
///
/// * `connect(left.out_state[k], right.in_state[k])` for all 96 limbs — **the carry.** A prover
///   whose right link starts from a state the left link did not produce has no satisfying
///   assignment, so there is no parent proof. This is the whole difference between 46 proofs and
///   one claim.
/// * `parent.transcript_acc = commit(left.acc ‖ right.acc)` — order-sensitive, so the two halves
///   cannot be swapped.
/// * exposes `left.in_state ‖ right.out_state ‖ parent.acc` — the same 200-lane shape a leaf
///   exposes, which is what makes the node composable with itself to any depth.
pub fn fold_chain_links(
    left: &RecursionOutput<DreggRecursionConfig>,
    right: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let left_idx = require_chain_claim(left, "left sub-chain")?;
    let right_idx = require_chain_claim(right, "right sub-chain")?;

    let left_input = left.into_recursion_input::<BatchOnly>();
    let right_input = right.into_recursion_input::<BatchOnly>();

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _left_vk_cap: &[Target],
                       _right_vk_cap: &[Target]| {
        let l = left_apt
            .get(left_idx)
            .expect("left sub-chain expose_claim instance present");
        let r = right_apt
            .get(right_idx)
            .expect("right sub-chain expose_claim instance present");
        debug_assert_eq!(l.len(), CHAIN_CLAIM_LEN);
        debug_assert_eq!(r.len(), CHAIN_CLAIM_LEN);

        // ⚑ THE CARRY. The left sub-chain's final sponge state IS the right sub-chain's initial
        // one, limb for limb, enforced in-circuit.
        for k in 0..STATE_WIDTH {
            cb.connect(l[STATE_WIDTH + k], r[k]);
        }

        // The ordered transcript commitment.
        let mut acc_inputs: Vec<Target> = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
        acc_inputs.extend_from_slice(&l[CLAIM_ACC_LO..CLAIM_ACC_LO + SEG_DIGEST_WIDTH]);
        acc_inputs.extend_from_slice(&r[CLAIM_ACC_LO..CLAIM_ACC_LO + SEG_DIGEST_WIDTH]);
        let acc = seg_poseidon_commit(cb, &acc_inputs);

        let mut parent: Vec<Target> = Vec::with_capacity(CHAIN_CLAIM_LEN);
        parent.extend_from_slice(&l[..STATE_WIDTH]); // left's INCOMING state
        parent.extend_from_slice(&r[STATE_WIDTH..2 * STATE_WIDTH]); // right's OUTGOING state
        parent.extend_from_slice(&acc);
        debug_assert_eq!(parent.len(), CHAIN_CLAIM_LEN);
        cb.expose_as_public_output(&parent);
    };

    prove_recursion_aggregation_auto_with_expose(&left_input, &right_input, config, Some(&expose))
        .map_err(|e| format!("chain fold failed: {e}"))
}

fn require_chain_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
    role: &str,
) -> Result<usize, String> {
    let len = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .map_or(0, |e| e.public_values.len());
    if len != CHAIN_CLAIM_LEN {
        return Err(format!(
            "{role} exposes {len} claim lane(s), expected exactly {CHAIN_CLAIM_LEN}; refusing an \
             ambiguous chain layout"
        ));
    }
    expose_claim_instance_index(&output.0).ok_or_else(|| {
        format!("{role} carries no expose_claim instance despite its claimed layout")
    })
}

/// Read the `in_state ‖ out_state ‖ transcript_acc` claim a leaf or fold node publishes.
///
/// ⚑ Delegates to the VERIFY crate's reader — the same function a node runs over a decoded root,
/// so a fold measured here and a root consumed there cannot read the claim differently.
pub fn read_chain_claim(output: &RecursionOutput<DreggRecursionConfig>) -> Option<ChainClaim> {
    read_chain_claim_from_proof(&output.0)
}

// ============================================================================
// THE HOST MIRROR — what the root digest is compared against.
// ============================================================================

/// The leaf-level transcript commitment: `commit(absorbed_pair)` over the 64 absorbed limbs of one
/// link's public inputs. Mirrors the leaf's in-circuit [`seg_poseidon_commit`] exactly.
pub fn host_chain_leaf_acc(public_inputs: &[BabyBear]) -> [BabyBear; SEG_DIGEST_WIDTH] {
    seg_poseidon_commit_host(&public_inputs[ABSORBED_PI_LO..ABSORBED_PI_LO + ABSORBED_WIDTH])
}

/// The node-level fold: `commit(left.acc ‖ right.acc)`, order-sensitive.
pub fn host_chain_transcript_fold(
    left: &[BabyBear; SEG_DIGEST_WIDTH],
    right: &[BabyBear; SEG_DIGEST_WIDTH],
) -> [BabyBear; SEG_DIGEST_WIDTH] {
    let mut inputs = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
    inputs.extend_from_slice(left);
    inputs.extend_from_slice(right);
    seg_poseidon_commit_host(&inputs)
}

/// ⚑ **THE VALUE THE ROOT'S DIGEST MUST EQUAL.** The LEFT-LEANING sequential fold of the per-link
/// commitments, in chain order — the host twin of the tree [`fold_chain_links`] builds. Computed
/// from the Lean-emitted public inputs of the real block's tape; if the root exposes a different
/// digest, the prover absorbed something else.
pub fn host_chain_transcript_acc(link_pis: &[Vec<BabyBear>]) -> [BabyBear; SEG_DIGEST_WIDTH] {
    assert!(!link_pis.is_empty(), "a chain has at least one link");
    let mut acc = host_chain_leaf_acc(&link_pis[0]);
    for pis in &link_pis[1..] {
        acc = host_chain_transcript_fold(&acc, &host_chain_leaf_acc(pis));
    }
    acc
}

/// ⚑ **THE WHOLE-CHAIN FOLD.** Prove every link as a leaf and fold them left-to-right into one
/// claim. `link_witnesses` is `(trace, public_inputs)` in CHAIN ORDER.
///
/// `progress` is called with `(index, phase)` so a caller can report a long fold without this
/// module owning a logging policy.
pub fn prove_chain_fold(
    link_witnesses: &[(Vec<Vec<BabyBear>>, Vec<BabyBear>)],
    config: &DreggRecursionConfig,
    mut progress: impl FnMut(usize, &str),
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if link_witnesses.is_empty() {
        return Err("a chain fold needs at least one link".into());
    }
    progress(0, "leaf");
    let mut acc = prove_chain_link_leaf(&link_witnesses[0].0, &link_witnesses[0].1, config)?;
    for (i, (trace, pis)) in link_witnesses.iter().enumerate().skip(1) {
        progress(i, "leaf");
        let leaf = prove_chain_link_leaf(trace, pis, config)?;
        progress(i, "fold");
        acc = fold_chain_links(&acc, &leaf, config)?;
    }
    Ok(acc)
}

/// The default config every chain leaf, fold and verify runs at.
pub fn chain_config() -> DreggRecursionConfig {
    ir2_leaf_wrap_config()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_chain_claim_layout_has_no_aliasing() {
        assert_eq!(STATE_WIDTH, 96);
        assert_eq!(IN_PI_LO, 0);
        assert_eq!(OUT_PI_LO, 96);
        assert_eq!(ABSORBED_PI_LO, 192);
        assert_eq!(CHAIN_PI_COUNT, 256);
        assert_eq!(CHAIN_CLAIM_LEN, 200);
        assert_eq!(CLAIM_ACC_LO, 192);
        // `in ‖ out` must be contiguous — the leaf exposes it as ONE slice.
        assert_eq!(OUT_PI_LO, IN_PI_LO + STATE_WIDTH);
        assert_eq!(ABSORBED_PI_LO, OUT_PI_LO + STATE_WIDTH);
    }

    #[test]
    fn the_lean_descriptor_declares_the_layout_this_module_reads() {
        let desc = chain_link_descriptor().expect("the Lean chain-link descriptor parses");
        assert_eq!(desc.name, "dregg-pasta-fq-chainlink::v1");
        assert_eq!(desc.public_input_count, CHAIN_PI_COUNT);
        assert_eq!(desc.trace_width, 469);
    }

    /// The transcript fold is ORDER-SENSITIVE — a swapped pair of sub-chains must not mint the
    /// same digest, or the fold would be a set commitment and the tape's order would be free.
    #[test]
    fn the_transcript_fold_is_order_sensitive() {
        let a = [BabyBear::new(7); SEG_DIGEST_WIDTH];
        let mut b = [BabyBear::new(7); SEG_DIGEST_WIDTH];
        b[0] = BabyBear::new(9);
        assert_ne!(
            host_chain_transcript_fold(&a, &b),
            host_chain_transcript_fold(&b, &a)
        );
    }
}
