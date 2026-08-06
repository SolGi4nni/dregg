//! ⚑⚑ **THE DEFERRED IPA ACCUMULATOR CHAIN, AS A RECURSION TREE.**
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **The AIR is Lean-authored.** `dregg-mina-accumulator-seg::v1` /
//! `dregg-mina-accumulator-final::v1` are `EffectLower.lowerAir` of
//! `Dregg2.Circuit.Emit.MinaAccumulatorAir.{accSegAir, accFinalAir}`. Not one constraint is
//! authored here: the descriptors, their pins, their range tables and their traces all come out of
//! Lean. Rust proves the artifact and folds it.
//!
//! ## WHAT THIS IS THE OTHER SIDE OF
//!
//! `bridge/src/mina_accumulator_discharge.rs` evaluates `Σᵢrⁱ·Cᵢ − ⟨Σᵢrⁱ·s(u⃗ᵢ), G⟩ == O`
//! **natively** over the 65 536-generator Vesta SRS, and its header says so: *"Nothing here is an
//! AIR, and that is the whole design."* Upstream's `Ipa.Step.accumulator_check` is inside their
//! verifier; ours was an oracle beside ours. This module and
//! `Dregg2.Circuit.Emit.MinaAccumulatorAir` are the leg moved inside.
//!
//! ## ⚑ WHY A FOLD AND NOT ONE PROOF — the number, not a worry
//!
//! `PastaMsmBucketed.fused_at_step` prices the whole `2^16`-generator MSM at **1 474 800** complete
//! additions. On the SOUND row that is `1 474 800 × 3 048 = 4.5 · 10⁹` committed cells, against a
//! `2^21` deployed row ceiling. So the full-width chain is a fold of segments and the recursion is
//! load-bearing rather than an optimisation — `MinaAccumulatorAir.the_full_width_sum_needs_the_fold`
//! is that arithmetic in the kernel.
//!
//! ## ⚑⚑ THE STATE IS CARRIED INSIDE THE RECURSION
//!
//! The lesson this campaign already paid for, from the phase-2 chain:
//!
//! > *"A fold that just re-pins the same public inputs closes nothing. The chain must carry state
//! > from leaf `i` to leaf `i+1` inside the recursion, so the last leaf's output is a consequence
//! > of the first leaf's input."*
//!
//! So [`fold_accumulator_segments`] `cb.connect`s the left child's **96 outgoing accumulator limbs**
//! to the right child's 96 incoming ones, in-circuit. A prover whose right segment starts from a
//! point the left segment did not produce makes the aggregation UNSAT: there is no parent proof.
//! Every lane connected is read from the child's OWN FRI-bound `air_public_targets` — the descriptor
//! PIs its inner batch proof binds — never from a free prover scalar.
//!
//! The 96 is not a coincidence with `mina_phase2_chain_leaf`'s 96: a projective Pasta point in the
//! sound 8-bit encoding and a Kimchi sponge state are both `3 × 32` felts.
//!
//! ⚑ **AND THE SEAM INSIDE A LEAF IS FORCED THE SAME WAY, ONE RAIL DOWN.** Within a segment the
//! accumulator crosses rows through 96 `AirLeg.window .transition` gates
//! (`PastaLadderThread.threadLegs`), and `MinaAccumulatorAir.threadedLadderV_forces` is the `n`-row
//! induction saying rows-satisfied + threads-held force the accumulator to BE the `n`-fold chain.
//! Between segments it crosses through `cb.connect`. Both are constraints; neither is a host
//! comparison.
//!
//! ## THE FOLD SHAPE
//!
//! A **left-leaning sequential** fold, `acc_{k+1} = node(acc_k, leaf_{k+1})`, for the same reason
//! the phase-2 chain chose one: the host mirror is a two-line loop rather than a tree the host must
//! reproduce shape-for-shape, and a shape-mismatched mirror is exactly the class of silent
//! disagreement this repo keeps finding. Each node exposes `left.acc_in ‖ right.acc_out` — the same
//! 192-lane shape a leaf exposes, which is what makes the node composable with itself to any depth.
//!
//! ## ⚑ THE DISCHARGE, AND WHICH RAIL IT IS ON
//!
//! Two ways to force the terminal accumulator to be the point at infinity, and they are not equally
//! strong. Both are reachable here and a caller must say which one a given root has:
//!
//! 1. ⚑ **IN-AIR (strongest).** Prove the LAST segment against `dregg-mina-accumulator-final::v1`,
//!    whose 64 `when_last_row` boundary gates force `OUT_X` and `OUT_Z` to be the canonical zero
//!    limbs. No host has to remember to look. [`prove_accumulator_fold`] does this by default.
//! 2. **HOST-READ (weaker, and named as such).**
//!    `dregg_recursion_verify::accumulator_root::AccumulatorClaim::is_identity` on the root's
//!    published `acc_out`. Correct, but it is a check a consumer can forget.
//!
//! ## ⚠ WHAT THIS DOES NOT ESTABLISH
//!
//! **Not that the addends are the SRS.** `accumulator_discharge_forced` forces the chain of the
//! trace's OWN addends to vanish and says nothing about what those addends are. Forcing `A_r` to be
//! the `r`-th scaled generator is the routing half — `PastaMsmBucketed`'s exact-public lookups —
//! and `MinaAccumulatorAir.the_routing_tuple_does_not_fit_one_table` prices the one deployed
//! constant in its way (`MAX_EXACT_PUBLIC_ARITY = 64` against a 97-wide point tuple).
//!
//! **And not that the claim is this block's.** The chain's entry accumulator IS the claim
//! commitment `C` and it is published at `PI[0..95]` at full 256-bit width, elementwise, with no
//! digest — but no gate here relates it to a light client's `TIP_STATE`. That comparison is the
//! consumer's, and it is a refusal, not a tie.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2Air, MemBoundaryWitness, UMemBoundaryWitness,
    ir2_airs_and_common_for_config, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;

use p3_recursion::{BatchOnly, RecursionInput, RecursionOutput, Target};

use crate::gpu_backend::{
    prove_recursion_aggregation_auto_with_expose, prove_recursion_layer_auto_with_expose,
};
use crate::ivc_turn_chain::{expose_claim_instance_index, ir2_leaf_wrap_config};
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;

type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

/// The Lean-emitted SEGMENT descriptor — an interior link of the accumulator chain.
const SEG_DESC_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/mina-accumulator-seg.json");
/// …and the FINAL one, which additionally forces the terminal accumulator to vanish.
const FINAL_DESC_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/mina-accumulator-final.json");

// ⚑ THE CLAIM SHAPE AND ITS READER LIVE IN `dregg-recursion-verify`, NOT HERE — a node that
// consumes a fold ROOT must read the claim without linking this crate, and a second copy of the
// layout on the verify side is the "two shapes that agree today" failure in its purest form.
pub use dregg_recursion_verify::accumulator_root::{
    ACC_CLAIM_LEN, AccumulatorClaim, CLAIM_OUT_LO, POINT_COORDS, POINT_WIDTH, SK,
    read_accumulator_claim_from_proof,
};

/// PI offset of the INCOMING accumulator block (`MinaAccumulatorAir.ACC_IN_PI 0`).
pub const IN_PI_LO: usize = 0;
/// PI offset of the OUTGOING accumulator block (`MinaAccumulatorAir.ACC_OUT_PI 0`).
pub const OUT_PI_LO: usize = POINT_WIDTH;
/// `MinaAccumulatorAir.ACC_PI_COUNT`.
pub const ACC_PI_COUNT: usize = 2 * POINT_WIDTH;

/// ⚑ TWO INDEPENDENT SOURCES, PINNED. The leaf's PI vector is `acc_in ‖ acc_out` and the claim the
/// verify crate reads is the same 192 lanes in the same order — so the prover's layout and the
/// consumer's must be the same number. A constant checked against its own definition is decoration;
/// this is the other kind.
const _: () = assert!(ACC_PI_COUNT == ACC_CLAIM_LEN);
const _: () = assert!(OUT_PI_LO == CLAIM_OUT_LO);
const _: () = assert!(POINT_WIDTH == POINT_COORDS * SK);

/// Which rung of the chain a segment is. The distinction is a DESCRIPTOR, not a flag: an interior
/// segment that used the final descriptor would be forced to vanish (and could not), and a final
/// segment that used the interior one would not be forced to vanish at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rung {
    /// An interior segment. Publishes its endpoints; says nothing about vanishing.
    Interior,
    /// ⚑ The LAST segment. Its own AIR forces the terminal accumulator to be the point at infinity.
    Final,
}

impl Rung {
    fn json(self) -> &'static str {
        match self {
            Rung::Interior => SEG_DESC_JSON,
            Rung::Final => FINAL_DESC_JSON,
        }
    }

    /// The descriptor name this rung must resolve to. Checked rather than trusted: a display name
    /// is not a key, and this tree has already shipped three wrong lookups in one day.
    fn expected_name(self) -> &'static str {
        match self {
            Rung::Interior => "dregg-mina-accumulator-seg::v1",
            Rung::Final => "dregg-mina-accumulator-final::v1",
        }
    }
}

/// Parse the Lean-emitted accumulator descriptor for a rung. Rust authors none of it.
pub fn accumulator_descriptor(rung: Rung) -> Result<EffectVmDescriptor2, String> {
    let desc = parse_vm_descriptor2(rung.json())
        .map_err(|e| format!("accumulator descriptor parse failed: {e}"))?;
    if desc.name != rung.expected_name() {
        return Err(format!(
            "the {rung:?} rung resolved to `{}`, expected `{}`; refusing a look-alike descriptor",
            desc.name,
            rung.expected_name()
        ));
    }
    if desc.public_input_count != ACC_PI_COUNT {
        return Err(format!(
            "accumulator descriptor `{}` declares {} PIs, expected {ACC_PI_COUNT}; refusing an \
             ambiguous endpoint layout",
            desc.name, desc.public_input_count
        ));
    }
    Ok(desc)
}

/// ⚑ **THE LEAF.** Prove one Lean-emitted segment as a foldable recursion leaf, exposing
/// `acc_in(96) ‖ acc_out(96)`.
///
/// Every exposed lane is read from the leaf's OWN verified `air_public_targets` — the descriptor
/// PIs the inner batch proof binds — so a prover cannot expose an accumulator that disagrees with
/// the chain it just proved. The two blocks are CONTIGUOUS by the Lean pin layout, which is why
/// this is one slice rather than two.
pub fn prove_accumulator_segment(
    rung: Rung,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != ACC_PI_COUNT {
        return Err(format!(
            "an accumulator segment carries exactly {ACC_PI_COUNT} public inputs, got {}",
            public_inputs.len()
        ));
    }
    let desc = accumulator_descriptor(rung)?;

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("accumulator segment inner IR-v2 prove failed: {e}"))?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &inner, public_inputs, config)
            .map_err(|e| format!("accumulator verify-triple build failed: {e}"))?;

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
            .expect("an accumulator segment has a main instance carrying the descriptor PIs");
        debug_assert!(
            main.len() >= ACC_PI_COUNT,
            "main instance must carry all {ACC_PI_COUNT} accumulator PI slots"
        );
        let claim: Vec<Target> = (0..ACC_PI_COUNT).map(|k| main[IN_PI_LO + k]).collect();
        debug_assert_eq!(claim.len(), ACC_CLAIM_LEN);
        cb.expose_as_public_output(&claim);
    };

    prove_recursion_layer_auto_with_expose(&input, config, Some(&expose))
        .map_err(|e| format!("accumulator segment leaf wrap failed: {e}"))
}

/// ⚑⚑ **THE FOLD — WHERE THE ACCUMULATOR IS CARRIED, INSIDE THE RECURSION.**
///
/// Verifies both children in-circuit and then:
///
/// * `connect(left.acc_out[k], right.acc_in[k])` for all 96 limbs — **the carry.** A prover whose
///   right segment starts from a point the left segment did not produce has no satisfying
///   assignment, so there is no parent proof. This is the whole difference between `N` proofs and
///   one claim, and it is the same mechanism `mina_phase2_chain_leaf` uses for the sponge state.
/// * exposes `left.acc_in ‖ right.acc_out` — the same 192-lane shape a leaf exposes.
///
/// ⚠ There is deliberately no host comparison here and no re-pinned public input. If the connect
/// were replaced by "both children publish the same PI vector", a prover would pick both sides and
/// the fold would close nothing.
pub fn fold_accumulator_segments(
    left: &RecursionOutput<DreggRecursionConfig>,
    right: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let left_idx = require_accumulator_claim(left, "left sub-chain")?;
    let right_idx = require_accumulator_claim(right, "right sub-chain")?;

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
        debug_assert_eq!(l.len(), ACC_CLAIM_LEN);
        debug_assert_eq!(r.len(), ACC_CLAIM_LEN);

        // ⚑ THE CARRY. The left sub-chain's terminal accumulator IS the right sub-chain's initial
        // one, limb for limb, enforced in-circuit.
        for k in 0..POINT_WIDTH {
            cb.connect(l[POINT_WIDTH + k], r[k]);
        }

        let mut parent: Vec<Target> = Vec::with_capacity(ACC_CLAIM_LEN);
        parent.extend_from_slice(&l[..POINT_WIDTH]); // left's INCOMING accumulator
        parent.extend_from_slice(&r[POINT_WIDTH..2 * POINT_WIDTH]); // right's OUTGOING one
        debug_assert_eq!(parent.len(), ACC_CLAIM_LEN);
        cb.expose_as_public_output(&parent);
    };

    prove_recursion_aggregation_auto_with_expose(&left_input, &right_input, config, Some(&expose))
        .map_err(|e| format!("accumulator fold failed: {e}"))
}

fn require_accumulator_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
    role: &str,
) -> Result<usize, String> {
    let len = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .map_or(0, |e| e.public_values.len());
    if len != ACC_CLAIM_LEN {
        return Err(format!(
            "{role} exposes {len} claim lane(s), expected exactly {ACC_CLAIM_LEN}; refusing an \
             ambiguous accumulator layout"
        ));
    }
    expose_claim_instance_index(&output.0).ok_or_else(|| {
        format!("{role} carries no expose_claim instance despite its claimed layout")
    })
}

/// Read the `acc_in ‖ acc_out` claim a leaf or fold node publishes.
///
/// ⚑ Delegates to the VERIFY crate's reader — the same function a node runs over a decoded root, so
/// a fold measured here and a root consumed there cannot read the claim differently.
pub fn read_accumulator_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<AccumulatorClaim> {
    read_accumulator_claim_from_proof(&output.0)
}

/// ⚑ **THE WHOLE-CHAIN FOLD.** Prove every segment as a leaf and fold them left-to-right into one
/// claim. `segments` is `(trace, public_inputs)` in CHAIN ORDER.
///
/// The LAST segment is proved against `dregg-mina-accumulator-final::v1`, so the discharge is
/// forced by that leaf's own AIR rather than by a host read of the root — see the module header's
/// two rails. A one-segment chain is legal and is the deterministic case: it is the final segment
/// and there is no fold.
///
/// `progress` is called with `(index, phase)` so a caller can report a long fold without this
/// module owning a logging policy.
pub fn prove_accumulator_fold(
    segments: &[(Vec<Vec<BabyBear>>, Vec<BabyBear>)],
    config: &DreggRecursionConfig,
    mut progress: impl FnMut(usize, &str),
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let n = segments.len();
    if n == 0 {
        return Err("an accumulator fold needs at least one segment".into());
    }
    let rung_of = |i: usize| {
        if i + 1 == n {
            Rung::Final
        } else {
            Rung::Interior
        }
    };

    progress(0, "leaf");
    let mut acc = prove_accumulator_segment(rung_of(0), &segments[0].0, &segments[0].1, config)?;
    for (i, (trace, pis)) in segments.iter().enumerate().skip(1) {
        progress(i, "leaf");
        let leaf = prove_accumulator_segment(rung_of(i), trace, pis, config)?;
        progress(i, "fold");
        acc = fold_accumulator_segments(&acc, &leaf, config)?;
    }
    Ok(acc)
}

/// The default config every accumulator leaf, fold and verify runs at.
pub fn accumulator_config() -> DreggRecursionConfig {
    ir2_leaf_wrap_config()
}

// ============================================================================
// THE HOST MIRROR — what a caller derives the leaf public inputs from.
// ============================================================================

/// The accumulator's three INPUT blocks in the trace, contiguous at `0, 32, 64`
/// (`MinaAccumulatorAir.ACC_X/ACC_Y/ACC_Z`).
pub const TRACE_ACC_IN: [usize; POINT_COORDS] = [0, SK, 2 * SK];
/// The accumulator's three OUTPUT blocks — the gadget's SSA `v 26 / v 29 / v 32`. NOT contiguous,
/// which is exactly why the published PI side is.
pub const TRACE_ACC_OUT: [usize; POINT_COORDS] = [1024, 1120, 1216];

/// ⚑ **THE PUBLIC INPUTS A SEGMENT PUBLISHES, DERIVED FROM ITS OWN PINNED COLUMNS.**
///
/// `PI[0..95]` are the FIRST row's `ACC_X‖ACC_Y‖ACC_Z` limbs; `PI[96..191]` are the LAST row's
/// `OUT_X‖OUT_Y‖OUT_Z`. Read off the columns the Lean pins name — never authored, so a caller
/// cannot publish an endpoint the trace does not carry (and the pins would refuse it if it tried).
pub fn segment_public_inputs(trace: &[Vec<BabyBear>]) -> Result<Vec<BabyBear>, String> {
    let last = trace.len().checked_sub(1).ok_or("an empty segment trace")?;
    let want = TRACE_ACC_OUT[POINT_COORDS - 1] + SK;
    if trace.iter().any(|r| r.len() < want) {
        return Err(format!(
            "an accumulator segment row must carry at least {want} columns"
        ));
    }
    let mut pis = Vec::with_capacity(ACC_PI_COUNT);
    for base in TRACE_ACC_IN {
        pis.extend((0..SK).map(|i| trace[0][base + i]));
    }
    for base in TRACE_ACC_OUT {
        pis.extend((0..SK).map(|i| trace[last][base + i]));
    }
    debug_assert_eq!(pis.len(), ACC_PI_COUNT);
    Ok(pis)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_accumulator_claim_layout_has_no_aliasing() {
        assert_eq!(POINT_WIDTH, 96);
        assert_eq!(IN_PI_LO, 0);
        assert_eq!(OUT_PI_LO, 96);
        assert_eq!(ACC_PI_COUNT, 192);
        assert_eq!(ACC_CLAIM_LEN, 192);
        // `in ‖ out` must be contiguous — the leaf exposes it as ONE slice.
        assert_eq!(OUT_PI_LO, IN_PI_LO + POINT_WIDTH);
    }

    /// ⚑ **THE TWO RUNGS ARE TWO DESCRIPTORS, AND THE FINAL ONE FORCES STRICTLY MORE.**
    /// A rung that resolved to the wrong artifact would fold a chain nothing forces to vanish.
    #[test]
    fn the_two_rungs_resolve_to_the_two_lean_artifacts() {
        let interior = accumulator_descriptor(Rung::Interior).expect("the segment descriptor");
        let fin = accumulator_descriptor(Rung::Final).expect("the final descriptor");
        assert_eq!(interior.name, "dregg-mina-accumulator-seg::v1");
        assert_eq!(fin.name, "dregg-mina-accumulator-final::v1");
        assert_ne!(interior.name, fin.name);
        assert_eq!(
            interior.trace_width, fin.trace_width,
            "3 048 at every depth"
        );
        assert_eq!(interior.public_input_count, fin.public_input_count);
        assert_eq!(
            fin.constraints.len(),
            interior.constraints.len() + 64,
            "the final rung is the segment plus 64 discharge gates — three coordinates' worth of \
             X and Z limbs, and nothing else"
        );
        assert_eq!(
            interior.constraints,
            fin.constraints[..interior.constraints.len()],
            "the final descriptor must EXTEND the segment, not re-author it"
        );
    }

    /// The PI derivation reads the trace's own pinned columns and refuses a short row rather than
    /// indexing past it.
    #[test]
    fn the_public_inputs_come_from_the_pinned_columns() {
        let mut t = vec![vec![BabyBear::new(0); 3048]; 2];
        for i in 0..SK {
            t[0][TRACE_ACC_IN[0] + i] = BabyBear::new(11 + i as u32);
            t[1][TRACE_ACC_OUT[2] + i] = BabyBear::new(77 + i as u32);
        }
        let pis = segment_public_inputs(&t).expect("a two-row segment");
        assert_eq!(pis.len(), ACC_PI_COUNT);
        assert_eq!(pis[0], BabyBear::new(11));
        assert_eq!(pis[ACC_PI_COUNT - SK], BabyBear::new(77));

        assert!(
            segment_public_inputs(&[]).is_err(),
            "an empty trace must refuse"
        );
        assert!(
            segment_public_inputs(&[vec![BabyBear::new(0); 10]]).is_err(),
            "a short row must refuse rather than index past the accumulator blocks"
        );
    }
}
