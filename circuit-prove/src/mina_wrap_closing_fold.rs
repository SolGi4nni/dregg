//! ⚑⚑ **THE IPA CLOSING CHAIN, AS A RECURSION TREE — and the leg that binds `sg` folded into it.**
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **The AIR is Lean-authored.** `dregg-mina-wrap-closing-{seg,final,srs}::v1` are
//! `EffectLower.lowerAir` of `Dregg2.Circuit.Emit.MinaWrapClosingAir.{closingSegAir,
//! closingFinalAir, closingRoutedAirOn}`. Not one constraint is authored here: the descriptors,
//! their pins, their manifest and their traces all come out of Lean. Rust proves the artifact and
//! folds it.
//!
//! ## WHAT THIS IS THE OTHER SIDE OF
//!
//! `MinaWrapOpeningGate` proves the IPA opening relation on Mina devnet block 539508 in the
//! KERNEL, and `MinaWrapVerifierAir.opening_is_vacuous_when_sg_is_free` is a theorem that it
//! refutes nothing while `sg` is free. `MinaAccumulatorAir` put the STEP-side accumulator check in
//! a circuit; the closing group equation had none. This is the closing equation, in a circuit, at
//! `ipa.rs`'s own combined MSM with `sg_rand_base = −z₁·rand_base` — the coefficient at which the
//! `sg` base drops out of the equation entirely (`MinaWrapClosingAir.the_combined_check_is_
//! constant_in_sg`) and the SRS leg carries `−z₁·s_r` instead.
//!
//! ## ⚑ THE PI LAYOUT IS THE ACCUMULATOR'S, ON PURPOSE
//!
//! A leaf publishes `acc_in ‖ acc_out` — 96 limbs each, contiguous, in that order — which is
//! `MinaAccumulatorAir`'s layout unchanged, so a fold node `cb.connect`s the left child's outgoing
//! 96 limbs to the right child's incoming ones and the two chains compose with ONE adapter.
//! [`crate::mina_accumulator_fold::ACC_PI_COUNT`] is re-used rather than re-declared: a second
//! spelling of 192 is the "two shapes that agree today" failure in its purest form.
//!
//! ## ⚑ THE ENGINE IS DERIVED, NEVER NAMED
//!
//! [`prove_closing_segment`] takes the engine its CHILD is minted at and derives its own wrap
//! engine with [`recursion_layer_over`]; [`prove_closing_fold`] applies it twice — the fixed point,
//! which is `create_recursion_config()`. No config constant is named at a call site. That is the
//! rule that landed 2026-08-07 and took an accumulator leaf from `298.08 s / 117.79 GiB / LDE 2^26`
//! to `21.63 s / 23.23 GiB / LDE 2^23`, and `recursion-verify/tests/tower_config_law.rs` is what
//! proves the measured object is the deployed one.
//!
//! ## ⚠ WHAT THIS DOES NOT ESTABLISH
//!
//! Every residual of `MinaWrapClosingAir`'s docblock, unchanged and not softened here:
//!
//! 1. The scaling `−z₁·s_r·G_r` runs in the EMITTER, not in the AIR. Circuit / emitter / nowhere,
//!    and there is no fourth place.
//! 2. `c·Q` enters as the published `PI[0..95]`. That it is the block's is a CONSUMER refusal.
//! 3. The challenges `u⃗` are not transcript-bound by anything here.
//! 4. P10 — that passing the closing check implies knowing an opening — is untouched.
//! 5. ⚑ **The row is `PastaCurveSound`'s 3 048-column one, NOT `PastaCurveScheduled`'s 481-column
//!    one.** The scheduled row is 6.34× narrower and 7.18× cheaper in committed cells, and the
//!    recursion cost law is linear in COLUMNS — so this leaf is roughly 7× more expensive than it
//!    needs to be. What blocks the port is that the scheduled layout puts one op per row with a
//!    33-phase shift register, so an accumulator crossing complete-additions needs a carry gated by
//!    the phase selector plus a re-run of `AirCrossRow`'s composition over a chain. That is real
//!    work this module does not do, and it is UNDONE WORK, not a theorem of the model.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, ir2_airs_and_common_for_config,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;

use p3_recursion::{BatchOnly, RecursionInput, RecursionOutput, Target};

use crate::fold_vk_pin::FoldVkPins;
use crate::gpu_backend::{
    prove_recursion_aggregation_auto_with_expose, prove_recursion_layer_auto_with_expose,
};
use crate::ivc_turn_chain::{expose_claim_instance_index, ir2_leaf_wrap_config};
use crate::mina_accumulator_fold::{ACC_PI_COUNT, IN_PI_LO, POINT_WIDTH};
use crate::plonky3_recursion_impl::recursive::{DreggRecursionConfig, recursion_layer_over};

type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

/// `PastaCurveSound.RCB_WIDTH`.
pub const CLOSING_WIDTH: usize = 3048;
/// `MinaAccumulatorAir.ROUTED_WIDTH`.
pub const CLOSING_ROUTED_WIDTH: usize = CLOSING_WIDTH + 1;

/// Which rung of the closing chain a segment is. The distinction is a DESCRIPTOR, not a flag: an
/// interior segment under the final descriptor would be forced to vanish (and could not), and a
/// final segment under the interior one would not be forced to vanish at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClosingRung {
    /// An interior segment. Publishes its endpoints; says nothing about vanishing.
    Interior,
    /// The LAST segment. Its own AIR forces the terminal accumulator to be the point at infinity.
    Final,
    /// ⚑ The last segment PLUS the routing: the addends are the descriptor's declared
    /// `closingAddends`, in which there is no `sg` slot.
    Routed,
}

impl ClosingRung {
    /// The descriptor name this rung must resolve to. Checked rather than trusted — a display name
    /// is not a key, and this tree has already shipped three wrong lookups in one day.
    #[must_use]
    pub const fn expected_name(self) -> &'static str {
        match self {
            ClosingRung::Interior => "dregg-mina-wrap-closing-seg::v1",
            ClosingRung::Final => "dregg-mina-wrap-closing-final::v1",
            ClosingRung::Routed => "dregg-mina-wrap-closing-srs::v1",
        }
    }

    /// The trace width the rung declares.
    #[must_use]
    pub const fn expected_width(self) -> usize {
        match self {
            ClosingRung::Interior | ClosingRung::Final => CLOSING_WIDTH,
            ClosingRung::Routed => CLOSING_ROUTED_WIDTH,
        }
    }
}

/// Parse a Lean-emitted closing descriptor and REFUSE anything whose name, width or PI count is not
/// the rung's.
///
/// ⚠ The descriptor JSON is not compiled in. `-srs`'s manifest carries the proof's own `delta`, so
/// there is one descriptor per opening proof and a by-name registry entry would be a lie about what
/// is fixed. The caller supplies the bytes; this refuses the ones that are not the rung's.
///
/// # Errors
/// Returns `Err` if the JSON does not parse, or if the parsed object's name, declared trace width
/// or public-input count is not the rung's.
pub fn closing_descriptor(rung: ClosingRung, json: &str) -> Result<EffectVmDescriptor2, String> {
    let desc =
        parse_vm_descriptor2(json).map_err(|e| format!("closing descriptor parse failed: {e}"))?;
    if desc.name != rung.expected_name() {
        return Err(format!(
            "the {rung:?} rung resolved to `{}`, expected `{}`; refusing a look-alike descriptor",
            desc.name,
            rung.expected_name()
        ));
    }
    if desc.trace_width != rung.expected_width() {
        return Err(format!(
            "closing descriptor `{}` declares width {}, expected {}",
            desc.name,
            desc.trace_width,
            rung.expected_width()
        ));
    }
    if desc.public_input_count != ACC_PI_COUNT {
        return Err(format!(
            "closing descriptor `{}` declares {} PIs, expected {ACC_PI_COUNT}; refusing an \
             ambiguous endpoint layout",
            desc.name, desc.public_input_count
        ));
    }
    Ok(desc)
}

/// Prove one closing segment as a recursion leaf, minting at the engine derived from the child's.
///
/// # Errors
/// Propagates every refusal of [`prove_closing_segment_split`].
pub fn prove_closing_segment(
    rung: ClosingRung,
    json: &str,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    prove_closing_segment_split(
        rung,
        json,
        trace,
        public_inputs,
        config,
        &recursion_layer_over(config),
    )
}

/// ⚑ The split form: verify the child at `inner_config`'s knobs and MINT this layer at
/// `wrap_config`'s. `prove_closing_segment` passes `recursion_layer_over(inner)` for the second,
/// which is the rule; a caller that names a config constant here is the thing that rule replaced.
///
/// # Errors
/// Returns `Err` if the public-input vector is not `ACC_PI_COUNT` long, if the descriptor is not
/// the rung's, if the inner IR-v2 proof fails, or if the wrap layer fails.
pub fn prove_closing_segment_split(
    rung: ClosingRung,
    json: &str,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    inner_config: &DreggRecursionConfig,
    wrap_config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != ACC_PI_COUNT {
        return Err(format!(
            "a closing segment carries exactly {ACC_PI_COUNT} public inputs, got {}",
            public_inputs.len()
        ));
    }
    let desc = closing_descriptor(rung, json)?;

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        inner_config,
    )?;
    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &inner, public_inputs, inner_config)?;

    let input = RecursionInput::NativeBatchStark {
        airs: &airs,
        proof: &inner,
        common_data: &common,
        table_public_inputs,
    };

    // ⚑ THE CLAIM IS THE CHILD'S OWN FRI-BOUND PI LANES, never a host scalar. `apt[0]` is the main
    // instance and the 192 lanes `acc_in ‖ acc_out` are contiguous by the Lean pin layout.
    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<Target>],
                       _vk_cap: &[Target]| {
        let main = apt
            .first()
            .expect("a closing segment has a main instance carrying the descriptor PIs");
        assert!(
            main.len() >= ACC_PI_COUNT,
            "main instance must carry all {ACC_PI_COUNT} closing PI slots"
        );
        let claim: Vec<Target> = (0..ACC_PI_COUNT).map(|k| main[IN_PI_LO + k]).collect();
        cb.expose_as_public_output(&claim);
    };

    prove_recursion_layer_auto_with_expose(&input, wrap_config, Some(&expose))
}

/// ⚑⚑ **THE FOLD, AND THE CARRY IS `cb.connect`, NOT A RE-PIN.**
///
/// The left sub-chain's TERMINAL accumulator is the right sub-chain's INITIAL one, limb for limb,
/// enforced in-circuit on the two children's own `expose_claim` instances. If this were replaced by
/// "both children publish the same PI vector", a prover would pick both sides and the node would
/// close nothing — the lesson `mina_phase2_chain_leaf` already paid for.
///
/// # Errors
/// Returns `Err` if either child's exposed claim is not `ACC_PI_COUNT` lanes, or if the aggregation
/// layer fails.
pub fn fold_closing_segments(
    left: &RecursionOutput<DreggRecursionConfig>,
    right: &RecursionOutput<DreggRecursionConfig>,
    pins: &FoldVkPins,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let left_idx = require_closing_claim(left, "left sub-chain")?;
    let right_idx = require_closing_claim(right, "right sub-chain")?;

    let left_input = left.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right_input = right.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _l_vk: &[Target],
                       _r_vk: &[Target]| {
        let l = left_apt
            .get(left_idx)
            .expect("the left child's exposed claim instance");
        let r = right_apt
            .get(right_idx)
            .expect("the right child's exposed claim instance");

        // ⚑ THE CARRY.
        for k in 0..POINT_WIDTH {
            cb.connect(l[POINT_WIDTH + k], r[k]);
        }

        let mut parent: Vec<Target> = Vec::with_capacity(ACC_PI_COUNT);
        parent.extend_from_slice(&l[..POINT_WIDTH]);
        parent.extend_from_slice(&r[POINT_WIDTH..2 * POINT_WIDTH]);
        debug_assert_eq!(parent.len(), ACC_PI_COUNT);
        cb.expose_as_public_output(&parent);
    };

    prove_recursion_aggregation_auto_with_expose(&left_input, &right_input, config, Some(&expose))
}

fn require_closing_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
    role: &str,
) -> Result<usize, String> {
    let lanes = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .map_or(0, |e| e.public_values.len());
    if lanes != ACC_PI_COUNT {
        return Err(format!(
            "the {role} exposes {lanes} claim lane(s), expected exactly {ACC_PI_COUNT}; refusing \
             an ambiguous closing-chain layout"
        ));
    }
    expose_claim_instance_index(&output.0).ok_or_else(|| {
        format!("the {role} carries no `expose_claim` instance despite its claimed layout")
    })
}

/// The engine a closing LEAF's inner IR-v2 batch proof is minted at.
#[must_use]
pub fn closing_inner_config() -> DreggRecursionConfig {
    ir2_leaf_wrap_config()
}

/// ⚑ Fold a whole closing chain left-to-right. The last segment is the one whose own AIR forces the
/// terminal accumulator to vanish; everything before it is `Interior`.
///
/// # Errors
/// Returns `Err` on an empty chain, or on any leaf or fold refusal.
pub fn prove_closing_fold(
    segments: &[(ClosingRung, &'static str, Vec<Vec<BabyBear>>, Vec<BabyBear>)],
    config: &DreggRecursionConfig,
    mut progress: impl FnMut(usize, &str),
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if segments.is_empty() {
        return Err("a closing chain has at least one segment".to_string());
    }
    // ⚑ THE FOLD ENGINE, DERIVED. A leaf wrap emits at `recursion_layer_over(config)`'s mint knobs,
    // so a node ABOVE a leaf verifies at those and mints at one more layer — the fixed point.
    let fold_config = recursion_layer_over(&recursion_layer_over(config));

    let mut acc: Option<RecursionOutput<DreggRecursionConfig>> = None;
    for (i, (rung, json, trace, pis)) in segments.iter().enumerate() {
        progress(i, "leaf");
        let leaf = prove_closing_segment(*rung, json, trace, pis, config)?;
        acc = Some(match acc {
            None => leaf,
            Some(prev) => {
                progress(i, "fold");
                let pins = FoldVkPins::tracked(&prev, &leaf)?;
                fold_closing_segments(&prev, &leaf, &pins, &fold_config)?
            }
        });
    }
    Ok(acc.expect("the chain is non-empty"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ⚑ The closing leaf's PI layout IS the accumulator's, so the two chains fold with one
    /// adapter. A constant checked against its own definition is decoration; this is the other
    /// kind — it is the reason `mina_accumulator_fold`'s constants are imported rather than
    /// respelled.
    #[test]
    fn the_closing_claim_layout_is_the_accumulators() {
        assert_eq!(IN_PI_LO, 0);
        assert_eq!(POINT_WIDTH, 96);
        assert_eq!(ACC_PI_COUNT, 192);
        assert_eq!(CLOSING_ROUTED_WIDTH, CLOSING_WIDTH + 1);
    }

    /// A display name is not a key: every rung names a distinct descriptor and a distinct width.
    #[test]
    fn the_three_rungs_name_three_objects() {
        let names = [
            ClosingRung::Interior.expected_name(),
            ClosingRung::Final.expected_name(),
            ClosingRung::Routed.expected_name(),
        ];
        let mut sorted = names;
        sorted.sort_unstable();
        sorted.iter().zip(sorted.iter().skip(1)).for_each(|(a, b)| {
            assert_ne!(a, b, "two rungs share a descriptor name");
        });
        assert_eq!(ClosingRung::Interior.expected_width(), CLOSING_WIDTH);
        assert_eq!(ClosingRung::Routed.expected_width(), CLOSING_ROUTED_WIDTH);
    }

    /// The resolver refuses a look-alike rather than proving the wrong claim.
    #[test]
    fn a_wrong_named_descriptor_is_refused() {
        let json = include_str!("../../circuit/tests/fixtures/mina-wrap-closing-final.json");
        assert!(closing_descriptor(ClosingRung::Final, json).is_ok());
        let err = closing_descriptor(ClosingRung::Routed, json)
            .expect_err("the final descriptor is not the routed rung");
        assert!(err.contains("refusing a look-alike"), "{err}");
    }
}
