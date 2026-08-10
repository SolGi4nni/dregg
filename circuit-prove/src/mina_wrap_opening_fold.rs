//! ⚑⚑ **THE IPA OPENING RELATION'S LEAF, FOLDED INTO THE RECURSION TOWER — the scheduled row's
//! first proving consumer.**
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **The AIR is Lean-authored.** `dregg-mina-wrap-opening-sched::v1` is
//! `EffectLower.lowerTiedAir` of `Dregg2.Circuit.Emit.MinaWrapOpeningSched.openingSchedAir`
//! (CertifiedRefines produced at the emit), and the trace is rendered by
//! `metatheory/MinaWrapOpeningSchedEmit.lean`. Nothing here authors a constraint.
//!
//! ## What the leaf claims
//!
//! Statement (B) — the IPA opening relation of Mina devnet block 539508, `wrap_verifier.ml:383` /
//! `:422`, `ipa.rs:409-425` — as a 35-addend scheduled chain whose every addend is a descriptor
//! constant, with the `−z₁·sg` term at slot 0 and the affine `sg` published at `PI[192..255]`.
//! The vacuity pair (`opening_is_vacuous_when_sg_is_free` / `pinned_sg_makes_the_opening_refute`)
//! is retired by PINNING: `sg` is not a witness of this descriptor at all.
//!
//! ## ⚑ THE ENGINE IS DERIVED, NEVER NAMED
//!
//! [`prove_opening_leaf`] takes the engine its child is minted at and derives its own wrap engine
//! with [`recursion_layer_over`] — the rule `mina_wrap_closing_fold` landed, unchanged.
//!
//! ## ⚠ WHAT THIS DOES NOT ESTABLISH
//!
//! `MinaWrapOpeningSched.lean`'s own list, not softened here: P10 (extraction) untouched;
//! statement (A) `sg = ⟨s, srs.g⟩` deferred (the deferral gate refuses an undischarged batch);
//! the scaling runs in the emitter; the chain-level forcing walk (block registers as cross-row
//! indicators) is per-leg-forced but not composed for blocks past the first — the refusals in
//! `circuit/tests/mina_wrap_opening_sched_proves.rs` are the running behavioural evidence.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, ir2_airs_and_common_for_config,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;

use p3_recursion::{RecursionInput, RecursionOutput, Target};

use crate::gpu_backend::prove_recursion_layer_auto_with_expose;
use crate::ivc_turn_chain::ir2_leaf_wrap_config;
use crate::mina_accumulator_fold::{ACC_PI_COUNT, IN_PI_LO};
use crate::plonky3_recursion_impl::recursive::{DreggRecursionConfig, recursion_layer_over};

type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

/// `MinaWrapOpeningSched.OPEN_W`.
pub const OPENING_WIDTH: usize = 581;
/// The published `sg`'s lanes: 32 X limbs then 32 Y limbs, appended after the endpoints.
pub const SG_LANES: usize = 64;
/// `MinaWrapOpeningSched.OPEN_PI` — `acc_in ‖ acc_out ‖ sg.x ‖ sg.y`.
pub const OPENING_PI_COUNT: usize = ACC_PI_COUNT + SG_LANES;
/// The one descriptor name this module proves. A display name is not a key; the resolver checks
/// name AND width AND PI count.
pub const OPENING_NAME: &str = "dregg-mina-wrap-opening-sched::v1";

/// Parse the Lean-emitted opening descriptor and REFUSE anything whose name, width or PI count is
/// not this rung's.
///
/// ⚠ The descriptor JSON is not compiled in: the manifest carries one block's opening, so there is
/// one descriptor per proof and the caller supplies the bytes.
///
/// # Errors
/// Returns `Err` if the JSON does not parse, or if the parsed object's name, declared trace width
/// or public-input count is not the opening leaf's.
pub fn opening_descriptor(json: &str) -> Result<EffectVmDescriptor2, String> {
    let desc =
        parse_vm_descriptor2(json).map_err(|e| format!("opening descriptor parse failed: {e}"))?;
    if desc.name != OPENING_NAME {
        return Err(format!(
            "the opening leaf resolved to `{}`, expected `{OPENING_NAME}`; refusing a look-alike \
             descriptor",
            desc.name
        ));
    }
    if desc.trace_width != OPENING_WIDTH {
        return Err(format!(
            "opening descriptor `{}` declares width {}, expected {OPENING_WIDTH}",
            desc.name, desc.trace_width
        ));
    }
    if desc.public_input_count != OPENING_PI_COUNT {
        return Err(format!(
            "opening descriptor `{}` declares {} PIs, expected {OPENING_PI_COUNT}; refusing an \
             ambiguous claim layout",
            desc.name, desc.public_input_count
        ));
    }
    Ok(desc)
}

/// Prove the opening leaf and wrap it at the engine DERIVED from the child's —
/// `recursion_layer_over(config)`, never a named constant.
///
/// # Errors
/// Propagates every refusal of [`prove_opening_leaf_split`].
pub fn prove_opening_leaf(
    json: &str,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    prove_opening_leaf_split(
        json,
        trace,
        public_inputs,
        config,
        &recursion_layer_over(config),
    )
}

/// The split form: verify the child at `inner_config`'s knobs and MINT this layer at
/// `wrap_config`'s.
///
/// # Errors
/// Returns `Err` if the public-input vector is not `OPENING_PI_COUNT` long, if the descriptor is
/// not the opening leaf's, if the inner IR-v2 proof fails, or if the wrap layer fails.
pub fn prove_opening_leaf_split(
    json: &str,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    inner_config: &DreggRecursionConfig,
    wrap_config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != OPENING_PI_COUNT {
        return Err(format!(
            "an opening leaf carries exactly {OPENING_PI_COUNT} public inputs, got {}",
            public_inputs.len()
        ));
    }
    let desc = opening_descriptor(json)?;

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

    // ⚑ THE CLAIM IS THE CHILD'S OWN FRI-BOUND PI LANES, never a host scalar: `acc_in ‖ acc_out ‖
    // sg.x ‖ sg.y`, contiguous by the Lean pin layout.
    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<Target>],
                       _vk_cap: &[Target]| {
        let main = apt
            .first()
            .expect("an opening leaf has a main instance carrying the descriptor PIs");
        assert!(
            main.len() >= OPENING_PI_COUNT,
            "main instance must carry all {OPENING_PI_COUNT} opening PI slots"
        );
        let claim: Vec<Target> = (0..OPENING_PI_COUNT).map(|k| main[IN_PI_LO + k]).collect();
        cb.expose_as_public_output(&claim);
    };

    prove_recursion_layer_auto_with_expose(&input, wrap_config, Some(&expose))
}

/// The engine an opening LEAF's inner IR-v2 batch proof is minted at.
#[must_use]
pub fn opening_inner_config() -> DreggRecursionConfig {
    ir2_leaf_wrap_config()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The claim layout extends the accumulator's, so a future 2-child fold reuses the same
    /// `cb.connect` adapter over the first 192 lanes.
    #[test]
    fn the_opening_claim_layout_extends_the_accumulators() {
        assert_eq!(IN_PI_LO, 0);
        assert_eq!(ACC_PI_COUNT, 192);
        assert_eq!(OPENING_PI_COUNT, 256);
    }
}
