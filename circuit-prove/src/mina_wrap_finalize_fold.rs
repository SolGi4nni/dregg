//! ⚑⚑ **THE ξ THE FINALIZE CONJUNCTION CHECKS IS THE ONE THE ENDO-LIFT PRODUCED — INSIDE THE
//! RECURSION.**
//!
//! ## What this module is the other side of
//!
//! `circuit/tests/mina_xi_endo_weld.rs` ties `dregg-mina-xi-endo-lift::v1`'s output block to
//! `dregg-mina-xi-scalar-vector::v2`'s input block **elementwise, 32 felts, no digest** — and it
//! does it as a HOST ASSERTION over two independently emitted PI vectors. That is a real
//! comparison, and it is a comparison a **test** makes. Nothing in either proof forces it: a prover
//! that hands the conjunction an ξ the endo-lift did not produce makes two proofs that both verify,
//! and only a reader running that test notices.
//!
//! This module makes the same equality a **constraint of a third proof**. `fold_endo_into_finalize`
//! verifies both children in-circuit and then `cb.connect`s the endo-lift's 32 published ξ limbs to
//! the conjunction's 32 published ξ limbs. A prover whose conjunction reads a different ξ has no
//! satisfying assignment in the aggregation circuit, so **there is no root**.
//!
//! ⚑ The distinction is the one this campaign already paid for, quoted from
//! `mina_phase2_chain_leaf.rs`:
//!
//! > *"A fold that just re-pins the same public inputs closes nothing. The chain must carry state
//! > from leaf `i` to leaf `i+1` inside the recursion."*
//!
//! Both lanes here are read from each child's OWN FRI-bound `air_public_targets` — the descriptor
//! PIs the inner batch proof binds — never from a free scalar the aggregation circuit invents.
//!
//! ## ⚑ WHAT THE ROOT CLAIM SAYS, AT THIS TREE'S RESOLUTION AND NOT AT THE NAME'S
//!
//! The root exposes `v'(32) ‖ zeta(32) ‖ zetaw(32) ‖ r(32) ‖ b0(32)` — 160 lanes, every one an
//! 8-bit limb of a Pasta-scalar field element — and read end to end it says:
//!
//! > **There is a polyscale ξ that is `ScalarChallenge(v′).to_field(endo_r)` for the published
//! > prechallenge `v′`, and against THAT ξ, this ζ, this ζω and this evalscale `r`: the deferred
//! > record's ξ equals the squeezed ξ; the published `b0` equals
//! > `bEval ζ chals + r · bEval ζω chals` for the fifteen IPA challenges the conjunction trace's own
//! > rows supplied; every one of those fifteen is welded to its inverse (`chal · chalinv ≡ 1`); and
//! > the opening residual's non-free coefficients (`c·cip − z1·b0`, `−z1`, `−z2`, `c·chal`,
//! > `c·chalinv`) are the values a sound core computed from those same columns.**
//!
//! ⚠ **IT IS NOT "THIS PICKLES PROOF IS VALID", AND THE REASON IS NAMED, NOT HAND-WAVED.**
//!
//! 1. **The IPA opening is not in circuit.** `PastaIpaDeferral.opening_is_vacuous_when_sg_is_free`
//!    is a THEOREM that the closing check accepts at every value of everything else while `sg` is a
//!    free witness. No fold of these two descriptors moves that.
//! 2. **Upstream's conjunction is a FOUR-way AND with the opening; this is a TWO-way AND.**
//!    `cipCorrect` and `plonkChecksPassed` are **absent by construction, not stubbed** —
//!    `MinaWrapConjunctionAir` §"WHAT THIS OBJECT FORCES" states why: a gate comparing `cip`
//!    against a ξ-fold with a FREE `ft_eval0` column forces nothing at all, and that `∃`-image
//!    vacuity has shipped in this repo before. Do not read this root as finalize.
//! 3. **`v′` is published, not derived here.** Tying it to the block's own Fq transcript is
//!    [`connect_chain_root_v_prime`]'s job, and that leg needs the 46-leaf chain fold
//!    (`mina_phase2_chain_leaf`; ⚠ the 1 037 s once recorded for it was measured at the OLD
//!    single-engine shape and is not this tower's price). Until a caller runs that fold and
//!    connects it, `v′` is a prover-chosen 128-bit value and the root is quantified over it.
//! 4. **ζ, ζω and `r` are published and derived by nothing.** ζ's provenance is the phase-1 (Fp)
//!    transcript, which has an emitted chain (`pasta-fp-chainlink.json`) and no weld to this object.
//!
//! ## THE FOLD SHAPE
//!
//! Two leaves, one node. Not a chain — there is one conjunction per proof and one endo-lift per
//! proof, so a sequential accumulator would be a fold of one. What makes this a fold rather than a
//! pair of proofs is the `connect`, which is the same mechanism `fold_chain_links` uses and the same
//! reason it is load-bearing there.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2Air, MemBoundaryWitness, UMemBoundaryWitness,
    ir2_airs_and_common_for_config, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;

use p3_recursion::{BatchOnly, RecursionInput, RecursionOutput, Target};

use crate::fold_vk_pin::FoldVkPins;
use crate::gpu_backend::{
    prove_recursion_aggregation_auto_with_expose, prove_recursion_layer_auto_with_expose,
};
use crate::ivc_turn_chain::{expose_claim_instance_index, ir2_leaf_wrap_config};
use crate::plonky3_recursion_impl::recursive::{DreggRecursionConfig, recursion_layer_over};
use crate::seam::{SeamSpec, apply_seam, xi_seam};

type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

/// The Lean-emitted endomorphism-lift descriptor (`MinaWrapXiEndoLift.endoDesc`).
const ENDO_DESC_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/mina-xi-endo-lift.json");
/// The Lean-emitted threaded finalize conjunction (`MinaWrapConjunctionAir.conjunctionDesc`).
const CONJ_DESC_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/mina-wrap-conjunction.json");

/// Limbs per Pasta field element in the sound base-`2^8` encoding (`PastaFieldSound.SK`).
pub const SK: usize = 32;

// ── the endo-lift's public surface ──────────────────────────────────────────────────────────────

/// `dregg-mina-xi-endo-lift::v1` PI offset of the prechallenge `v′` block.
pub const ENDO_PI_VPRIME: usize = 0;
/// …and of the lifted ξ block.
pub const ENDO_PI_XI: usize = SK;
/// The endo-lift publishes exactly two blocks.
pub const ENDO_PI_COUNT: usize = 2 * SK;

// ── the conjunction's public surface (`MinaWrapConjunctionAir` §9b) ─────────────────────────────

/// `dregg-mina-wrap-conjunction::v1` PI offset of the ξ block (`XI_CL`).
pub const CONJ_PI_XI: usize = 0;
/// …ζ.
pub const CONJ_PI_ZETA: usize = SK;
/// …ζω.
pub const CONJ_PI_ZETAW: usize = 2 * SK;
/// …the evalscale `r`.
pub const CONJ_PI_R: usize = 3 * SK;
/// …and the claimed `b0`.
pub const CONJ_PI_B0: usize = 4 * SK;
/// `MinaWrapConjunctionAir.CJ_PI_COUNT`.
pub const CONJ_PI_COUNT: usize = 5 * SK;

/// The conjunction's declared trace height: 15 IPA round rows plus the terminal read row.
pub const CONJ_ROWS: usize = 16;

// ── the root claim ──────────────────────────────────────────────────────────────────────────────

/// Root claim offset of the prechallenge `v′` — the only lane of the endo-lift that survives the
/// fold, because ξ itself is now *internal* to the aggregation and publishing it would invite a
/// reader to treat the two halves as separately checkable again.
pub const CLAIM_VPRIME: usize = 0;
/// …ζ.
pub const CLAIM_ZETA: usize = SK;
/// …ζω.
pub const CLAIM_ZETAW: usize = 2 * SK;
/// …`r`.
pub const CLAIM_R: usize = 3 * SK;
/// …`b0`.
pub const CLAIM_B0: usize = 4 * SK;
/// `v'(32) ‖ zeta(32) ‖ zetaw(32) ‖ r(32) ‖ b0(32)`.
pub const FINALIZE_CLAIM_LEN: usize = 5 * SK;

/// Parse the Lean-emitted endo-lift descriptor. Rust authors none of it.
pub fn endo_lift_descriptor() -> Result<EffectVmDescriptor2, String> {
    let d = parse_vm_descriptor2(ENDO_DESC_JSON)
        .map_err(|e| format!("endo-lift descriptor parse failed: {e}"))?;
    if d.public_input_count != ENDO_PI_COUNT {
        return Err(format!(
            "endo-lift descriptor declares {} PIs, expected {ENDO_PI_COUNT}; refusing an ambiguous \
             pin layout",
            d.public_input_count
        ));
    }
    Ok(d)
}

/// Parse the Lean-emitted conjunction descriptor. Rust authors none of it.
///
/// ⚑ The `public_input_count` check is the whole reason this function exists rather than a bare
/// `parse`: until 2026-08-06 this descriptor declared **zero** public inputs, so a fold of it could
/// only ever have connected nothing to nothing. A build against a pre-08-06 artifact must FAIL
/// here, loudly, rather than silently fold an empty claim.
pub fn conjunction_descriptor() -> Result<EffectVmDescriptor2, String> {
    let d = parse_vm_descriptor2(CONJ_DESC_JSON)
        .map_err(|e| format!("conjunction descriptor parse failed: {e}"))?;
    if d.public_input_count != CONJ_PI_COUNT {
        return Err(format!(
            "conjunction descriptor declares {} PIs, expected {CONJ_PI_COUNT}; a descriptor with no \
             public surface has no subject and cannot be folded",
            d.public_input_count
        ));
    }
    Ok(d)
}

/// ⚑ **LEAF A — the endomorphism lift**, exposing `v'(32) ‖ xi(32)` from its own bound PIs.
pub fn prove_endo_lift_leaf(
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    prove_endo_lift_leaf_split(trace, public_inputs, config, &recursion_layer_over(config))
}

/// ⚑⚑ **THE SAME LEAF WITH ITS TWO FRI ROLES NAMED SEPARATELY** — and they were never one.
///
/// * `inner_config` mints the IR-v2 descriptor batch AND supplies the in-circuit verifier params
///   that check it. These two must agree: they are the same proof, minted then verified.
/// * `wrap_config` mints the WRAP's own output proof. Its `FriVerifierParams` must still describe
///   the child, but its PCS `log_blowup` — the number that multiplies every committed cell of the
///   verification circuit — is a **free choice**.
///
/// [`prove_endo_lift_leaf`] derives the second from the first. This exists so the OLD
/// single-engine shape stays REACHABLE for a before/after measurement in ONE binary, and for
/// nothing else.
pub fn prove_endo_lift_leaf_split(
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    inner_config: &DreggRecursionConfig,
    wrap_config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let desc = endo_lift_descriptor()?;
    prove_ir2_leaf(
        &desc,
        trace,
        public_inputs,
        ENDO_PI_COUNT,
        inner_config,
        wrap_config,
        "endo-lift",
    )
}

/// ⚑ **LEAF B — the threaded finalize conjunction**, exposing all five published blocks.
pub fn prove_conjunction_leaf(
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    prove_conjunction_leaf_split(trace, public_inputs, config, &recursion_layer_over(config))
}

/// ⚑ The conjunction leaf with its two FRI roles named separately — see
/// [`prove_endo_lift_leaf_split`] for what the pair means and why it exists.
pub fn prove_conjunction_leaf_split(
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    inner_config: &DreggRecursionConfig,
    wrap_config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let desc = conjunction_descriptor()?;
    if trace.len() != CONJ_ROWS {
        return Err(format!(
            "the conjunction trace is {} rows; the descriptor's `.transition` thread is {} rounds \
             plus one terminal read row",
            trace.len(),
            CONJ_ROWS - 1
        ));
    }
    prove_ir2_leaf(
        &desc,
        trace,
        public_inputs,
        CONJ_PI_COUNT,
        inner_config,
        wrap_config,
        "conjunction",
    )
}

/// The shared leaf body: prove the descriptor, wrap it as a recursion layer, and expose the whole
/// PI vector read out of the leaf's own verified `air_public_targets`.
#[allow(clippy::too_many_arguments)]
fn prove_ir2_leaf(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    pi_count: usize,
    config: &DreggRecursionConfig,
    wrap_config: &DreggRecursionConfig,
    role: &'static str,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != pi_count {
        return Err(format!(
            "{role} leaf carries {} public inputs, expected {pi_count}",
            public_inputs.len()
        ));
    }

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        desc,
        trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("{role} inner IR-v2 prove failed: {e}"))?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(desc, &inner, public_inputs, config)
            .map_err(|e| format!("{role} verify-triple build failed: {e}"))?;

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
            .expect("an IR-v2 leaf has a main instance carrying the descriptor PIs");
        debug_assert!(main.len() >= pi_count);
        let claim: Vec<Target> = (0..pi_count).map(|k| main[k]).collect();
        cb.expose_as_public_output(&claim);
    };

    prove_recursion_layer_auto_with_expose(&input, wrap_config, Some(&expose))
        .map_err(|e| format!("{role} leaf wrap failed: {e}"))
}

/// ⚑⚑ **THE FOLD — WHERE ξ STOPS BEING TWO NUMBERS THAT AGREE AND BECOMES ONE.**
///
/// Verifies both children in-circuit and then:
///
/// * applies the **ξ seam** — [`crate::seam::xi_seam`], the Lean-emitted
///   `MinaSeams.xiSeam` — welding all **32** limbs of the endo-lift's lifted-ξ block to the
///   conjunction's record-ξ block. Elementwise, 255 bits, **no digest and therefore no birthday
///   bound**. A prover whose conjunction reads an ξ the endo-lift did not produce has no
///   satisfying assignment, so there is no parent proof. ⚑ This function authors NO index
///   arithmetic: the pin list is the emitted object, `S1 =
///   the_xi_seam_welds_the_lift_to_the_record` proves it names exactly the two published ξ blocks,
///   and `S2 = xi_seam_certifies` (refutable: `xi_seam_S2_needs_the_seam`) is the composition.
/// * exposes `endo.v' ‖ conj.zeta ‖ conj.zetaw ‖ conj.r ‖ conj.b0` — ξ itself is deliberately NOT
///   re-published: it is now an internal wire of the aggregation, and a root that re-published it
///   would read as though the two halves were still separately checkable.
/// ⚑ **AND THE CHILD-VK PIN.** `pins` fixes each child's preprocessed commitment in-circuit
/// ([`crate::fold_vk_pin`]). Without it the two `require_claim` lane-count checks are the only
/// gate, and a same-shape/different-constants endo-lift or conjunction descriptor passes them.
///
/// # Refusals
///
/// Beyond the claim-width checks: the seam's two ends are checked against the descriptors this
/// module actually loads, by name AND by RECOMPUTED fingerprint lanes
/// ([`crate::seam::SeamEnd::require_matches`]) — a stale emitted seam is a loud error here.
///
/// ⚠ `config` here is [`finalize_root_config`], the FOLD engine — **not** the inner descriptor
/// engine the two leaves are handed. Both are `DreggRecursionConfig` and nothing in the type system
/// separates them; passing the leaves' config here is a `QueryProofCountMismatch { expected: 19,
/// got: 38 }` at the in-circuit verifier of a 38-query child.
pub fn fold_endo_into_finalize(
    endo: &RecursionOutput<DreggRecursionConfig>,
    conj: &RecursionOutput<DreggRecursionConfig>,
    pins: &FoldVkPins,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let endo_idx = require_claim(endo, "endo-lift leaf", ENDO_PI_COUNT)?;
    let conj_idx = require_claim(conj, "conjunction leaf", CONJ_PI_COUNT)?;

    // ⚑ THE SEAM, read rather than authored — and refused if it does not name the two descriptors
    // this fold verifies (fingerprint lanes recomputed, not trusted).
    let seam: SeamSpec = xi_seam()?;
    seam.left.require_matches(&endo_lift_descriptor()?)?;
    seam.right.require_matches(&conjunction_descriptor()?)?;

    // ⚠ No host pre-flight against `pins` — the refusal must be the circuit's.
    let endo_input = endo.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let conj_input = conj.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       endo_apt: &[Vec<Target>],
                       conj_apt: &[Vec<Target>],
                       _endo_vk_cap: &[Target],
                       _conj_vk_cap: &[Target]| {
        let e = endo_apt
            .get(endo_idx)
            .expect("endo-lift expose_claim instance present");
        let c = conj_apt
            .get(conj_idx)
            .expect("conjunction expose_claim instance present");
        debug_assert_eq!(e.len(), ENDO_PI_COUNT);
        debug_assert_eq!(c.len(), CONJ_PI_COUNT);

        // ⚑ THE CARRY. The endo-lift's OUTPUT block IS the conjunction's ξ block, limb for limb,
        // enforced in-circuit rather than asserted by a test over two PI files. The 32 welds are
        // the emitted seam's, applied — not re-derived offsets.
        let issued = apply_seam(cb, e, c, &seam);
        debug_assert_eq!(issued, SK);

        let mut parent: Vec<Target> = Vec::with_capacity(FINALIZE_CLAIM_LEN);
        parent.extend_from_slice(&e[ENDO_PI_VPRIME..ENDO_PI_VPRIME + SK]);
        parent.extend_from_slice(&c[CONJ_PI_ZETA..CONJ_PI_ZETA + SK]);
        parent.extend_from_slice(&c[CONJ_PI_ZETAW..CONJ_PI_ZETAW + SK]);
        parent.extend_from_slice(&c[CONJ_PI_R..CONJ_PI_R + SK]);
        parent.extend_from_slice(&c[CONJ_PI_B0..CONJ_PI_B0 + SK]);
        debug_assert_eq!(parent.len(), FINALIZE_CLAIM_LEN);
        cb.expose_as_public_output(&parent);
    };

    prove_recursion_aggregation_auto_with_expose(&endo_input, &conj_input, config, Some(&expose))
        .map_err(|e| format!("endo -> finalize fold failed: {e}"))
}

/// ⚑ **THE THIRD LEG IS NOW AN EMITTED OBJECT, NOT A FUNCTION IN THIS FILE.**
///
/// The 46-leaf Fq-transcript fold (`mina_phase2_chain_leaf::prove_chain_fold`) exposes
/// `in_state(96) ‖ out_state(96) ‖ transcript_acc(8)`, and `MinaPhase2Chain`'s
/// `the_chain_ends_at_the_blocks_challenges` says outgoing lane 0's **low 128 bits** are the block's
/// own `v′`. Connecting that to [`CLAIM_VPRIME`] is what stops `v′` being a prover-chosen value.
///
/// `connect_chain_root_v_prime` used to live here as Rust index arithmetic — the function `git
/// grep` once found in exactly three places: a docblock, its own definition, and a test saying it
/// is NOT what the test does. It is DELETED, not aliased. The seam is now the Lean-emitted
/// [`crate::seam::v_prime_seam`] (`MinaSeams.vPrimeSeam`, 16 welds + 16 zero-pins — without the
/// zero-pins a prover picks 128 free high bits and "low 128 bits" is not what the weld enforces),
/// with S1 `the_v_prime_seam_is_the_terminal_squeeze` — the theorem the R1 obligation in
/// `mina_kimchi_verifier_gadget.rs` asked for by name — and S2 `v_prime_seam_certifies`
/// (refutable: `v_prime_seam_S2_needs_the_seam`). Its one applier is
/// [`crate::mina_kimchi_verifier_gadget::fold_transcript_into_finalize`], through
/// [`crate::seam::apply_seam`].
///
/// `v′ = LINK_V_RAW % 2^128`, and `128 / 8 = 16`.
pub const V_PRIME_LIMBS: usize = 16;

fn require_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
    role: &str,
    want: usize,
) -> Result<usize, String> {
    let len = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .map_or(0, |e| e.public_values.len());
    if len != want {
        return Err(format!(
            "{role} exposes {len} claim lane(s), expected exactly {want}; refusing an ambiguous \
             claim layout"
        ));
    }
    expose_claim_instance_index(&output.0).ok_or_else(|| {
        format!("{role} carries no expose_claim instance despite its claimed layout")
    })
}

/// Read the `v' ‖ zeta ‖ zetaw ‖ r ‖ b0` claim the fold root publishes.
///
/// ⚑ Canonicalized through `as_canonical_u32`, exactly as `chain_root::read_chain_claim_from_proof`
/// does — a Montgomery representative compared against a decimal fixture is the class of silent
/// disagreement this repo keeps finding.
pub fn read_finalize_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<Vec<BabyBear>> {
    use p3_field::PrimeField32;
    let e = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?;
    if e.public_values.len() != FINALIZE_CLAIM_LEN {
        return None;
    }
    Some(
        e.public_values
            .iter()
            .map(|&v| BabyBear::new(v.as_canonical_u32()))
            .collect(),
    )
}

/// ⚑ **THE ENGINE THE ENDO-LIFT'S AND THE CONJUNCTION'S INNER DESCRIPTOR BATCHES ARE MINTED AT** —
/// and therefore the engine each leaf wrap's in-circuit verifier checks its child against. Pass
/// this to [`prove_endo_lift_leaf`] / [`prove_conjunction_leaf`]; the wrap engine is derived from it
/// by [`recursion_layer_over`], inside the leaf.
///
/// ⚠ It is **NOT** the config the fold runs at or the root verifies under — that is
/// [`finalize_root_config`]. The single `finalize_config()` that used to answer both questions is
/// DELETED rather than aliased: it was only ever right because the two answers coincided.
pub fn finalize_inner_config() -> DreggRecursionConfig {
    ir2_leaf_wrap_config()
}

/// ⚑ **THE ENGINE THE FOLD RUNS AT AND THE ROOT VERIFIES UNDER** — the fixed point of
/// [`recursion_layer_over`], reached by applying it twice to [`finalize_inner_config`] rather than
/// by naming its answer. A leaf wrap emits at `recursion_layer_over(inner)`'s mint knobs, so the
/// fold above it verifies at those; one more application lands on the fixed point and a third
/// changes nothing.
///
/// ⚠ **The finalize root's VK rotates with this.** It is the same engine the phase-2 chain root and
/// the kimchi gadget root now run at, which is what keeps the three towers foldable into each
/// other: an aggregation of two proofs minted at different FRI engines does not build.
pub fn finalize_root_config() -> DreggRecursionConfig {
    recursion_layer_over(&recursion_layer_over(&finalize_inner_config()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_lean_descriptors_declare_the_layouts_this_module_reads() {
        let e = endo_lift_descriptor().expect("the Lean endo-lift descriptor parses");
        assert_eq!(e.name, "dregg-mina-xi-endo-lift::v1");
        assert_eq!(e.public_input_count, ENDO_PI_COUNT);

        let c = conjunction_descriptor().expect("the Lean conjunction descriptor parses");
        assert_eq!(c.name, "dregg-mina-wrap-conjunction::v1");
        assert_eq!(c.public_input_count, CONJ_PI_COUNT);
        assert_eq!(c.trace_width, 2536, "flat in the round count");
    }

    /// The claim layout has no aliasing and the connected block is the one both descriptors call ξ.
    #[test]
    fn the_claim_layout_has_no_aliasing() {
        assert_eq!(ENDO_PI_VPRIME, 0);
        assert_eq!(ENDO_PI_XI, SK);
        assert_eq!(CONJ_PI_XI, 0);
        assert_eq!(FINALIZE_CLAIM_LEN, 160);
        assert_eq!(CLAIM_VPRIME + SK, CLAIM_ZETA);
        assert_eq!(CLAIM_ZETAW + SK, CLAIM_R);
        assert_eq!(CLAIM_R + SK, CLAIM_B0);
        assert_eq!(CLAIM_B0 + SK, FINALIZE_CLAIM_LEN);
        // ⚑ ξ is NOT in the root claim — it is internal to the aggregation.
        assert_eq!(FINALIZE_CLAIM_LEN, CONJ_PI_COUNT);
        // Constant-only: a build obligation (see the same pin in `mina_kimchi_verifier_gadget`).
        const _: () = assert!(V_PRIME_LIMBS < SK, "v' is 128 of 255 bits");
    }
}
