//! ⚑⚑ **`SeamSpec` — the seam is an OBJECT the fold READS, not index arithmetic the fold authors.**
//!
//! ## The wound this closes
//!
//! Four "true about the wrong object" incidents share one form: *a claim true of the FOLD,
//! attributed to the AIR*. The canonical instance: `MinaWrapConjunctionAir.xiCorrectLegs` is a
//! column equality between two blocks its own `no_arithmetic_call_names_an_xi_block` proves FREE;
//! the forcing lives in [`crate::mina_wrap_finalize_fold::fold_endo_into_finalize`]'s 32
//! `cb.connect`s. Nothing unsound — but no OBJECT carried "this conjunct is forced by seam S".
//! Only prose did, and prose is invisible to every census instrument in the tree.
//!
//! ## What this module is
//!
//! A reader for the Lean-emitted seam artifacts (`circuit/descriptors/seams/*.json`, authored by
//! `metatheory/Dregg2/Circuit/Emit/MinaSeams.lean`, rendered by `EmitSeamSpecs.lean`) and ONE
//! generic [`apply_seam`]. A fold function that used to write `for i in 0..SK { cb.connect(...) }`
//! now parses its seam and applies it — the index arithmetic has exactly one author, and that
//! author proves S1 ("the pin list names exactly the published slots it claims to") and S2 (the
//! composition theorem, shown refutable) about it.
//!
//! ⚑ **The descriptor key is the fingerprint, not the name.** A [`SeamEnd`] carries the nine
//! `Faithful9` lanes of `effect_vm_descriptor2_semantic_fingerprint`; [`SeamEnd::require_matches`]
//! RECOMPUTES them from the descriptor actually loaded and refuses a mismatch. Display names have
//! collided in this tree before; lanes have not.
//!
//! ⚠ **Standing.** `apply_seam` issues recursion wiring — `cb.connect` over targets the child
//! verifiers already bound. It authors no AIR (House Law #1 holds), proves on a box, and inherits
//! the undischarged FRI/STARK floor. The gain is provenance and closure-kind honesty: "closed by
//! seam S, theorem S2" is now a checkable sentence.

use dregg_circuit::descriptor_ir2::EffectVmDescriptor2;
use dregg_circuit::descriptor_ir2_canonical::effect_vm_descriptor2_semantic_fingerprint;
use dregg_circuit::faithful9::Faithful9;
use p3_recursion::Target;
use serde::Deserialize;

use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;

type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

/// One end of a seam: which claim layout, how many lanes, and which Lean-emitted descriptor
/// grounds the welded slots — keyed by name AND fingerprint lanes.
#[derive(Debug, Clone, Deserialize)]
pub struct SeamEnd {
    pub claim: String,
    pub claim_len: usize,
    pub descriptor: String,
    pub lanes: Vec<u64>,
}

/// The Lean-emitted seam: elementwise welds plus zero-pins, in claim indices of each end.
#[derive(Debug, Clone, Deserialize)]
pub struct SeamSpec {
    pub name: String,
    pub left: SeamEnd,
    pub right: SeamEnd,
    pub pins: Vec<(usize, usize)>,
    pub zero_left: Vec<usize>,
    pub zero_right: Vec<usize>,
}

impl SeamEnd {
    /// ⚑ Refuse unless `desc` is the descriptor this end names — by NAME and by RECOMPUTED
    /// fingerprint lanes. A stale lane literal in the emitted seam (the `ABSORB_VK_LANES` class)
    /// is a loud error here, not a silent misname.
    pub fn require_matches(&self, desc: &EffectVmDescriptor2) -> Result<(), String> {
        if desc.name != self.descriptor {
            return Err(format!(
                "seam end names descriptor `{}` but was handed `{}`",
                self.descriptor, desc.name
            ));
        }
        let fp = effect_vm_descriptor2_semantic_fingerprint(desc).map_err(|e| {
            format!(
                "descriptor `{}` is not fingerprint-representable: {e}",
                desc.name
            )
        })?;
        let lanes = Faithful9::from_key_lanes9(&fp).lanes();
        let recomputed: Vec<u64> = lanes.iter().map(|l| l.as_u32() as u64).collect();
        if recomputed != self.lanes {
            return Err(format!(
                "seam end `{}`: fingerprint lanes disagree — seam carries {:?}, descriptor \
                 recomputes {:?}; the emitted seam is stale against the served descriptor",
                self.descriptor, self.lanes, recomputed
            ));
        }
        Ok(())
    }
}

impl SeamSpec {
    /// Parse an emitted seam artifact.
    pub fn parse(json: &str) -> Result<Self, String> {
        let s: SeamSpec =
            serde_json::from_str(json).map_err(|e| format!("seam spec parse failed: {e}"))?;
        s.validate()?;
        Ok(s)
    }

    /// The Lean `SeamSpec.wf` verdict, re-checked on the artifact: indices in range, nine lanes
    /// per end, and non-empty.
    pub fn validate(&self) -> Result<(), String> {
        let name = &self.name;
        for &(l, r) in &self.pins {
            if l >= self.left.claim_len || r >= self.right.claim_len {
                return Err(format!("seam `{name}`: pin ({l},{r}) out of range"));
            }
        }
        if let Some(i) = self.zero_left.iter().find(|&&i| i >= self.left.claim_len) {
            return Err(format!("seam `{name}`: zero_left {i} out of range"));
        }
        if let Some(i) = self.zero_right.iter().find(|&&i| i >= self.right.claim_len) {
            return Err(format!("seam `{name}`: zero_right {i} out of range"));
        }
        if self.pins.is_empty() && self.zero_left.is_empty() && self.zero_right.is_empty() {
            return Err(format!(
                "seam `{name}` is empty — an empty seam forces nothing"
            ));
        }
        if self.left.lanes.len() != 9 || self.right.lanes.len() != 9 {
            return Err(format!(
                "seam `{name}`: an end does not carry nine fingerprint lanes"
            ));
        }
        Ok(())
    }

    /// Total in-circuit constraints this seam issues.
    pub fn connect_count(&self) -> usize {
        self.pins.len() + self.zero_left.len() + self.zero_right.len()
    }
}

/// ⚑ **THE ONE APPLICATOR.** Issue every weld and zero-pin of `spec` over two FRI-bound claim
/// slices. Panics (inside proof construction, before any proof exists) if the claim widths do not
/// match the seam — the caller is expected to have refused mismatched shapes already via
/// `require_claim`; this is the last-line shape check, not the refusal.
///
/// Returns the number of connects issued, so call sites can assert their documented totals.
pub fn apply_seam(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    left: &[Target],
    right: &[Target],
    spec: &SeamSpec,
) -> usize {
    assert_eq!(
        left.len(),
        spec.left.claim_len,
        "seam `{}`: left claim has {} lanes, spec says {}",
        spec.name,
        left.len(),
        spec.left.claim_len
    );
    assert_eq!(
        right.len(),
        spec.right.claim_len,
        "seam `{}`: right claim has {} lanes, spec says {}",
        spec.name,
        right.len(),
        spec.right.claim_len
    );
    for &(l, r) in &spec.pins {
        cb.connect(left[l], right[r]);
    }
    if !spec.zero_left.is_empty() || !spec.zero_right.is_empty() {
        // A `connect` to a `define_const` IS a pin at the pinned fork rev — measured in
        // `const_pin_probe.rs`, not read off a docblock.
        let zero = cb.alloc_const(
            <RecursionChallenge as p3_field::PrimeCharacteristicRing>::ZERO,
            "seam zero-pin target",
        );
        for &i in &spec.zero_left {
            cb.connect(left[i], zero);
        }
        for &i in &spec.zero_right {
            cb.connect(right[i], zero);
        }
    }
    spec.connect_count()
}

/// The ξ seam: `fold_endo_into_finalize`'s 32 welds.
/// Lean: `MinaSeams.xiSeam`; S1 `the_xi_seam_welds_the_lift_to_the_record`;
/// S2 `xi_seam_certifies`, refuted without its hypothesis by `xi_seam_S2_needs_the_seam`.
pub fn xi_seam() -> Result<SeamSpec, String> {
    SeamSpec::parse(include_str!(
        "../../circuit/descriptors/seams/seam-xi-endo-to-conjunction.json"
    ))
}

/// The `v′` seam: the kimchi gadget's 16 welds + 16 zero-pins.
/// Lean: `MinaSeams.vPrimeSeam`; S1 `the_v_prime_seam_is_the_terminal_squeeze`;
/// S2 `v_prime_seam_certifies`, refuted without its hypothesis by `v_prime_seam_S2_needs_the_seam`.
pub fn v_prime_seam() -> Result<SeamSpec, String> {
    SeamSpec::parse(include_str!(
        "../../circuit/descriptors/seams/seam-chain-vprime-to-finalize.json"
    ))
}

/// The fresh-sponge seam: the kimchi gadget's 96 zero-pins.
/// Lean: `MinaSeams.freshSpongeSeam`; S1 `the_fresh_sponge_seam_zeroes_the_whole_incoming_state`;
/// S2 `fresh_sponge_seam_certifies`.
pub fn fresh_sponge_seam() -> Result<SeamSpec, String> {
    SeamSpec::parse(include_str!(
        "../../circuit/descriptors/seams/seam-chain-fresh-sponge.json"
    ))
}

/// ⚑ The head↔link seam: the executor's REFUSAL 13/14a/14b as an object — nine tip pins (the
/// head descriptor's `LINK_OK`-guarded `proof_bind` commit surface, welded elementwise), nine
/// anchor pins and the anchor-height pin (head slot 29 ↔ link slot 18).
/// Lean: `MinaSeams.headTipSeam`; S1 `the_head_tip_seam_welds_published_slots`.
///
/// ⚠ APPLIED BY THE EXECUTOR, not by a fold: `dregg_turn::executor::mina_head_verifier::
/// check_segment_binding` performs these comparisons natively after verifying both STARKs (both
/// polarities in its release tests). REFUSAL 14c (`link PI[19] = head PI[18] − head PI[29]`) is
/// AFFINE and outside `SeamSpec`'s vocabulary — the seam is nineteen of the twenty refusals, and
/// the twentieth stays the executor's alone.
pub fn head_tip_seam() -> Result<SeamSpec, String> {
    SeamSpec::parse(include_str!(
        "../../circuit/descriptors/seams/seam-head-tip-to-link.json"
    ))
}
