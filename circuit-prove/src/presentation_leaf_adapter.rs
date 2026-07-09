//! Re-prove a BOUND-PRESENTATION turn's authorization claim as a RECURSION-FOLDABLE
//! IR-v2 leaf (the presentation analog of [`crate::membership_leaf_adapter`]).
//!
//! ## What this closes (Golden Lift, stage 3b-i)
//!
//! Stage 3a ([`dregg_circuit::bound_presentation_witness`], `dregg-bound-presentation::v1`)
//! makes a presentation's authorization claim — `action_binding[8]` (PI 1..8),
//! `revealed_facts[8]` (PI 11..18) and the `presentation_tag` (PI 10, constrained
//! in-circuit to `Poseidon2(final_root, presentation_randomness, verifier_nonce, DSK)`) — a
//! genuinely CONSTRAINED, light-client-visible set of public inputs, and its forge-teeth
//! BITE at the LEAF (`BoundPresentationRung2`). But that soundness is LEAF-level: it
//! certifies a single re-proved bound-presentation trace. A PURE LIGHT CLIENT that verifies
//! only the AGGREGATED root — the per-turn recursion fold — never re-runs the leaf verifier;
//! for it, the leg's published presentation claim is executor-attested and, absent the fold
//! edge, unbacked. That is the SAME class [`crate::membership_leaf_adapter`] closes for the
//! sender-membership leg.
//!
//! This module mints the bound-presentation LEAF as a recursion-foldable IR-v2 leaf — the
//! same `aggregate_tree` / chain a light client verifies — and dual-exposes its
//! authorization claim `(action_binding, revealed_facts, tag)` so the binding node
//! [`prove_presentation_binding_node_segmented`] can `connect` it to the deployed leg's
//! published presentation-claim PIs, exactly as
//! [`crate::membership_leaf_adapter::prove_membership_binding_node_segmented`] connects the
//! membership tuple. It is the Rust realization of the Stage-2 Lean proof
//! [`metatheory/Dregg2/Circuit/PresentationBindingFromFold.lean`]
//! (`presentation_binding_from_fold`): a verifying aggregate FORCES the leg's published
//! presentation claim to be backed by a verifying bound-presentation sub-proof.
//!
//! ## Why the REAL bound-presentation descriptor (not a synthetic tuple)
//!
//! Unlike the membership tuple (a table-free `(sender_leaf, authorized_root)` pair whose
//! Merkle path stays off-AIR), the bound-presentation descriptor ALREADY binds its whole
//! claim in-circuit: `action_binding`/`revealed_facts` by per-row `PiBinding`s and the
//! `presentation_tag` by a faithful arity-4 `TID_P2` Poseidon2 chip lookup over the hidden
//! preimage `(final_root, randomness, verifier_nonce, DSK)`. So the leaf here IS the
//! Stage-3a descriptor (`descriptor_by_name("dregg-bound-presentation::v1")`), proved through
//! the real p3 prover and wrapped as a foldable leaf via
//! [`crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config`]. What the fold
//! dual-exposes is the claim the leaf already binds — a prover cannot expose a claim that
//! disagrees with the descriptor it folded, because both are the SAME in-circuit PI targets.
//!
//! ## The claim layout (`PRESENTATION_CLAIM_LEN` = 17)
//!
//! The exposed claim is the authorization commitments a light client checks, packed in a
//! fixed order that the leg re-exposes IDENTICALLY:
//!
//! | claim lane            | source (bound-presentation descriptor PI)               |
//! |-----------------------|---------------------------------------------------------|
//! | `[0 .. 8)`            | `action_binding`  — PI `[REQUEST_PREDICATE_BASE .. +8)` |
//! | `[8 .. 16)`           | `revealed_facts`  — PI `[REVEALED_FACTS_BASE .. +8)`    |
//! | `16`                  | `presentation_tag` — PI `PRESENTATION_TAG`             |
//!
//! The claim lanes are read from the leaf's OWN FRI-bound descriptor PIs (not free prover
//! scalars), so the exposed claim is welded to the execution the leaf re-proves.
//!
//! ## THE NAMED BIG-BANG PIECE (the deployed presentation-leg PI exposure)
//!
//! [`prove_presentation_binding_node_segmented`] consumes a DUAL-EXPOSE leg leaf whose
//! `expose_claim` carries the chain SEGMENT in lanes `[0 .. SEG_WIDTH)` AND the claimed
//! `(action_binding, revealed_facts, tag)` in lanes
//! `[SEG_WIDTH .. SEG_WIDTH+PRESENTATION_CLAIM_LEN)`. **Adding that presentation-claim PI
//! exposure to the deployed turn leg descriptor is the BIG-BANG DESCRIPTOR PIECE (a
//! PI-exposure change that moves the VK, owned by the descriptor lane).** This node + its
//! mechanism (and the leaf below) are READY for it; the mechanism node
//! [`prove_presentation_binding_node`] proves the fold MECHANISM bites today.

use dregg_circuit::bound_presentation_witness::{
    BOUND_PRESENTATION_NAME, PRESENTATION_TAG, REQUEST_PREDICATE_BASE, REVEALED_FACTS_BASE,
    bound_presentation_tag, bound_presentation_witness,
};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2Air, MemBoundaryWitness, UMemBoundaryWitness,
    ir2_airs_and_common_for_config, prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;

use p3_field::PrimeField32;
use p3_recursion::{
    BatchOnly, ProveNextLayerParams, RecursionInput, RecursionOutput, Target,
    build_and_prove_aggregation_layer_with_expose, build_and_prove_next_layer_with_expose,
};
use p3_uni_stark::StarkGenericConfig;

use crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config;
use crate::joint_turn_aggregation::JointAggError;
use crate::plonky3_recursion_impl::recursive::{DreggRecursionConfig, create_recursion_backend};

type RecursionChallenge = <DreggRecursionConfig as StarkGenericConfig>::Challenge;
const D: usize = 4;

// ---- Presentation-claim layout (the fold's dual-exposed claim lanes) ----
/// Claim lane base of `action_binding` (8 felts) — the requested-action commitment.
pub const CLAIM_ACTION_BASE: usize = 0;
/// Claim lane base of `revealed_facts` (8 felts) — the disclosed-attributes commitment.
pub const CLAIM_FACTS_BASE: usize = CLAIM_ACTION_BASE + 8;
/// Claim lane of `presentation_tag` — the Poseidon2 image of the hidden tag preimage.
pub const CLAIM_TAG: usize = CLAIM_FACTS_BASE + 8;
/// The exposed presentation-claim width: `action_binding[8] + revealed_facts[8] + tag[1]`.
pub const PRESENTATION_CLAIM_LEN: usize = CLAIM_TAG + 1; // 17

/// A bound-presentation turn's inputs — the SAME fields the Stage-3a witness builder
/// [`dregg_circuit::bound_presentation_witness::bound_presentation_witness`] consumes. The
/// public authorization claim is `(action_binding, revealed_facts, presentation_tag)`; the
/// tag preimage (`final_root`, `randomness`) rides as a HIDDEN witness (unlinkability).
#[derive(Clone, Copy, Debug)]
pub struct BoundPresentationInput {
    /// PI 0 — the federation-root anchor (summary copy).
    pub federation_root: BabyBear,
    /// PI 1..8 — the requested-action commitment (`request_predicate`, 8 felts).
    pub action_binding: [BabyBear; 8],
    /// PI 9 — the presentation timestamp.
    pub timestamp: BabyBear,
    /// PI 11..18 — the revealed-facts commitment (8 felts).
    pub revealed_facts: [BabyBear; 8],
    /// HIDDEN — end-of-chain state root (part of the tag preimage; NOT a PI).
    pub final_root: BabyBear,
    /// HIDDEN — fresh per-presentation randomness (unlinkability; NOT a PI).
    pub randomness: BabyBear,
    /// PI 19 — the verifier's public nonce challenge.
    pub verifier_nonce: BabyBear,
    /// Base-trace height — a power of two ≥ 2.
    pub height: usize,
}

impl BoundPresentationInput {
    /// The Stage-3a `(base_trace, public_inputs)` for the emitted bound-presentation
    /// descriptor. Errors on a non-power-of-two height (the witness builder's check).
    pub fn build(&self) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
        bound_presentation_witness(
            self.federation_root,
            self.action_binding,
            self.timestamp,
            self.revealed_facts,
            self.final_root,
            self.randomness,
            self.verifier_nonce,
            self.height,
        )
    }

    /// The 20 descriptor public inputs `[summary(0..18)] ++ [verifier_nonce]`.
    pub fn public_inputs(&self) -> Result<Vec<BabyBear>, String> {
        Ok(self.build()?.1)
    }

    /// The bound-presentation base trace (width `BOUND_PRES_WIDTH` = 29).
    pub fn generate_trace(&self) -> Result<Vec<Vec<BabyBear>>, String> {
        Ok(self.build()?.0)
    }

    /// The 17-felt authorization claim `(action_binding, revealed_facts, tag)` this
    /// presentation binds — the value [`prove_presentation_leaf_with_claim`] re-exposes and
    /// [`read_exposed_presentation`] reads back. The tag is the GENUINE Poseidon2 image of
    /// the hidden preimage (the internalized chip tooth), so an honest claim is not free.
    pub fn claim(&self) -> [BabyBear; PRESENTATION_CLAIM_LEN] {
        let mut c = [BabyBear::new(0); PRESENTATION_CLAIM_LEN];
        c[CLAIM_ACTION_BASE..CLAIM_ACTION_BASE + 8].copy_from_slice(&self.action_binding);
        c[CLAIM_FACTS_BASE..CLAIM_FACTS_BASE + 8].copy_from_slice(&self.revealed_facts);
        c[CLAIM_TAG] =
            bound_presentation_tag(self.final_root, self.randomness, self.verifier_nonce);
        c
    }
}

/// The bound-presentation descriptor the leaf re-proves — the byte-pinned Stage-3a emitted
/// golden dispatched by name (`dregg-bound-presentation::v1`).
pub fn presentation_to_descriptor2() -> Result<EffectVmDescriptor2, String> {
    dregg_circuit::descriptor_by_name::descriptor_by_name(BOUND_PRESENTATION_NAME).ok_or_else(
        || format!("bound-presentation descriptor '{BOUND_PRESENTATION_NAME}' does not dispatch"),
    )
}

/// Prove a bound presentation as a RECURSION-FOLDABLE IR-v2 leaf. `public_inputs` is the
/// 20-slot descriptor PI vector — for an HONEST proof it equals `input.public_inputs()?`.
/// Passing a DIFFERENT summary PI is a forged binding (trace claims one summary, PIs another):
/// the descriptor's `PiBinding`s require `row0[col] == pi[col]`, so the mismatch is UNSAT and
/// no foldable leaf is minted.
pub fn prove_presentation_leaf(
    input: &BoundPresentationInput,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let desc = presentation_to_descriptor2()?;
    let base_trace = input.generate_trace()?;

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("bound-presentation leaf inner IR-v2 prove failed: {e}"))?;

    prove_descriptor_leaf_rotated_with_config(&desc, &inner, public_inputs, config)
        .map_err(|e| format!("bound-presentation leaf recursion wrap failed: {e}"))
}

/// Prove the bound presentation as a foldable leaf AND re-expose its bound 17-felt
/// authorization claim `(action_binding, revealed_facts, tag)` (lanes
/// `[0 .. PRESENTATION_CLAIM_LEN)`) as a public CLAIM the binding node `connect`s to the
/// deployed leg's published presentation-claim PIs.
///
/// The exposed claim is welded to the execution: a prover cannot expose a claim that
/// disagrees with the presentation the leaf proves, because the claim lanes are read from the
/// leaf's OWN FRI-bound descriptor PI targets (`action_binding` at `REQUEST_PREDICATE_BASE`,
/// `revealed_facts` at `REVEALED_FACTS_BASE`, tag at `PRESENTATION_TAG`).
pub fn prove_presentation_leaf_with_claim(
    input: &BoundPresentationInput,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let desc = presentation_to_descriptor2()?;
    let base_trace = input.generate_trace()?;

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("bound-presentation claim leaf inner IR-v2 prove failed: {e}"))?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &inner, public_inputs, config)
            .map_err(|e| format!("bound-presentation claim verify-triple build failed: {e}"))?;

    let input_ri: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &inner,
            common_data: &common,
            table_public_inputs,
        };

    // Plain backend: a direct-lane re-expose carries no decompose/coeff table.
    let backend = create_recursion_backend();

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<Target>]| {
        let main = apt
            .first()
            .expect("bound-presentation leaf has a main instance carrying the descriptor PIs");
        debug_assert!(
            main.len() > PRESENTATION_TAG.max(REVEALED_FACTS_BASE + 7),
            "main instance must carry the presentation claim PI slots"
        );
        // Re-expose the FRI-bound claim lanes directly, in the fixed
        // (action_binding ++ revealed_facts ++ tag) order.
        let mut claim: Vec<Target> = Vec::with_capacity(PRESENTATION_CLAIM_LEN);
        for k in 0..8 {
            claim.push(main[REQUEST_PREDICATE_BASE + k]);
        }
        for k in 0..8 {
            claim.push(main[REVEALED_FACTS_BASE + k]);
        }
        claim.push(main[PRESENTATION_TAG]);
        debug_assert_eq!(claim.len(), PRESENTATION_CLAIM_LEN);
        cb.expose_as_public_output(&claim);
    };

    build_and_prove_next_layer_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
        &input_ri,
        config,
        &backend,
        &ProveNextLayerParams::default(),
        Some(&expose),
    )
    .map_err(|e| format!("bound-presentation claim leaf-wrap failed: {e:?}"))
}

/// Read the 17-felt `(action_binding, revealed_facts, tag)` a
/// [`prove_presentation_leaf_with_claim`] leaf exposes through its `expose_claim` table.
/// Returns `None` if the proof carries no claim.
pub fn read_exposed_presentation(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; PRESENTATION_CLAIM_LEN]> {
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < PRESENTATION_CLAIM_LEN {
        return None;
    }
    let mut out = [BabyBear::new(0); PRESENTATION_CLAIM_LEN];
    out.copy_from_slice(&claims[..PRESENTATION_CLAIM_LEN]);
    Some(out)
}

// ============================================================================
// THE PRESENTATION-BINDING FOLD NODES.
// ============================================================================

/// **THE PRESENTATION-BINDING MECHANISM NODE (the minimal fold tooth — no segment).**
/// Aggregate a presentation leg leaf (which must RE-EXPOSE its CLAIMED 17-felt
/// `(action_binding, revealed_facts, tag)` as an `expose_claim`) WITH the re-proved
/// bound-presentation leaf ([`prove_presentation_leaf_with_claim`]), CONNECTING the two claims
/// in-circuit and re-exposing the now-bound claim as the parent claim.
///
/// THE TOOTH: if the leg claims a presentation the bound-presentation leaf does not bind, the
/// per-lane `connect` is a conflict and the aggregation is UNSAT — no root. This is the
/// presentation twin of [`crate::membership_leaf_adapter::prove_membership_binding_node`], the
/// Rust realization of `PresentationBindingFromFold.presentation_binding_from_fold`'s `connect`.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_presentation_binding_node(
    leg_claim_leaf: &RecursionOutput<DreggRecursionConfig>,
    presentation_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::expose_claim_instance_index;
    use p3_circuit::CircuitBuilder;

    let leg_idx = expose_claim_instance_index(&leg_claim_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "presentation leg leaf carries no re-exposed claim (expose_claim) table — it \
                     must re-expose (action_binding, revealed_facts, tag)"
                .to_string(),
        }
    })?;
    let pr_idx = expose_claim_instance_index(&presentation_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "bound-presentation leaf carries no exposed claim (expose_claim) table — it \
                     must be minted via prove_presentation_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = leg_claim_leaf.into_recursion_input::<BatchOnly>();
    let right = presentation_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("presentation leg's re-exposed claim instance present");
        let pr = right_apt
            .get(pr_idx)
            .expect("bound-presentation leaf's exposed claim instance present");
        debug_assert!(lg.len() >= PRESENTATION_CLAIM_LEN && pr.len() >= PRESENTATION_CLAIM_LEN);
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED presentation must equal the
        // bound-presentation leaf's BOUND claim, lane by lane. A forged claim no
        // bound-presentation leaf backs is a conflict here ⇒ UNSAT ⇒ no root.
        for k in 0..PRESENTATION_CLAIM_LEN {
            cb.connect(lg[k], pr[k]);
        }
        let bound: Vec<Target> = (0..PRESENTATION_CLAIM_LEN).map(|k| lg[k]).collect();
        cb.expose_as_public_output(&bound);
    };

    build_and_prove_aggregation_layer_with_expose::<
        DreggRecursionConfig,
        BatchOnly,
        BatchOnly,
        _,
        D,
    >(&left, &right, config, &backend, &params, None, Some(&expose))
    .map_err(|e| JointAggError::AggregationProofInvalid {
        reason: format!("presentation-binding aggregation node failed: {e:?}"),
    })
}

/// **THE SEGMENT-PRESERVING PRESENTATION BINDING NODE (deployed presentation-binding,
/// caller-ready — the analog of
/// [`crate::membership_leaf_adapter::prove_membership_binding_node_segmented`]).** Aggregate a
/// presentation turn's DUAL-EXPOSE effect-vm leg leaf (whose single `expose_claim` carries the
/// chain SEGMENT in lanes `[0 .. SEG_WIDTH)` and the CLAIMED `(action_binding, revealed_facts,
/// tag)` in lanes `[SEG_WIDTH .. SEG_WIDTH+PRESENTATION_CLAIM_LEN)`) WITH the re-proved
/// bound-presentation leaf ([`prove_presentation_leaf_with_claim`], whose `expose_claim` is the
/// in-circuit-bound claim in lanes `[0 .. PRESENTATION_CLAIM_LEN)`), and:
///
///   1. `connect`s the leg's claimed lanes to the bound-presentation leaf's bound claim (the
///      binding tooth — a turn whose teeth name a presentation no bound-presentation leaf binds
///      is a conflict ⇒ UNSAT ⇒ no root), and
///   2. RE-EXPOSES the leg's SEGMENT lanes `[0 .. SEG_WIDTH)` as the parent claim.
///
/// The output exposes an ordinary `SEG_WIDTH`-lane chain segment, so it folds into
/// [`crate::ivc_turn_chain::aggregate_tree`] like any other per-turn segment leaf — making the
/// presentation authorization REAL for a pure light client while preserving the chain
/// endpoints/digest.
///
/// THE NAMED SEAM (honest): the deployed presentation leg must DUAL-EXPOSE its
/// `(action_binding, revealed_facts, tag)` teeth (lanes `[SEG_WIDTH ..)`). That leg dual-expose
/// is the BIG-BANG DESCRIPTOR PIECE (a PI-exposure change, owned by the descriptor lane). This
/// node is its consumer.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`]. Both children re-expose
/// FRI-bound PI lanes directly (no `recompose/coeff` table), so the plain backend suffices.
pub fn prove_presentation_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    presentation_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::{SEG_WIDTH, expose_claim_instance_index};
    use p3_circuit::CircuitBuilder;

    let ev_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "dual-expose presentation leg leaf carries no expose_claim table — it must be \
                     wrapped to expose (segment ++ (action_binding, revealed_facts, tag))"
                .to_string(),
        }
    })?;
    let pr_idx = expose_claim_instance_index(&presentation_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "bound-presentation leaf carries no exposed claim (expose_claim) table — it \
                     must be minted via prove_presentation_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input::<BatchOnly>();
    let right = presentation_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let ev = left_apt
            .get(ev_idx)
            .expect("dual-expose presentation leg's claim instance present");
        let pr = right_apt
            .get(pr_idx)
            .expect("bound-presentation leaf's exposed claim instance present");
        debug_assert!(
            ev.len() >= SEG_WIDTH + PRESENTATION_CLAIM_LEN && pr.len() >= PRESENTATION_CLAIM_LEN,
            "dual-expose claim must carry segment ++ presentation claim; leaf carries the claim"
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED presentation (lanes
        // [SEG_WIDTH .. SEG_WIDTH+PRESENTATION_CLAIM_LEN)) must equal the bound-presentation
        // leaf's BOUND claim, lane by lane. A turn whose teeth name a presentation no leaf
        // binds is a conflict here ⇒ UNSAT ⇒ no root.
        for k in 0..PRESENTATION_CLAIM_LEN {
            cb.connect(ev[SEG_WIDTH + k], pr[k]);
        }
        // RE-EXPOSE ONLY THE SEGMENT (lanes [0 .. SEG_WIDTH)) as the parent claim.
        let seg: Vec<Target> = (0..SEG_WIDTH).map(|k| ev[k]).collect();
        cb.expose_as_public_output(&seg);
    };

    build_and_prove_aggregation_layer_with_expose::<
        DreggRecursionConfig,
        BatchOnly,
        BatchOnly,
        _,
        D,
    >(&left, &right, config, &backend, &params, None, Some(&expose))
    .map_err(|e| JointAggError::AggregationProofInvalid {
        reason: format!("segmented presentation-binding aggregation node failed: {e:?}"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;

    /// A distinct-felt honest bound presentation at the minimal power-of-two height.
    fn make_input() -> BoundPresentationInput {
        BoundPresentationInput {
            federation_root: BabyBear::new(111),
            action_binding: std::array::from_fn(|k| BabyBear::new(200 + k as u32)),
            timestamp: BabyBear::new(300),
            revealed_facts: std::array::from_fn(|k| BabyBear::new(500 + k as u32)),
            final_root: BabyBear::new(0xF1A1),
            randomness: BabyBear::new(0xB11D),
            verifier_nonce: BabyBear::new(0xC0FFEE),
            height: 2,
        }
    }

    /// The dispatched leaf descriptor IS the byte-pinned Stage-3a golden (name + shape).
    #[test]
    fn presentation_dispatches_the_bound_descriptor() {
        let desc = presentation_to_descriptor2().expect("bound-presentation dispatches");
        assert_eq!(desc.name, BOUND_PRESENTATION_NAME);
        // exactly one arity-4 chip lookup (the internalized tag-binding tooth) lives in it.
        assert!(!desc.constraints.is_empty());
    }

    /// The claim packing agrees with the descriptor PI offsets it re-exposes.
    #[test]
    fn claim_layout_matches_descriptor_pis() {
        let inp = make_input();
        let pis = inp.public_inputs().expect("witness builds");
        let claim = inp.claim();
        assert_eq!(claim.len(), PRESENTATION_CLAIM_LEN);
        for k in 0..8 {
            assert_eq!(
                claim[CLAIM_ACTION_BASE + k],
                pis[REQUEST_PREDICATE_BASE + k]
            );
            assert_eq!(claim[CLAIM_FACTS_BASE + k], pis[REVEALED_FACTS_BASE + k]);
        }
        assert_eq!(claim[CLAIM_TAG], pis[PRESENTATION_TAG]);
    }

    /// THE POSITIVE POLE: an honest bound presentation proves as a foldable recursion leaf.
    #[test]
    fn honest_presentation_proves_as_foldable_leaf() {
        let inp = make_input();
        let pis = inp.public_inputs().expect("witness builds");
        let config = ir2_leaf_wrap_config();
        let _output = prove_presentation_leaf(&inp, &pis, &config)
            .expect("the honest bound presentation must prove as a foldable leaf");
    }

    /// THE POSITIVE POLE (claim variant): the claim leaf folds AND re-exposes the bound
    /// 17-felt `(action_binding, revealed_facts, tag)`.
    #[test]
    fn honest_claim_leaf_exposes_bound_claim() {
        let inp = make_input();
        let pis = inp.public_inputs().expect("witness builds");
        let config = ir2_leaf_wrap_config();
        let output = prove_presentation_leaf_with_claim(&inp, &pis, &config)
            .expect("the claim leaf must fold");
        let exposed = read_exposed_presentation(&output).expect("a presentation claim is exposed");
        assert_eq!(
            exposed,
            inp.claim(),
            "the exposed claim is the bound (action_binding, revealed_facts, tag)"
        );
    }

    /// THE NEGATIVE POLE: a FORGED summary PI (honest trace, a TAMPERED `action_binding[0]` PI)
    /// has no satisfying assembly — the descriptor's `PiBinding` requires `row0[col] == pi[col]`,
    /// so the mismatch is UNSAT. No foldable leaf is minted.
    #[test]
    fn forged_presentation_pi_does_not_fold() {
        let inp = make_input();
        let mut forged_pis = inp.public_inputs().expect("witness builds");
        forged_pis[REQUEST_PREDICATE_BASE] += BabyBear::new(1); // action_binding[0] ≠ row
        assert_ne!(forged_pis, inp.public_inputs().unwrap());
        let config = ir2_leaf_wrap_config();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_presentation_leaf(&inp, &forged_pis, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => {
                panic!("a FORGED presentation PI minted a foldable leaf — soundness OPEN")
            }
        }
    }

    /// THE FOLD, HONEST: the presentation-binding MECHANISM node folds a leg leaf (re-exposing
    /// the claim) WITH the bound-presentation leaf (binding the same claim); the `connect`
    /// succeeds and the aggregate re-exposes the bound authorization claim. This is the Rust
    /// realization of `presentation_binding_from_fold` — the leg's claim is FORCED backed.
    #[test]
    fn honest_fold_binds_and_exposes_claim() {
        let inp = make_input();
        let pis = inp.public_inputs().expect("witness builds");
        let config = ir2_leaf_wrap_config();

        // Both children re-expose the SAME 17-felt claim: the "leg" (executor-attested) and the
        // re-proved bound-presentation leaf.
        let leg = prove_presentation_leaf_with_claim(&inp, &pis, &config).expect("leg claim leaf");
        let leaf =
            prove_presentation_leaf_with_claim(&inp, &pis, &config).expect("presentation leaf");

        let folded = prove_presentation_binding_node(&leg, &leaf, &config)
            .expect("the honest presentation fold must bind and produce a root");
        let exposed = read_exposed_presentation(&folded)
            .expect("the fold re-exposes the now-bound authorization claim");
        assert_eq!(
            exposed,
            inp.claim(),
            "the aggregate exposes the bound (action_binding, revealed_facts, tag)"
        );
    }

    /// THE FOLD, FORGED: a leg that CLAIMS a different presentation (a forged `action_binding`)
    /// than the bound-presentation leaf binds is a per-lane `connect` conflict ⇒ UNSAT ⇒ no
    /// root. What the deployed light client alone would admit, the aggregate REFUSES.
    #[test]
    fn forged_claim_fold_does_not_bind() {
        let honest = make_input();
        let honest_pis = honest.public_inputs().expect("witness builds");
        // A DIFFERENT (but internally-honest) presentation: a forged requested action.
        let mut forged = honest;
        forged.action_binding[0] += BabyBear::new(1);
        let forged_pis = forged.public_inputs().expect("witness builds");
        let config = ir2_leaf_wrap_config();

        // The leg claims the FORGED presentation; the re-proved leaf binds the HONEST one.
        let leg = prove_presentation_leaf_with_claim(&forged, &forged_pis, &config)
            .expect("the forged leg is itself a valid bound-presentation leaf");
        let leaf = prove_presentation_leaf_with_claim(&honest, &honest_pis, &config)
            .expect("the honest presentation leaf");

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_presentation_binding_node(&leg, &leaf, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!(
                "a leg claiming a presentation the leaf does not bind produced a root — \
                 binding OPEN"
            ),
        }
    }
}
