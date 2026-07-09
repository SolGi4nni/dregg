//! Re-prove a BLINDED RING-MEMBERSHIP show's `(blinded_leaf, root)` claim as a
//! RECURSION-FOLDABLE IR-v2 leaf (the blinded-membership analog of
//! [`crate::presentation_leaf_adapter`] / [`crate::membership_leaf_adapter`]).
//!
//! ## What this closes (Golden Lift, stage 3d-3)
//!
//! Stage 3d-2 ([`dregg_circuit::blinded_membership_witness`], `dregg-blinded-membership::v1`) makes
//! an anonymous-credential show's claim — the published `blinded_leaf` (PI 0) and the federation
//! `root` (PI 1) — a genuinely CONSTRAINED, light-client-visible pair of public inputs: `blinded_leaf`
//! is tied in-circuit to `hash_2_to_1(leaf_hash, blinding_factor)` (an arity-2 `TID_P2` chip lookup)
//! and `leaf_hash` is proven to sit under `root` by a 4-ary Poseidon2 Merkle chip chain. But that
//! soundness is LEAF-level. A PURE LIGHT CLIENT that verifies only the AGGREGATED root — the per-turn
//! recursion fold — never re-runs the leaf verifier; for it, the leg's published blinded-membership
//! claim is executor-attested and, absent the fold edge, unbacked. That is the SAME class
//! [`crate::membership_leaf_adapter`] closes for the sender-membership leg and
//! [`crate::presentation_leaf_adapter`] closes for the bound-presentation leg.
//!
//! This module mints the blinded-membership LEAF as a recursion-foldable IR-v2 leaf — the same
//! `aggregate_tree` / chain a light client verifies — and dual-exposes its `(blinded_leaf, root)`
//! claim so the binding node [`prove_blinded_membership_binding_node_segmented`] can `connect` it to
//! the deployed leg's published blinded-membership-claim PIs, exactly as
//! [`crate::presentation_leaf_adapter::prove_presentation_binding_node_segmented`] connects the
//! presentation claim.
//!
//! ## Why the REAL blinded-membership descriptor (not a synthetic tuple)
//!
//! Like the bound-presentation descriptor (and unlike the table-free membership tuple), the
//! blinded-membership descriptor ALREADY binds its whole claim in-circuit: `root` by the last-parent
//! `PiBinding` at the head of a faithful 4-ary `TID_P2` Merkle chip chain, and `blinded_leaf` by the
//! arity-2 blinding `TID_P2` chip lookup over the hidden `(leaf_hash, blinding_factor)`. So the leaf
//! here IS the Stage-3d-2 descriptor (`descriptor_by_name("dregg-blinded-membership::v1")`), proved
//! through the real p3 prover and wrapped as a foldable leaf via
//! [`crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config`]. What the fold dual-exposes
//! is the claim the leaf already binds — a prover cannot expose a claim that disagrees with the
//! descriptor it folded, because both are the SAME in-circuit PI targets.
//!
//! ## The claim layout (`BLINDED_MEMBERSHIP_CLAIM_LEN` = 2)
//!
//! | claim lane | source (blinded-membership descriptor PI)          |
//! |------------|----------------------------------------------------|
//! | `0`        | `blinded_leaf` — PI `BLINDED_LEAF_PI` (the unlinkable commitment) |
//! | `1`        | `root`         — PI `ROOT_PI` (the public federation Merkle root)  |
//!
//! The claim lanes are read from the leaf's OWN FRI-bound descriptor PIs, so the exposed claim is
//! welded to the execution the leaf re-proves.
//!
//! ## THE NAMED BIG-BANG PIECE (the deployed blinded-membership-leg PI exposure)
//!
//! [`prove_blinded_membership_binding_node_segmented`] consumes a DUAL-EXPOSE leg leaf whose
//! `expose_claim` carries the chain SEGMENT in lanes `[0 .. SEG_WIDTH)` AND the claimed
//! `(blinded_leaf, root)` in lanes `[SEG_WIDTH .. SEG_WIDTH+BLINDED_MEMBERSHIP_CLAIM_LEN)`. Adding
//! that PI exposure to the deployed turn leg descriptor is the BIG-BANG DESCRIPTOR PIECE (a
//! PI-exposure change that moves the VK, owned by the descriptor lane). This node + its mechanism
//! (and the leaf below) are READY for it; the mechanism node
//! [`prove_blinded_membership_binding_node`] proves the fold MECHANISM bites today.

use dregg_circuit::blinded_membership_witness::{
    BLINDED_LEAF_PI, BLINDED_MEMBERSHIP_NAME, ROOT_PI, blinded_leaf, blinded_membership_witness,
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

// ---- Blinded-membership-claim layout (the fold's dual-exposed claim lanes) ----
/// Claim lane of `blinded_leaf` — the unlinkable arity-2 Poseidon2 commitment (descriptor PI 0).
pub const CLAIM_BLINDED_LEAF: usize = 0;
/// Claim lane of `root` — the public federation Merkle root (descriptor PI 1).
pub const CLAIM_ROOT: usize = CLAIM_BLINDED_LEAF + 1;
/// The exposed blinded-membership-claim width: `blinded_leaf[1] + root[1]` = the 2 descriptor PIs.
pub const BLINDED_MEMBERSHIP_CLAIM_LEN: usize = CLAIM_ROOT + 1; // 2

/// A blinded-membership show's inputs — the SAME fields the Stage-3d-2 witness builder
/// [`dregg_circuit::blinded_membership_witness::blinded_membership_witness`] consumes. The public
/// claim is `(blinded_leaf, root)`; the member `leaf_hash` and the fresh `blinding_factor` ride as
/// HIDDEN witnesses (unlinkability).
#[derive(Clone, Debug)]
pub struct BlindedMembershipInput {
    /// HIDDEN — the member `leaf_hash` (the Merkle path's leaf AND the blinding tooth's input; NOT a PI).
    pub leaf_hash: BabyBear,
    /// HIDDEN — fresh per-show `blinding_factor` (unlinkability; NOT a PI).
    pub blinding_factor: BabyBear,
    /// Per-level sibling triples (depth 2 — the emitted descriptor's fixed depth).
    pub siblings: Vec<[BabyBear; 3]>,
    /// Per-level child positions — must be `0` (the descriptor pins the member to the leftmost slot).
    pub positions: Vec<u8>,
}

impl BlindedMembershipInput {
    /// The Stage-3d-2 `(base_trace, public_inputs)` for the emitted blinded-membership descriptor.
    /// Errors on a wrong depth or a non-leftmost position (the witness builder's checks).
    pub fn build(&self) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
        blinded_membership_witness(
            self.leaf_hash,
            self.blinding_factor,
            &self.siblings,
            &self.positions,
        )
    }

    /// The 2 descriptor public inputs `[blinded_leaf, root]`.
    pub fn public_inputs(&self) -> Result<Vec<BabyBear>, String> {
        Ok(self.build()?.1)
    }

    /// The blinded-membership base trace (width `BLINDED_WIDTH` = 33).
    pub fn generate_trace(&self) -> Result<Vec<Vec<BabyBear>>, String> {
        Ok(self.build()?.0)
    }

    /// The 2-felt `(blinded_leaf, root)` claim this show binds — the value
    /// [`prove_blinded_membership_leaf_with_claim`] re-exposes and
    /// [`read_exposed_blinded_membership`] reads back. `blinded_leaf` is the GENUINE arity-2
    /// Poseidon2 image of the hidden `(leaf_hash, blinding_factor)`, so an honest claim is not free.
    pub fn claim(&self) -> Result<[BabyBear; BLINDED_MEMBERSHIP_CLAIM_LEN], String> {
        let pis = self.public_inputs()?;
        let mut c = [BabyBear::new(0); BLINDED_MEMBERSHIP_CLAIM_LEN];
        c[CLAIM_BLINDED_LEAF] = pis[BLINDED_LEAF_PI];
        c[CLAIM_ROOT] = pis[ROOT_PI];
        debug_assert_eq!(
            c[CLAIM_BLINDED_LEAF],
            blinded_leaf(self.leaf_hash, self.blinding_factor)
        );
        Ok(c)
    }
}

/// The blinded-membership descriptor the leaf re-proves — the byte-pinned Stage-3d-2 emitted golden
/// dispatched by name (`dregg-blinded-membership::v1`).
pub fn blinded_membership_to_descriptor2() -> Result<EffectVmDescriptor2, String> {
    dregg_circuit::descriptor_by_name::descriptor_by_name(BLINDED_MEMBERSHIP_NAME).ok_or_else(
        || format!("blinded-membership descriptor '{BLINDED_MEMBERSHIP_NAME}' does not dispatch"),
    )
}

/// Prove a blinded membership as a RECURSION-FOLDABLE IR-v2 leaf. `public_inputs` is the 2-slot
/// descriptor PI vector — for an HONEST proof it equals `input.public_inputs()?`. Passing a DIFFERENT
/// PI is a forged binding (trace claims one root/blinded_leaf, PIs another): the descriptor's
/// `PiBinding`s require `row0[col] == pi[col]`, so the mismatch is UNSAT and no foldable leaf is
/// minted.
pub fn prove_blinded_membership_leaf(
    input: &BlindedMembershipInput,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let desc = blinded_membership_to_descriptor2()?;
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
    .map_err(|e| format!("blinded-membership leaf inner IR-v2 prove failed: {e}"))?;

    prove_descriptor_leaf_rotated_with_config(&desc, &inner, public_inputs, config)
        .map_err(|e| format!("blinded-membership leaf recursion wrap failed: {e}"))
}

/// Prove the blinded membership as a foldable leaf AND re-expose its bound 2-felt
/// `(blinded_leaf, root)` (lanes `[0 .. BLINDED_MEMBERSHIP_CLAIM_LEN)`) as a public CLAIM the binding
/// node `connect`s to the deployed leg's published blinded-membership-claim PIs.
///
/// The exposed claim is welded to the execution: a prover cannot expose a claim that disagrees with
/// the show the leaf proves, because the claim lanes are read from the leaf's OWN FRI-bound
/// descriptor PI targets (`blinded_leaf` at `BLINDED_LEAF_PI`, `root` at `ROOT_PI`).
pub fn prove_blinded_membership_leaf_with_claim(
    input: &BlindedMembershipInput,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let desc = blinded_membership_to_descriptor2()?;
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
    .map_err(|e| format!("blinded-membership claim leaf inner IR-v2 prove failed: {e}"))?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &inner, public_inputs, config)
            .map_err(|e| format!("blinded-membership claim verify-triple build failed: {e}"))?;

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
            .expect("blinded-membership leaf has a main instance carrying the descriptor PIs");
        debug_assert!(
            main.len() >= BLINDED_MEMBERSHIP_CLAIM_LEN,
            "main instance must carry the (blinded_leaf, root) PI slots"
        );
        // Re-expose the FRI-bound (blinded_leaf, root) lanes directly (PI 0, PI 1).
        let claim: Vec<Target> = (0..BLINDED_MEMBERSHIP_CLAIM_LEN).map(|k| main[k]).collect();
        cb.expose_as_public_output(&claim);
    };

    build_and_prove_next_layer_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
        &input_ri,
        config,
        &backend,
        &ProveNextLayerParams::default(),
        Some(&expose),
    )
    .map_err(|e| format!("blinded-membership claim leaf-wrap failed: {e:?}"))
}

/// Read the 2-felt `(blinded_leaf, root)` a [`prove_blinded_membership_leaf_with_claim`] leaf
/// exposes through its `expose_claim` table. Returns `None` if the proof carries no claim.
pub fn read_exposed_blinded_membership(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; BLINDED_MEMBERSHIP_CLAIM_LEN]> {
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < BLINDED_MEMBERSHIP_CLAIM_LEN {
        return None;
    }
    Some([claims[CLAIM_BLINDED_LEAF], claims[CLAIM_ROOT]])
}

// ============================================================================
// THE BLINDED-MEMBERSHIP-BINDING FOLD NODES.
// ============================================================================

/// **THE BLINDED-MEMBERSHIP-BINDING MECHANISM NODE (the minimal fold tooth — no segment).**
/// Aggregate a blinded-membership leg leaf (which must RE-EXPOSE its CLAIMED 2-felt
/// `(blinded_leaf, root)` as an `expose_claim`) WITH the re-proved blinded-membership leaf
/// ([`prove_blinded_membership_leaf_with_claim`]), CONNECTING the two claims in-circuit and
/// re-exposing the now-bound claim as the parent claim.
///
/// THE TOOTH: if the leg claims a `(blinded_leaf, root)` the leaf does not bind, the per-lane
/// `connect` is a conflict and the aggregation is UNSAT — no root. This is the blinded-membership
/// twin of [`crate::presentation_leaf_adapter::prove_presentation_binding_node`].
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_blinded_membership_binding_node(
    leg_claim_leaf: &RecursionOutput<DreggRecursionConfig>,
    blinded_membership_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::expose_claim_instance_index;
    use p3_circuit::CircuitBuilder;

    let leg_idx = expose_claim_instance_index(&leg_claim_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "blinded-membership leg leaf carries no re-exposed claim (expose_claim) table — \
                     it must re-expose (blinded_leaf, root)"
                    .to_string(),
        }
    })?;
    let bm_idx = expose_claim_instance_index(&blinded_membership_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "blinded-membership leaf carries no exposed claim (expose_claim) table — it must \
                     be minted via prove_blinded_membership_leaf_with_claim"
                    .to_string(),
        }
    })?;

    let left = leg_claim_leaf.into_recursion_input::<BatchOnly>();
    let right = blinded_membership_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("blinded-membership leg's re-exposed claim instance present");
        let bm = right_apt
            .get(bm_idx)
            .expect("blinded-membership leaf's exposed claim instance present");
        debug_assert!(
            lg.len() >= BLINDED_MEMBERSHIP_CLAIM_LEN && bm.len() >= BLINDED_MEMBERSHIP_CLAIM_LEN
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED (blinded_leaf, root) must equal the
        // leaf's BOUND claim, lane by lane. A forged claim no leaf backs is a conflict ⇒ UNSAT.
        for k in 0..BLINDED_MEMBERSHIP_CLAIM_LEN {
            cb.connect(lg[k], bm[k]);
        }
        let bound: Vec<Target> = (0..BLINDED_MEMBERSHIP_CLAIM_LEN).map(|k| lg[k]).collect();
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
        reason: format!("blinded-membership-binding aggregation node failed: {e:?}"),
    })
}

/// **THE SEGMENT-PRESERVING BLINDED-MEMBERSHIP BINDING NODE (deployed binding, caller-ready — the
/// analog of [`crate::presentation_leaf_adapter::prove_presentation_binding_node_segmented`]).**
/// Aggregate a blinded-membership turn's DUAL-EXPOSE effect-vm leg leaf (whose single `expose_claim`
/// carries the chain SEGMENT in lanes `[0 .. SEG_WIDTH)` and the CLAIMED `(blinded_leaf, root)` in
/// lanes `[SEG_WIDTH .. SEG_WIDTH+BLINDED_MEMBERSHIP_CLAIM_LEN)`) WITH the re-proved
/// blinded-membership leaf ([`prove_blinded_membership_leaf_with_claim`], whose `expose_claim` is the
/// in-circuit-bound claim in lanes `[0 .. BLINDED_MEMBERSHIP_CLAIM_LEN)`), and:
///
///   1. `connect`s the leg's claimed lanes to the leaf's bound claim (the binding tooth — a turn
///      whose teeth name a `(blinded_leaf, root)` no leaf binds is a conflict ⇒ UNSAT ⇒ no root), and
///   2. RE-EXPOSES the leg's SEGMENT lanes `[0 .. SEG_WIDTH)` as the parent claim.
///
/// The output exposes an ordinary `SEG_WIDTH`-lane chain segment, so it folds into
/// [`crate::ivc_turn_chain::aggregate_tree`] like any other per-turn segment leaf — making the
/// blinded membership REAL for a pure light client while preserving the chain endpoints/digest.
///
/// THE NAMED SEAM (honest): the deployed blinded-membership leg must DUAL-EXPOSE its
/// `(blinded_leaf, root)` teeth (lanes `[SEG_WIDTH ..)`). That leg dual-expose is the BIG-BANG
/// DESCRIPTOR PIECE (a PI-exposure change, owned by the descriptor lane). This node is its consumer.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`]. Both children re-expose
/// FRI-bound PI lanes directly (no `recompose/coeff` table), so the plain backend suffices.
pub fn prove_blinded_membership_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    blinded_membership_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::{SEG_WIDTH, expose_claim_instance_index};
    use p3_circuit::CircuitBuilder;

    let ev_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "dual-expose blinded-membership leg leaf carries no expose_claim table — it must \
                     be wrapped to expose (segment ++ (blinded_leaf, root))"
                    .to_string(),
        }
    })?;
    let bm_idx = expose_claim_instance_index(&blinded_membership_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "blinded-membership leaf carries no exposed claim (expose_claim) table — it must \
                     be minted via prove_blinded_membership_leaf_with_claim"
                    .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input::<BatchOnly>();
    let right = blinded_membership_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let ev = left_apt
            .get(ev_idx)
            .expect("dual-expose blinded-membership leg's claim instance present");
        let bm = right_apt
            .get(bm_idx)
            .expect("blinded-membership leaf's exposed claim instance present");
        debug_assert!(
            ev.len() >= SEG_WIDTH + BLINDED_MEMBERSHIP_CLAIM_LEN
                && bm.len() >= BLINDED_MEMBERSHIP_CLAIM_LEN,
            "dual-expose claim must carry segment ++ blinded-membership claim; leaf carries the claim"
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED (blinded_leaf, root) (lanes
        // [SEG_WIDTH .. SEG_WIDTH+BLINDED_MEMBERSHIP_CLAIM_LEN)) must equal the leaf's BOUND claim,
        // lane by lane. A turn whose teeth name a claim no leaf binds is a conflict ⇒ UNSAT ⇒ no root.
        for k in 0..BLINDED_MEMBERSHIP_CLAIM_LEN {
            cb.connect(ev[SEG_WIDTH + k], bm[k]);
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
        reason: format!("segmented blinded-membership-binding aggregation node failed: {e:?}"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;

    /// A distinct-felt honest blinded membership (leftmost-child path, depth 2).
    fn make_input() -> BlindedMembershipInput {
        BlindedMembershipInput {
            leaf_hash: BabyBear::new(1001),
            blinding_factor: BabyBear::new(0xB11D),
            siblings: vec![
                [
                    BabyBear::new(2002),
                    BabyBear::new(3003),
                    BabyBear::new(4004),
                ],
                [
                    BabyBear::new(5005),
                    BabyBear::new(6006),
                    BabyBear::new(7007),
                ],
            ],
            positions: vec![0, 0],
        }
    }

    /// The dispatched leaf descriptor IS the byte-pinned Stage-3d-2 golden (name + shape).
    #[test]
    fn blinded_membership_dispatches_the_descriptor() {
        let desc = blinded_membership_to_descriptor2().expect("blinded-membership dispatches");
        assert_eq!(desc.name, BLINDED_MEMBERSHIP_NAME);
        assert!(!desc.constraints.is_empty());
    }

    /// The claim packing agrees with the descriptor PI offsets it re-exposes.
    #[test]
    fn claim_layout_matches_descriptor_pis() {
        let inp = make_input();
        let pis = inp.public_inputs().expect("witness builds");
        let claim = inp.claim().expect("claim builds");
        assert_eq!(claim.len(), BLINDED_MEMBERSHIP_CLAIM_LEN);
        assert_eq!(claim[CLAIM_BLINDED_LEAF], pis[BLINDED_LEAF_PI]);
        assert_eq!(claim[CLAIM_ROOT], pis[ROOT_PI]);
    }

    /// THE POSITIVE POLE: an honest blinded membership proves as a foldable recursion leaf.
    #[test]
    fn honest_blinded_membership_proves_as_foldable_leaf() {
        let inp = make_input();
        let pis = inp.public_inputs().expect("witness builds");
        let config = ir2_leaf_wrap_config();
        let _output = prove_blinded_membership_leaf(&inp, &pis, &config)
            .expect("the honest blinded membership must prove as a foldable leaf");
    }

    /// THE POSITIVE POLE (claim variant): the claim leaf folds AND re-exposes the bound
    /// 2-felt `(blinded_leaf, root)`.
    #[test]
    fn honest_claim_leaf_exposes_bound_claim() {
        let inp = make_input();
        let pis = inp.public_inputs().expect("witness builds");
        let config = ir2_leaf_wrap_config();
        let output = prove_blinded_membership_leaf_with_claim(&inp, &pis, &config)
            .expect("the claim leaf must fold");
        let exposed = read_exposed_blinded_membership(&output)
            .expect("a blinded-membership claim is exposed");
        assert_eq!(
            exposed,
            inp.claim().expect("claim"),
            "the exposed claim is the bound (blinded_leaf, root)"
        );
    }

    /// UNLINKABILITY (fold level): the SAME member folded with two DIFFERENT blinding factors mints
    /// two foldable leaves whose exposed `blinded_leaf` DIFFER but whose `root` agrees — both fold.
    #[test]
    fn unlinkability_two_foldable_leaves_differ_in_blinded_leaf() {
        let mut a = make_input();
        a.blinding_factor = BabyBear::new(0xB11D);
        let mut b = make_input();
        b.blinding_factor = BabyBear::new(0xDEAD);
        let config = ir2_leaf_wrap_config();

        let out_a = prove_blinded_membership_leaf_with_claim(
            &a,
            &a.public_inputs().expect("a pis"),
            &config,
        )
        .expect("show a folds");
        let out_b = prove_blinded_membership_leaf_with_claim(
            &b,
            &b.public_inputs().expect("b pis"),
            &config,
        )
        .expect("show b folds");
        let ca = read_exposed_blinded_membership(&out_a).expect("a claim");
        let cb = read_exposed_blinded_membership(&out_b).expect("b claim");
        assert_ne!(
            ca[CLAIM_BLINDED_LEAF], cb[CLAIM_BLINDED_LEAF],
            "distinct blinding factors → distinct exposed blinded_leaf (unlinkability)"
        );
        assert_eq!(
            ca[CLAIM_ROOT], cb[CLAIM_ROOT],
            "both shows fold to the same member under the same root"
        );
    }

    /// THE NEGATIVE POLE: a FORGED PI (honest trace, a TAMPERED `root` PI) has no satisfying
    /// assembly — the root pin requires `row0[PARENT1] == pi[ROOT_PI]`, so the mismatch is UNSAT.
    #[test]
    fn forged_blinded_membership_pi_does_not_fold() {
        let inp = make_input();
        let mut forged_pis = inp.public_inputs().expect("witness builds");
        forged_pis[ROOT_PI] += BabyBear::new(1); // root ≠ last parent
        assert_ne!(forged_pis, inp.public_inputs().unwrap());
        let config = ir2_leaf_wrap_config();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_blinded_membership_leaf(&inp, &forged_pis, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => {
                panic!("a FORGED blinded-membership PI minted a foldable leaf — soundness OPEN")
            }
        }
    }

    /// THE FOLD, HONEST: the binding MECHANISM node folds a leg leaf (re-exposing the claim) WITH
    /// the blinded-membership leaf (binding the same claim); the `connect` succeeds and the
    /// aggregate re-exposes the bound `(blinded_leaf, root)`.
    #[test]
    fn honest_fold_binds_and_exposes_claim() {
        let inp = make_input();
        let pis = inp.public_inputs().expect("witness builds");
        let config = ir2_leaf_wrap_config();

        let leg =
            prove_blinded_membership_leaf_with_claim(&inp, &pis, &config).expect("leg claim leaf");
        let leaf = prove_blinded_membership_leaf_with_claim(&inp, &pis, &config)
            .expect("blinded-membership leaf");

        let folded = prove_blinded_membership_binding_node(&leg, &leaf, &config)
            .expect("the honest fold must bind and produce a root");
        let exposed = read_exposed_blinded_membership(&folded)
            .expect("the fold re-exposes the now-bound claim");
        assert_eq!(
            exposed,
            inp.claim().expect("claim"),
            "the aggregate exposes the bound (blinded_leaf, root)"
        );
    }

    /// THE FOLD, FORGED: a leg that CLAIMS a different show (a forged member under a different root)
    /// than the leaf binds is a per-lane `connect` conflict ⇒ UNSAT ⇒ no root.
    #[test]
    fn forged_claim_fold_does_not_bind() {
        let honest = make_input();
        let honest_pis = honest.public_inputs().expect("witness builds");
        // A DIFFERENT (but internally-honest) show: a forged member → a different root + blinded_leaf.
        let mut forged = make_input();
        forged.leaf_hash = BabyBear::new(9999);
        let forged_pis = forged.public_inputs().expect("witness builds");
        assert_ne!(honest_pis, forged_pis);
        let config = ir2_leaf_wrap_config();

        let leg = prove_blinded_membership_leaf_with_claim(&forged, &forged_pis, &config)
            .expect("the forged leg is itself a valid blinded-membership leaf");
        let leaf = prove_blinded_membership_leaf_with_claim(&honest, &honest_pis, &config)
            .expect("the honest blinded-membership leaf");

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_blinded_membership_binding_node(&leg, &leaf, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!(
                "a leg claiming a show the leaf does not bind produced a root — binding OPEN"
            ),
        }
    }
}
