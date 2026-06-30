//! GOLD: genuine recursive N-to-1 joint-turn aggregation — REAL descriptor leaves.
//!
//! ## Silver -> Gold, for real
//!
//! [`joint_turn_aggregation`](crate::joint_turn_aggregation) is **Silver**: a
//! bundle = {N per-cell whole-turn proofs} + ONE aggregation STARK that binds
//! their shared turn id (CG-2) and folds their commitments. The verifier still
//! re-runs verification on **every** per-cell proof, so verification cost
//! grows linearly with the number of cells.
//!
//! This module is **Gold**: it recursively verifies the N per-cell whole-turn
//! proofs *in-circuit* — plus the shared-turn-id binding layer — and folds them
//! into ONE succinct recursive (batch-STARK) proof via the emberian
//! `plonky3-recursion` fork. The verifier checks **one** root proof whose cost
//! does **not** grow with the number of cells. That is the constant-verifier
//! property the Golden Vision asks for.
//!
//! ## The recursion tree
//!
//! ```text
//!   per-cell leaves           binding leaf
//!   ┌─────────┐ ┌─────────┐   ┌────────────┐
//!   │ cell 0  │ │ cell 1  │…  │ shared-tid │   (uni-STARK inner proofs)
//!   │ DESC AIR│ │ DESC AIR│   │  + digest  │
//!   └────┬────┘ └────┬────┘   └─────┬──────┘
//!        │  next-layer (uni→batch)  │            build_and_prove_next_layer
//!   ┌────▼────┐ ┌────▼────┐   ┌─────▼──────┐
//!   │ batch 0 │ │ batch 1 │…  │  batch_b   │
//!   └────┬────┘ └────┬────┘   └─────┬──────┘
//!        └─────┬─────┘  2-to-1 aggregation     build_and_prove_aggregation_layer
//!         ┌────▼────┐        …                  (BatchOnly chaining up the tree)
//!         │ agg L1  │ … pairwise to a single root
//!         └────┬────┘
//!         ┌────▼────┐
//!         │  ROOT   │  ONE succinct batch-STARK proof  ← verifier checks ONLY this
//!         └─────────┘
//! ```
//!
//! Each leaf is a genuine recursion-compatible uni-STARK proof:
//!   - per-cell leaves: **the Lean-descriptor EffectVM AIR itself**
//!     ([`EffectVmDescriptorAir`], the graduated ONE-circuit cutover constraint
//!     set — Poseidon2 state-commit hash sites, per-row gates, transition
//!     continuity, `OLD/NEW_COMMIT` PI bindings, range checks), re-proven over
//!     each cell's REAL 186-column execution trace via the SAME
//!     [`prove_descriptor_leaf`](crate::ivc_turn_chain) recipe the whole-chain
//!     fold cut over to. The descriptor PI prefix includes the
//!     [`pi::TURN_HASH_BASE`] slot, so each leaf's wrap binds the shared turn
//!     id AND the cell's genuine state commitments in-circuit;
//!   - binding leaf: [`JointTurnAggregationAir`] over the N participants,
//!     enforcing CG-2 (every cell's `shared_turn_id == published id`) and the
//!     commitment hash-chain digest.
//!
//! The former `EffectVmShapeAir` SHAPE-STUB leaves (a passthrough trace any
//! fabricated `cell_commit` could satisfy — per-cell execution soundness
//! rested on the host gate) are GONE. The discriminating check that earns the
//! claim is `ungated_joint_prover_with_forged_cell_commit_cannot_produce_a_root`:
//! a prover that SKIPS the host-side descriptor admission and forges a
//! post-state commitment has NO satisfying leaf — the descriptor's hash sites
//! force the commit cells to be the genuine Poseidon2 digests — so no root
//! exists. The host gate is an admission discipline, not the soundness
//! boundary.
//!
//! ## What the verifier checks
//!
//! [`verify_joint_turn_recursive`] mirrors the whole-chain verifier's three
//! teeth (see [`crate::ivc_turn_chain`]'s module docs for the precise
//! guarantee statements and the fork follow-up each one names):
//!
//!   1. **VK pin** — the root's verifier-key fingerprint
//!      ([`RecursionVk`]) must equal a caller-held trust anchor;
//!   2. **claimed-publics attestation** — the carried `shared_turn_id` /
//!      `bundle_digest` must verify as the public inputs of the carried
//!      binding proof (Fiat–Shamir binds them);
//!   3. **the root** batch-STARK proof verifies.
//!
//! The residual floor is the same as the whole-chain fold's, named there once:
//! engine soundness (`recursive_sound`), child-circuit identity under the
//! harness VK pin, and cross-leaf public-value linkage — all three pinned to
//! the same precise fork follow-up (thread `table_public_inputs` up the tree +
//! host-check the circuit public vector).

use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing as _;
use p3_recursion::ProveNextLayerParams;
use p3_recursion::build_and_prove_next_layer;
use p3_recursion::{BatchOnly, RecursionInput, RecursionOutput};

use crate::joint_turn_aggregation::{
    DescriptorParticipant, JointAggError, JointTurnAggregationAir, verify_descriptor_participant,
};
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, RecursionCompatibleProof, RecursionVk, create_recursion_backend,
    prove_inner_for_air_with_config, recursion_vk_fingerprint, verify_inner_for_air_with_config,
    verify_recursive_batch_proof_with_config,
};
use dregg_circuit::field::BabyBear;

const D: usize = 4;

/// IR2 PI slot the deployed `customVmDescriptor2R24` publishes its `custom_proof_commitment` at
/// (the Lean `customPiExposure`; see `effect_vm/trace_rotated.rs::generate_rotated_custom_wide` —
/// the four `custom_proof_commitment` limbs land at IR2 PI 46..49, the four low
/// `custom_program_vk_hash` limbs at 50..53).
pub const CUSTOM_COMMIT_PI_LO: usize = 46;
/// Width of the `custom_proof_commitment` claim (4 felts).
pub const CUSTOM_COMMIT_LEN: usize = 4;

fn to_p3(v: BabyBear) -> P3BabyBear {
    P3BabyBear::from_u64(v.0 as u64)
}

// ============================================================================
// Per-cell input: a whole-turn descriptor proof + the trace it attests.
// ============================================================================

/// One cell's contribution to a joint turn on the Gold path: its whole-turn
/// DESCRIPTOR-INTERPRETER proof ([`DescriptorParticipant`]) plus the
/// 186-column execution trace the proof attests — the prover-side witness from
/// which the in-circuit leaf is re-proven. Identical in shape and recipe to
/// the whole-chain fold's per-turn input; the joint aggregator additionally
/// reads [`pi::TURN_HASH_BASE`](dregg_circuit::effect_vm::pi) (the shared turn id)
/// out of the PI prefix, which the descriptor leaf's wrap binds in-circuit.
pub type JointCell = crate::ivc_turn_chain::FinalizedTurn;

// NOTE (Bucket-F / PATH-PRESERVE Phase 5a): the v1 binding leaf (`prove_binding_leaf`, which
// read the v1-prefix `cell_commit` via `recursion_binding_trace_descriptor`) is DELETED. The
// rotated joint fold builds its CG-2 binding trace over the ROTATED commitments via
// `recursion_binding_trace_descriptor_rotated` (see `prove_joint_core_rotated`).

// ============================================================================
// The Gold artifact.
// ============================================================================

/// The Gold deliverable: ONE succinct recursive proof attesting that **all** N
/// per-cell whole-turn DESCRIPTOR leaves AND the shared-turn-id binding leaf
/// verified in-circuit. The verifier checks only this root proof (plus the VK
/// pin and the carried binding attestation); cost is independent of the number
/// of cells.
pub struct RecursiveJointTurnProof {
    /// The single root batch-STARK proof (the whole tree folded to one).
    pub root: RecursionOutput<DreggRecursionConfig>,
    /// The binding uni-STARK (the SAME statement the fold wraps in-circuit),
    /// carried so the verifier checks the claimed publics below AGAINST A
    /// PROOF instead of trusting bare fields (Fiat–Shamir binds them).
    pub binding_proof: RecursionCompatibleProof,
    /// The shared turn id all participants agreed on.
    pub shared_turn_id: BabyBear,
    /// The bundle digest: the hash-chain fold of the ordered
    /// `(shared_turn_id, cell_commit)` pairs the binding leaf attests.
    pub bundle_digest: BabyBear,
    /// The number of participating cells.
    pub num_cells: usize,
}

impl RecursiveJointTurnProof {
    /// The root proof's verifier-key fingerprint — see
    /// [`WholeChainProof::root_vk_fingerprint`](crate::ivc_turn_chain::WholeChainProof::root_vk_fingerprint)
    /// for the trust-anchor discipline (an honest SETUP extracts it once; a
    /// verifier must never take it from the artifact under verification).
    pub fn root_vk_fingerprint(&self) -> RecursionVk {
        recursion_vk_fingerprint(&self.root.0)
    }
}

/// Prove a joint (cross-cell) turn **recursively**: fold the N per-cell
/// whole-turn ROTATED proofs and the shared-turn-id binding into ONE
/// succinct recursive proof.
///
/// **Bucket-F (PATH-PRESERVE Phase 5a):** the per-cell leaf is the MANDATORY ROTATED multi-table
/// `Ir2BatchProof` (carried on `participant.rotated`), wrapped in-circuit via
/// [`crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config`] — the v1
/// `EffectVmDescriptorAir` leaf is gone. This entry now routes straight to the rotated core.
///
/// Steps:
///   1. host admission: >= 2 cells; every cell's ROTATED proof verifies SELECTOR-BOUND through
///      [`verify_descriptor_participant`] (which also determines each cell's selector); all cells
///      agree on the shared turn id (CG-2, host side);
///   2. prove the binding leaf over the ROTATED commitments (rejects disagreeing turn ids
///      in-circuit too);
///   3. mint each cell's ROTATED descriptor leaf in-circuit;
///   4. wrap every leaf in its own IN-CIRCUIT verifier layer (uni→batch);
///   5. pairwise-aggregate all batch leaves up a binary tree to ONE root.
///
/// The host gate (step 1) is an admission discipline, NOT the soundness
/// boundary: a prover that skips it
/// ([`prove_joint_turn_recursive_without_host_gate`]) still cannot produce a
/// verifying root for a forged cell, because a forged `cell_commit` has no
/// satisfying descriptor leaf.
pub fn prove_joint_turn_recursive(
    cells: &[JointCell],
) -> Result<RecursiveJointTurnProof, JointAggError> {
    if cells.len() < 2 {
        return Err(JointAggError::TooFewParticipants { count: cells.len() });
    }
    // (1a) per-cell descriptor admission, selector-bound.
    let mut selectors = Vec::with_capacity(cells.len());
    for (i, c) in cells.iter().enumerate() {
        let s = verify_descriptor_participant(&c.participant)
            .map_err(|reason| JointAggError::ParticipantProofInvalid { index: i, reason })?;
        selectors.push(s);
    }
    // (1b) CG-2 host check.
    let shared_tid = cells[0].participant.shared_turn_id();
    for (i, c) in cells.iter().enumerate() {
        if c.participant.shared_turn_id() != shared_tid {
            return Err(JointAggError::SharedTurnIdMismatch {
                index: i,
                expected: shared_tid.0,
                found: c.participant.shared_turn_id().0,
            });
        }
    }
    let refs: Vec<&JointCell> = cells.iter().collect();
    prove_joint_core_rotated(&refs, &selectors)
}

/// **THE UNGATED PROVER (tamper surface).** Fold a joint turn WITHOUT the
/// host-side descriptor admission, taking the prover's CLAIMED selectors at
/// face value. Exists to make the soundness claim falsifiable: a malicious
/// prover that skips the gate and feeds a forged `cell_commit` still has to
/// satisfy the REAL ROTATED descriptor AIR at the leaf — and a forged commitment has
/// no satisfying witness, so the fold fails and no verifying root exists
/// (`ungated_joint_prover_with_forged_cell_commit_cannot_produce_a_root`).
pub fn prove_joint_turn_recursive_without_host_gate(
    cells: &[JointCell],
    claimed_selectors: &[usize],
) -> Result<RecursiveJointTurnProof, JointAggError> {
    let refs: Vec<&JointCell> = cells.iter().collect();
    prove_joint_core_rotated(&refs, claimed_selectors)
}

// ============================================================================
// THE ROTATED joint fold (Bucket-F: the ONLY joint fold — the v1 `prove_joint_core`
// + v1 leaf are deleted; both public entries route here).
// ============================================================================

/// Prove a joint turn recursively through the ROTATED leaf-wrap: every per-cell leaf is the
/// rotated multi-table `Ir2BatchProof` (carried on `participant.rotated`), minted in-circuit
/// via [`crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config`] at
/// [`crate::ivc_turn_chain::ir2_leaf_wrap_config`]. The whole tree runs at the wrap config.
pub fn prove_joint_turn_recursive_rotated(
    cells: &[JointCell],
) -> Result<RecursiveJointTurnProof, JointAggError> {
    if cells.len() < 2 {
        return Err(JointAggError::TooFewParticipants { count: cells.len() });
    }
    // (1a) per-cell descriptor admission, selector-bound (host gate).
    let mut selectors = Vec::with_capacity(cells.len());
    for (i, c) in cells.iter().enumerate() {
        let s = verify_descriptor_participant(&c.participant)
            .map_err(|reason| JointAggError::ParticipantProofInvalid { index: i, reason })?;
        selectors.push(s);
    }
    let refs: Vec<&JointCell> = cells.iter().collect();
    prove_joint_core_rotated(&refs, &selectors)
}

/// The rotated joint fold core: like [`prove_joint_core`] but mints rotated native-batch
/// leaves and runs the whole tree at the wrap config.
fn prove_joint_core_rotated(
    cells: &[&JointCell],
    selectors: &[usize],
) -> Result<RecursiveJointTurnProof, JointAggError> {
    use crate::ivc_turn_chain::{ir2_leaf_wrap_config, prove_descriptor_leaf_rotated_with_config};
    use crate::joint_turn_aggregation::recursion_binding_trace_descriptor_rotated;

    if selectors.len() != cells.len() {
        return Err(JointAggError::AggregationProofInvalid {
            reason: format!(
                "selector count {} != cell count {}",
                selectors.len(),
                cells.len()
            ),
        });
    }
    let participants: Vec<&DescriptorParticipant> = cells.iter().map(|c| &c.participant).collect();

    let config = ir2_leaf_wrap_config();
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // (2) binding leaf over the ROTATED commitments (shared-tid agreement + digest).
    // Bucket-F fix: the binding-leaf inner proof MUST be minted at the wrap config (log_blowup 6),
    // the SAME FRI engine the whole rotated tree runs at — proving it at the default
    // `create_recursion_config` (log_blowup 3) and then wrapping at the wrap config raises
    // `InvalidProofShape("Fewer siblings in proof than op_ids provided")` in-circuit.
    let (binding_matrix, binding_pis) = recursion_binding_trace_descriptor_rotated(&participants)?;
    let binding_air = JointTurnAggregationAir;
    let binding_inner =
        prove_inner_for_air_with_config(&binding_air, binding_matrix, &binding_pis, &config);
    verify_inner_for_air_with_config(&binding_air, &binding_inner, &binding_pis, &config)
        .map_err(|reason| JointAggError::AggregationProofInvalid { reason })?;
    let shared_turn_id = binding_pis[0];
    let bundle_digest = binding_pis[2];

    // (3)+(4) one rotated descriptor leaf per cell.
    let mut batch_leaves: Vec<RecursionOutput<DreggRecursionConfig>> =
        Vec::with_capacity(cells.len() + 1);
    for (i, c) in cells.iter().enumerate() {
        // Bucket-F: the rotated leg is MANDATORY (`DescriptorParticipant` carries exactly one),
        // so it is read directly — no `Option`, no v1 fallback leg.
        let leg = &c.participant.rotated;
        let wrapped = prove_descriptor_leaf_rotated_with_config(
            &leg.descriptor,
            &leg.proof,
            &leg.public_inputs,
            &config,
        )
        .map_err(|reason| JointAggError::ParticipantProofInvalid { index: i, reason })?;
        batch_leaves.push(wrapped);
    }

    // The binding leaf wrapped uni->batch at the wrap config.
    {
        let p3_pis: Vec<P3BabyBear> = binding_pis.iter().map(|&v| to_p3(v)).collect();
        let input = RecursionInput::UniStark {
            proof: &binding_inner,
            air: &binding_air,
            public_inputs: p3_pis,
            preprocessed_commit: None,
        };
        let wrapped =
            build_and_prove_next_layer::<DreggRecursionConfig, JointTurnAggregationAir, _, D>(
                &input, &config, &backend, &params,
            )
            .map_err(|e| JointAggError::AggregationProofInvalid {
                reason: format!("recursive binding layer failed: {e:?}"),
            })?;
        batch_leaves.push(wrapped);
    }

    // (5) Pairwise-aggregate up a binary tree to ONE root batch proof.
    let root = aggregate_tree(batch_leaves, &config, &backend, &params)?;

    Ok(RecursiveJointTurnProof {
        root,
        binding_proof: binding_inner,
        shared_turn_id,
        bundle_digest,
        num_cells: cells.len(),
    })
}

/// Fold a vector of batch-STARK proofs to ONE via 2-to-1 aggregation layers.
///
/// On each level, consecutive pairs are aggregated with
/// [`build_and_prove_aggregation_layer`](p3_recursion::build_and_prove_aggregation_layer)
/// (chained via [`BatchOnly`]). An odd proof out is carried to the next level
/// unchanged. Repeats until one remains.
fn aggregate_tree(
    mut proofs: Vec<RecursionOutput<DreggRecursionConfig>>,
    config: &DreggRecursionConfig,
    backend: &p3_recursion::FriRecursionBackendForExt<D, 16, 8, p3_recursion::ops::Poseidon2Config>,
    params: &ProveNextLayerParams,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    if proofs.is_empty() {
        return Err(JointAggError::AggregationProofInvalid {
            reason: "no leaves to aggregate".to_string(),
        });
    }

    while proofs.len() > 1 {
        let mut next_level: Vec<RecursionOutput<DreggRecursionConfig>> =
            Vec::with_capacity(proofs.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < proofs.len() {
            let left = proofs[i].into_recursion_input::<BatchOnly>();
            let right = proofs[i + 1].into_recursion_input::<BatchOnly>();
            let out = p3_recursion::build_and_prove_aggregation_layer::<
                DreggRecursionConfig,
                BatchOnly,
                BatchOnly,
                _,
                D,
            >(&left, &right, config, backend, params, None)
            .map_err(|e| JointAggError::AggregationProofInvalid {
                reason: format!("aggregation layer failed: {e:?}"),
            })?;
            next_level.push(out);
            i += 2;
        }
        // Carry an odd proof out to the next level.
        if i < proofs.len() {
            next_level.push(proofs.pop().unwrap());
        }
        proofs = next_level;
    }

    Ok(proofs.pop().unwrap())
}

/// Verify the Gold artifact against a caller-held trust anchor. Three teeth
/// (the joint mirror of
/// [`verify_turn_chain_recursive`](crate::ivc_turn_chain::verify_turn_chain_recursive),
/// whose docs state precisely what each guarantees):
///
///   1. **VK pin** — the presented root's verifier-key fingerprint must equal
///      `expected_vk`;
///   2. **claimed-publics attestation** — the carried
///      `shared_turn_id`/`bundle_digest` must verify as the carried binding
///      proof's public inputs;
///   3. **the root** batch-STARK proof verifies (cost independent of the
///      number of cells — the per-cell proofs are folded inside).
pub fn verify_joint_turn_recursive(
    proof: &RecursiveJointTurnProof,
    expected_vk: &RecursionVk,
) -> Result<(), JointAggError> {
    // (1) VK pin.
    let found = recursion_vk_fingerprint(&proof.root.0);
    if found != *expected_vk {
        return Err(JointAggError::VkFingerprintMismatch {
            expected: expected_vk.to_hex(),
            found: found.to_hex(),
        });
    }

    // (2) Claimed publics, read against the carried binding proof. The binding proof is minted
    // at the rotated leaf-wrap config (log_blowup 6, `prove_joint_core_rotated`), so it must be
    // verified under that SAME config.
    let claimed_pis = vec![proof.shared_turn_id, BabyBear::ZERO, proof.bundle_digest];
    verify_inner_for_air_with_config(
        &JointTurnAggregationAir,
        &proof.binding_proof,
        &claimed_pis,
        &crate::ivc_turn_chain::ir2_leaf_wrap_config(),
    )
    .map_err(|reason| JointAggError::ClaimedPublicsUnattested { reason })?;

    // (3) The root. The root batch proof is produced by `aggregate_tree` at the rotated
    // leaf-wrap config (`ir2_leaf_wrap_config`, log_blowup 6 / 19 queries — the SAME FRI engine
    // the whole rotated tree runs at), NOT the default `create_recursion_config` (log_blowup 3 /
    // 38 queries). It MUST be verified under that same config, else FRI reconstruction expects
    // the wrong query count (`QueryProofCountMismatch { expected: 38, got: 19 }`).
    verify_recursive_batch_proof_with_config(
        &proof.root.0,
        &crate::ivc_turn_chain::ir2_leaf_wrap_config(),
    )
    .map_err(|reason| JointAggError::AggregationProofInvalid { reason })
}

// ============================================================================
// THE CUSTOM-EFFECT FOLD-WIRE (the deployed realization of the binding
// `StarkSoundCustom` falsely assumed).
// ============================================================================
//
// A `Custom` effect's effect-vm leg publishes a CLAIMED `custom_proof_commitment` at IR2 PI
// slots 46..49 (`customVmDescriptor2R24` / Lean `customPiExposure`). On its own that is an
// UNBACKED claim: the in-AIR `proof_bind` op is a declaration, so a re-executing validator runs
// `CellProgram::verify_transition` OFF-AIR but a PURE LIGHT CLIENT (folding only the recursion
// tree) never witnesses the sub-proof. `StarkSoundCustom` ASSUMED `proofBind ⟹ ∃ verifying
// sub-proof`; over the deployed AIR that gate is `True` and the assumption is vacuous.
//
// This fold-wire makes it REAL. For a custom turn the fold aggregates TWO leaves:
//   * the effect-vm leg leaf, RE-EXPOSING its claimed 4-felt commitment (PI 46..49) through the
//     `expose_claim` channel ([`crate::ivc_turn_chain::prove_descriptor_leaf_with_pi_slice_expose`]
//     — the inner PIs themselves are consumed into the primitive `Public` table and never reach a
//     combine hook, so the re-expose is mandatory);
//   * the custom SUB-PROOF leaf, exposing its GENUINE in-circuit-computed PI-commitment
//     ([`crate::custom_leaf_adapter::prove_custom_leaf_with_commitment`]).
// The combine hook `connect`s the two 4-felt claims lane-by-lane. A turn whose effect-vm row
// claims a commitment NO verifying sub-proof backs is now UNSAT: there is no satisfying custom
// leaf whose exposed commitment equals the claimed slots 46..49, so the aggregate does not prove
// — the binding a light client witnesses by folding the tree.

/// Aggregate a custom turn's effect-vm leg leaf (which must RE-EXPOSE its claimed 4-felt
/// `custom_proof_commitment` at PI 46..49 via
/// [`crate::ivc_turn_chain::prove_descriptor_leaf_with_pi_slice_expose`]) WITH the custom
/// sub-proof leaf (which exposes its genuine commitment via
/// [`crate::custom_leaf_adapter::prove_custom_leaf_with_commitment`]), CONNECTING the two 4-felt
/// claims in-circuit.
///
/// Both children carry exactly one `expose_claim` table (the 4-felt commitment claim). The combine
/// hook reads each, `connect`s them lane-by-lane (`connect`, never `sub`+`assert_zero`, to keep the
/// equality off the shared zero witness), and re-exposes the now-bound commitment as the parent
/// claim so the node folds onward like any other leaf.
///
/// THE TOOTH: if the effect-vm leg claims a commitment the custom sub-proof does not back, the
/// per-lane `connect` is a conflict and the aggregation is UNSAT — no root. There is no separate,
/// swappable backing: the custom leaf's commitment is bound in-circuit to the sub-proof's REAL PIs
/// ([`crate::custom_leaf_adapter::incircuit_custom_pi_commitment`]), so a forged claim has no
/// satisfying partner.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`] (both leaves are minted under
/// it). The connecting node uses the coeff-forced backend
/// ([`create_recursion_backend_with_coeff_lookups`]) because the custom sub-proof child carries the
/// `recompose/coeff` table (its commitment expose decomposes one ext limb into 4 consecutive base
/// lanes); the table is inert for the effect-vm child.
pub fn prove_custom_binding_node(
    effectvm_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    custom_subproof_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::expose_claim_instance_index;
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend_with_coeff_lookups;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let ev_idx = expose_claim_instance_index(&effectvm_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "effect-vm custom leg leaf carries no re-exposed commitment (expose_claim) \
                     table — it must be wrapped via prove_descriptor_leaf_with_pi_slice_expose \
                     (pi_lo=46, len=4)"
                .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&custom_subproof_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "custom sub-proof leaf carries no exposed commitment (expose_claim) table — \
                     it must be minted via prove_custom_leaf_with_commitment"
                .to_string(),
        }
    })?;

    let left = effectvm_leg_leaf.into_recursion_input::<BatchOnly>();
    let right = custom_subproof_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend_with_coeff_lookups();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let ev = left_apt
            .get(ev_idx)
            .expect("effect-vm leg's re-exposed commitment instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("custom sub-proof's exposed commitment instance present");
        debug_assert!(ev.len() >= CUSTOM_COMMIT_LEN && cs.len() >= CUSTOM_COMMIT_LEN);

        // THE BINDING TOOTH, IN-CIRCUIT: the effect-vm leg's CLAIMED commitment (PI 46..49,
        // re-exposed) must equal the custom sub-proof's GENUINE in-circuit commitment, lane by
        // lane. A forged claim with no backing sub-proof is a conflict here ⇒ UNSAT ⇒ no root.
        for k in 0..CUSTOM_COMMIT_LEN {
            cb.connect(ev[k], cs[k]);
        }
        // Re-expose the now-bound commitment as the parent claim (the node folds onward like any
        // leaf carrying an `expose_claim`).
        let bound: Vec<Target> = (0..CUSTOM_COMMIT_LEN).map(|k| ev[k]).collect();
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
        reason: format!("custom-binding aggregation node failed: {e:?}"),
    })
}

// ============================================================================
// Tests
// ============================================================================
//
// Bucket-F (PATH-PRESERVE Phase 5a): the in-lib `#[cfg(test)] mod tests` (the 3-cell
// recursive joint, disagreeing-turn-id CG-2, tampered-participant, ungated-forged-cell-commit,
// and in-circuit-wrap teeth) RELOCATED to the integration test
// `circuit/tests/joint_turn_recursive_rotated.rs`, which mints the mandatory ROTATED
// participant through `dregg_turn::rotation_witness::mint_rotated_participant_leg` (the
// circuit lib cannot — no `dregg-cell` / `dregg-turn` dep, the cycle).

// ============================================================================
// THE CUSTOM-EFFECT FOLD-WIRE TEETH (in-lib — no rotated mint needed).
//
// These exercise the deployed binding MECHANISM directly: the REAL custom sub-proof leaf
// (`prove_custom_leaf_with_commitment`, the deployed custom-leaf adapter) folded against an
// effect-vm leg leaf that PUBLISHES a claimed `custom_proof_commitment` at IR2 PI 46..49 — the
// exact slot semantics the deployed `customVmDescriptor2R24` `customPiExposure` uses (four
// `PiBinding .first` pins). The leg leaf here is a minimal PiBinding-only IR2 descriptor standing
// in for the 789-wide deployed trace at the SAME exposure surface (binding the literal 789-wide
// `customVmDescriptor2R24` leg end-to-end is the heavier `dregg-turn` custom-mint integration
// follow-up; this proves the fold-wire + the tooth bite over the deployed slot + the deployed
// custom leaf).
// ============================================================================
#[cfg(test)]
mod custom_fold_wire_tests {
    use super::*;
    use crate::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
    };
    use crate::custom_proof_bind::custom_proof_pi_commitment;
    use crate::ivc_turn_chain::{ir2_leaf_wrap_config, prove_descriptor_leaf_with_pi_slice_expose};
    use dregg_circuit::descriptor_ir2::{
        EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, VmConstraint2,
        prove_vm_descriptor2_for_config,
    };
    use dregg_circuit::dsl::circuit::{
        CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
    };
    use dregg_circuit::field::BABYBEAR_P;
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
    use std::collections::HashMap;

    /// The same minimal-but-REAL custom program the off-AIR engine + custom-leaf adapter tests
    /// use: one boolean column + one conservation polynomial (the sovereign-transfer shape).
    fn demo_program() -> CellProgram {
        let p_minus_1 = BabyBear::new(BABYBEAR_P - 1);
        let descriptor = CircuitDescriptor {
            name: "dregg-custom-demo-v1".to_string(),
            trace_width: 4,
            max_degree: 2,
            columns: vec![
                ColumnDef {
                    name: "old".into(),
                    index: 0,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "amt".into(),
                    index: 1,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "new".into(),
                    index: 2,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "dir".into(),
                    index: 3,
                    kind: ColumnKind::Binary,
                },
            ],
            constraints: vec![
                ConstraintExpr::Binary { col: 3 },
                ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![2],
                        },
                        PolyTerm {
                            coeff: p_minus_1,
                            col_indices: vec![0],
                        },
                        PolyTerm {
                            coeff: p_minus_1,
                            col_indices: vec![1],
                        },
                        PolyTerm {
                            coeff: BabyBear::new(2),
                            col_indices: vec![3, 1],
                        },
                    ],
                },
            ],
            boundaries: vec![],
            public_input_count: 2,
            lookup_tables: vec![],
        };
        CellProgram::new(descriptor, 1)
    }

    /// Honest witness for a credit (dir=0): new = old + amt, constant across rows.
    fn honest_witness() -> (HashMap<String, Vec<BabyBear>>, usize) {
        let rows = 4;
        let mut w = HashMap::new();
        w.insert("old".into(), vec![BabyBear::new(10); rows]);
        w.insert("amt".into(), vec![BabyBear::new(5); rows]);
        w.insert("new".into(), vec![BabyBear::new(15); rows]);
        w.insert("dir".into(), vec![BabyBear::ZERO; rows]);
        (w, rows)
    }

    /// Build an effect-vm leg leaf that PUBLISHES `claim` at IR2 PI 46..49 (the deployed
    /// `customVmDescriptor2R24` slot semantics — four `PiBinding .first` pins) and re-exposes it
    /// for the fold. A minimal stand-in for the 789-wide deployed trace at the SAME surface.
    fn effectvm_leg_leaf(
        claim: [BabyBear; 4],
        config: &DreggRecursionConfig,
    ) -> RecursionOutput<DreggRecursionConfig> {
        let pi_count = 50; // slots 0..49 — 46..49 carry the claimed commitment.
        let constraints: Vec<VmConstraint2> = (0..4)
            .map(|k| {
                VmConstraint2::Base(VmConstraint::PiBinding {
                    row: VmRow::First,
                    col: k,
                    pi_index: CUSTOM_COMMIT_PI_LO + k,
                })
            })
            .collect();
        let desc = EffectVmDescriptor2 {
            name: "customVmDescriptor2R24-pi46-standin".to_string(),
            trace_width: 4,
            public_input_count: pi_count,
            tables: vec![],
            constraints,
            hash_sites: vec![],
            ranges: vec![],
        };
        let rows = 4;
        let trace: Vec<Vec<BabyBear>> = (0..rows)
            .map(|_| vec![claim[0], claim[1], claim[2], claim[3]])
            .collect();
        let mut pis = vec![BabyBear::ZERO; pi_count];
        for k in 0..4 {
            pis[CUSTOM_COMMIT_PI_LO + k] = claim[k];
        }
        let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
            &desc,
            &trace,
            &pis,
            &MemBoundaryWitness::default(),
            &[],
            &UMemBoundaryWitness::default(),
            config,
        )
        .expect("effect-vm leg stand-in proves (the claim is internally consistent)");
        prove_descriptor_leaf_with_pi_slice_expose(
            &desc,
            &inner,
            &pis,
            config,
            CUSTOM_COMMIT_PI_LO,
            CUSTOM_COMMIT_LEN,
        )
        .expect("effect-vm leg leaf re-exposes PI 46..49 as a 4-felt claim")
    }

    /// THE POSITIVE POLE: an HONEST custom turn — the effect-vm leg's claimed commitment EQUALS
    /// the genuine commitment the custom sub-proof exposes — binds in the fold, and the node
    /// re-exposes that bound commitment.
    #[test]
    fn honest_custom_turn_binds_in_the_fold() {
        let config = ir2_leaf_wrap_config();
        let program = demo_program();
        let (w, rows) = honest_witness();
        let pis: Vec<BabyBear> = vec![BabyBear::new(10), BabyBear::new(15)];
        let real = custom_proof_pi_commitment(&pis);

        let custom_leaf = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
            .expect("the custom sub-proof leaf proves");
        let ev_leaf = effectvm_leg_leaf(real, &config); // claims the REAL commitment

        let node = prove_custom_binding_node(&ev_leaf, &custom_leaf, &config)
            .expect("an honest custom turn binds in the fold");
        let exposed = read_exposed_pi_commitment(&node)
            .expect("the binding node re-exposes the bound commitment");
        assert_eq!(
            exposed, real,
            "the fold node's re-exposed commitment is the bound (== sub-proof) commitment"
        );
    }

    /// THE TOOTH (the repair BITES): a FORGED effect-vm leg — claiming a `custom_proof_commitment`
    /// no verifying sub-proof backs (it is internally consistent, so the leg leaf itself proves) —
    /// has NO satisfying partner in the fold: the per-lane `connect` to the custom sub-proof leaf's
    /// genuine commitment is a conflict, so the aggregate is UNSAT and no root exists. This is the
    /// deployed realization of the binding `StarkSoundCustom` falsely assumed.
    #[test]
    fn forged_custom_commitment_is_rejected_by_the_fold() {
        let config = ir2_leaf_wrap_config();
        let program = demo_program();
        let (w, rows) = honest_witness();
        let pis: Vec<BabyBear> = vec![BabyBear::new(10), BabyBear::new(15)];
        let real = custom_proof_pi_commitment(&pis);

        // A claim NO verifying sub-proof of these PIs backs (lane 0 perturbed by +1 mod p).
        let mut forged = real;
        forged[0] = BabyBear::new((real[0].0 + 1) % BABYBEAR_P);
        assert_ne!(forged, real);

        let custom_leaf = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
            .expect("the custom sub-proof leaf proves");
        let ev_leaf = effectvm_leg_leaf(forged, &config); // internally consistent, but FORGED claim

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_custom_binding_node(&ev_leaf, &custom_leaf, &config)
        }));
        match result {
            // The in-circuit `connect` conflict panicked the constraint/witness builder — rejected.
            Err(_) => {}
            // Or the aggregation returned an error — rejected.
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!(
                "a FORGED custom_proof_commitment minted a verifying fold node — the binding is OPEN"
            ),
        }
    }
}
