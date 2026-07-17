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
/// the PROOF-BIND FLAG-DAY ROTATION lays the eight `custom_proof_commitment` limbs at IR2 PI
/// 46..53 (limbs 0..4 from cols 72..75, limbs 4..8 from the commit-teeth columns), and the four
/// low `custom_program_vk_hash` limbs at 54..57).
pub const CUSTOM_COMMIT_PI_LO: usize = 46;
/// Width of the `custom_proof_commitment` claim — the FULL 8-felt `WideHash` class
/// (~124-bit birthday; flag-day rotation from the retired 4-felt / ~62-bit shape).
/// Old 4-felt custom artifacts are refused at the versioned admission boundary
/// (`dregg_circuit::effect_vm_descriptors::require_custom_commit_teeth_v2`).
pub const CUSTOM_COMMIT_LEN: usize = 8;

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
// THE CUSTOM-EFFECT FOLD-WIRE (DEPLOYED — wired into the chain prover). The binding the Lean
// `CustomBindingFromFold.custom_binding_from_fold` premise needs is now REAL for a pure light
// client: `prove_custom_binding_node_state_segmented` (below) is the DEPLOYED DEFAULT, minted by
// `crate::ivc_turn_chain::prove_chain_core_rotated`.
// ============================================================================
//
// A `Custom` effect's effect-vm leg publishes a CLAIMED `custom_proof_commitment` at IR2 PI
// slots 46..53 (`customVmDescriptor2R24` / Lean `customPiExposure`). On its own that is an
// UNBACKED claim: the in-AIR `proof_bind` op is a declaration, so a re-executing validator runs
// `CellProgram::verify_transition` OFF-AIR but a PURE LIGHT CLIENT (folding only the recursion
// tree) never witnesses the sub-proof. The fold-wire binds it IN the deployed tree.
//
// For a custom turn the deployed chain prover (`prove_chain_core_rotated`) aggregates TWO leaves:
//   * the effect-vm leg leaf as a DUAL-EXPOSE leaf
//     ([`crate::ivc_turn_chain::prove_descriptor_leaf_dual_expose`]) — ONE `expose_claim` carrying
//     the chain SEGMENT in lanes `[0 .. SEG_WIDTH)` AND the claimed 8-felt commitment (PI 46..53)
//     in lanes `[SEG_WIDTH ..)`; the inner PIs are otherwise consumed into the primitive `Public`
//     table and never reach a combine hook, so the re-expose is mandatory;
//   * the custom SUB-PROOF leaf, exposing its GENUINE in-circuit-computed PI-commitment AND its
//     declared `[old8 ‖ new8]` state prefix — the 24-lane
//     ([`crate::custom_leaf_adapter::prove_custom_leaf_with_state_commitment`]), RE-PROVEN from the
//     prover-side `CustomWitnessBundle` retained on the leg
//     ([`crate::joint_turn_aggregation::RotatedParticipantLeg::custom_witness`]).
// [`prove_custom_binding_node_state_segmented`] `connect`s the leg's claimed commitment lanes to
// the sub-proof's genuine commitment, `connect`s the sub-proof's declared roots to the leg's REAL
// rotated roots, AND re-exposes the SEGMENT, so the node folds into `aggregate_tree` like any
// segment leaf. TWO forgeries are therefore UNSAT: a turn whose effect-vm row claims a commitment
// NO verifying sub-proof backs (no custom leaf's exposed commitment equals the claimed slots), and
// a turn carrying a verifying, honestly-committed sub-proof about a DIFFERENT transition (its
// declared roots are not the leg's). Either way the aggregate does not prove (no root) and the
// light client never receives a verifying artifact. The deployed bite is exercised end-to-end by
// `circuit-prove/tests/custom_binding_deployed_tooth.rs` (honest-accept + forged-commitment-reject
// + forged-ROOT-reject through `prove_turn_chain_recursive` → `verify_turn_chain_recursive`).
//
// The commitment-only [`prove_custom_binding_node_segmented`] and the single-claim
// [`prove_custom_binding_node`] (a leg leaf re-exposing ONLY the commitment), with the in-lib
// `custom_fold_wire_tests` below, remain as the minimal MECHANISM teeth over a stand-in leg — and
// as the CANARY the state node is measured against (`custom_state_fold_wire_tests`: the same
// forged-root inputs the state node refuses, the commitment-only node accepts). They are NOT on
// the deployed path. Do not re-point the deployed arm at them: the commitment-only node's
// documented reach stops at "which PIs", and the dodge the state node closes is real.

/// Aggregate a custom turn's effect-vm leg leaf (which must RE-EXPOSE its claimed 4-felt
/// `custom_proof_commitment` at PI 46..53 via
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
                     (pi_lo=CUSTOM_COMMIT_PI_LO, len=CUSTOM_COMMIT_LEN=8)"
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

        // THE BINDING TOOTH, IN-CIRCUIT: the effect-vm leg's CLAIMED commitment (PI 46..53,
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

/// **THE SEGMENT-PRESERVING CUSTOM BINDING NODE (deployed custom-binding half #2).** Aggregate a
/// custom turn's DUAL-EXPOSE effect-vm leg leaf (minted by
/// [`crate::ivc_turn_chain::prove_descriptor_leaf_dual_expose`] — its single `expose_claim` carries
/// the chain SEGMENT in lanes `[0 .. SEG_WIDTH)` and the CLAIMED `custom_proof_commitment` in lanes
/// `[SEG_WIDTH .. SEG_WIDTH+CUSTOM_COMMIT_LEN)`) WITH the custom sub-proof leaf
/// ([`crate::custom_leaf_adapter::prove_custom_leaf_with_commitment`], whose `expose_claim` is the
/// genuine in-circuit commitment in lanes `[0 .. CUSTOM_COMMIT_LEN)`), and:
///
///   1. `connect`s the leg's claimed commitment lanes to the sub-proof's genuine commitment lanes
///      (the binding tooth — a forged claim no sub-proof backs is a conflict ⇒ UNSAT ⇒ no root), and
///   2. RE-EXPOSES the leg's SEGMENT lanes `[0 .. SEG_WIDTH)` as the parent claim.
///
/// The output therefore exposes an ordinary `SEG_WIDTH`-lane chain segment — byte-identical to what
/// a plain [`crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_segment`] leaf for the same
/// turn would expose — so it folds into [`crate::ivc_turn_chain::aggregate_tree`] like any other
/// per-turn segment leaf. This is what makes the custom binding REAL for a pure light client: the
/// commitment is bound IN the deployed recursion tree the light client folds, while the segment is
/// preserved so the chain `[genesis_root, final_root, num_turns, chain_digest]` still reaches the
/// root.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`]. The connecting node uses the
/// coeff-forced backend (the custom sub-proof child carries the `recompose/coeff` table).
pub fn prove_custom_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    custom_subproof_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    prove_claim_binding_node_segmented(
        dual_expose_leg_leaf,
        custom_subproof_leaf,
        config,
        CUSTOM_COMMIT_LEN,
    )
}

/// **THE IN-CIRCUIT STATE-BINDING FOLD** — as [`prove_custom_binding_node_segmented`], but it
/// ALSO `connect`s the custom sub-proof's CLAIMED `[old_commit8, new_commit8]` state prefix to
/// the leg's REAL descriptor-bound rotated roots, so a PURE LIGHT CLIENT witnesses that the
/// custom transition is about THIS cell's actual roots — not merely that some verifying
/// sub-proof backs the claimed commitment.
///
/// ## The gap this closes (the named remainder on `custom_state_binding`)
///
/// [`prove_custom_binding_node_segmented`] binds WHICH public inputs the sub-proof used (the
/// commitment is an opaque hash of them). It never bound what those inputs SAY. So a custom AIR
/// could prove a beautiful transition `R1 -> R2` while the turn commits `S1 -> S2`, and every
/// in-tree gate passed. The EXECUTOR refuses that off-AIR
/// (`TurnExecutor::enforce_custom_proof_state_binding`), but a light client folding only the
/// tree could not see it. That was tooth 2 of the two-teeth doc, explicitly "NOT landed".
///
/// ## The three connects
///
/// The dual-expose leg leaf already carries the REAL roots in its exposed segment — no leg-side
/// change was needed. The custom sub-proof leaf now re-exposes its bound PI prefix
/// ([`crate::custom_leaf_adapter::prove_custom_leaf_with_state_commitment`]). This node welds
/// them:
///
/// ```text
///   ev[SEG_WIDTH + k]        == cs[k]                        k in 0..8   the commitment (as before)
///   ev[SEG_FIRST_OLD + k]    == cs[CUSTOM_COMMIT_LEN + k]     k in 0..8   REAL old root == claimed old
///   ev[SEG_LAST_NEW  + k]    == cs[CUSTOM_COMMIT_LEN + 8 + k] k in 0..8   REAL new root == claimed new
/// ```
///
/// A sub-proof whose PIs declare roots the leg's transition did not produce is a per-lane
/// `connect` CONFLICT ⇒ the aggregation is UNSAT ⇒ no root exists ⇒ the light client never
/// receives a verifying artifact. Every lane of both roots is connected: a node binding only
/// some would accept a forgery in the rest.
///
/// ## Why this is a DEDICATED node, not a widened `prove_custom_binding_node_segmented`
///
/// The state connect requires the custom leaf to expose [`CUSTOM_STATE_CLAIM_LEN`] (24) lanes,
/// which in turn requires the sub-program to publish >= 16 PIs (the state-binding ABI). The
/// existing mechanism/demo carriers publish 2 PIs, and the DSL/Dfa carrier binds a 4-felt
/// claim — neither can serve the prefix. Making the connect CONDITIONAL on `cs.len() >= 24`
/// inside the shared node would be worse than useless: a forging prover would simply mint the
/// 8-lane leaf and the state connect would silently not fire — a dodgeable gate. So the state
/// binding is its OWN node that REQUIRES the 24-lane claim and always connects. Callers choose
/// the tooth they want; neither weakens the other.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_custom_binding_node_state_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    custom_subproof_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::custom_leaf_adapter::CUSTOM_STATE_CLAIM_LEN;
    use crate::ivc_turn_chain::{
        SEG_ANCHOR_WIDTH, SEG_FIRST_OLD, SEG_LAST_NEW, SEG_WIDTH, expose_claim_instance_index,
    };
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend_with_coeff_lookups;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let ev_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "dual-expose custom leg leaf carries no expose_claim table — it must be \
                     wrapped via prove_descriptor_leaf_dual_expose (segment ++ commitment)"
                .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&custom_subproof_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "custom sub-proof leaf carries no exposed claim (expose_claim) table — the \
                     state-binding fold requires a leaf minted via \
                     prove_custom_leaf_with_state_commitment (commitment ++ [old8 ‖ new8])"
                .to_string(),
        }
    })?;

    // FAIL-CLOSED on an 8-lane (commitment-only) custom leaf: without the exposed prefix there
    // is nothing to weld the roots to, and silently degrading to a commitment-only connect
    // would hand back a proof that LOOKS state-bound and is not.
    //
    // NB: read the table by op_type, NOT by `cs_idx` — `expose_claim_instance_index` returns an
    // index into the in-circuit `air_public_targets` (primitive tables FIRST, then
    // non-primitives), so it is offset by `NUM_PRIMITIVE_TABLES` and must not be used to index
    // `non_primitives` directly.
    let cs_lanes = custom_subproof_leaf
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .map(|e| e.public_values.len())
        .unwrap_or(0);
    if cs_lanes < CUSTOM_STATE_CLAIM_LEN {
        return Err(JointAggError::AggregationProofInvalid {
            reason: format!(
                "custom sub-proof leaf exposes {cs_lanes} claim lane(s) but the state-binding fold \
                 requires {CUSTOM_STATE_CLAIM_LEN} (commitment(8) ‖ old8 ‖ new8) — mint it with \
                 prove_custom_leaf_with_state_commitment. Refusing rather than degrading to a \
                 commitment-only connect."
            ),
        });
    }

    let left = dual_expose_leg_leaf.into_recursion_input::<BatchOnly>();
    let right = custom_subproof_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend_with_coeff_lookups();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let ev = left_apt
            .get(ev_idx)
            .expect("dual-expose leg's claim instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("custom sub-proof's exposed claim instance present");
        debug_assert!(
            ev.len() >= SEG_WIDTH + CUSTOM_COMMIT_LEN && cs.len() >= CUSTOM_STATE_CLAIM_LEN,
            "leg must carry segment ++ commitment; custom leaf must carry commitment ++ [old8 ‖ new8]"
        );

        // 1. THE COMMITMENT TOOTH (unchanged): the leg's CLAIMED commitment must equal the
        //    sub-proof's GENUINE in-circuit commitment.
        for k in 0..CUSTOM_COMMIT_LEN {
            cb.connect(ev[SEG_WIDTH + k], cs[k]);
        }
        // 2. THE STATE TOOTH (new): the sub-proof's CLAIMED pre/post roots must equal the leg's
        //    REAL descriptor-bound rotated roots. This is what makes the light client's fold say
        //    "the custom transition is about THIS cell's roots", not just "some sub-proof backs
        //    this hash".
        for k in 0..SEG_ANCHOR_WIDTH {
            cb.connect(ev[SEG_FIRST_OLD + k], cs[CUSTOM_COMMIT_LEN + k]);
            cb.connect(
                ev[SEG_LAST_NEW + k],
                cs[CUSTOM_COMMIT_LEN + SEG_ANCHOR_WIDTH + k],
            );
        }

        // RE-EXPOSE ONLY THE SEGMENT, so this node folds into `aggregate_tree` exactly like a
        // plain per-turn segment leaf (identical parent shape to the commitment-only node).
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
        reason: format!("state-binding custom fold aggregation node failed: {e:?}"),
    })
}

/// **THE IN-CIRCUIT APP-ROOT WELD FOLD (the keystone)** — as
/// [`prove_custom_binding_node_state_segmented`], but it ALSO `connect`s the custom sub-proof's
/// PUBLISHED application root `R` to the wide leg's EXPOSED committed value for the declared field
/// key `K`. So a PURE LIGHT CLIENT witnesses that the app's published root IS the value the cell
/// actually stores — not merely that the transition is about this cell's roots.
///
/// ## The gap this closes (the shared keystone four consumers named)
///
/// The state node ties `[old8 ‖ new8]` to the leg's real rotated roots, so the transition is about
/// THIS cell. But the sub-proof ALSO publishes an application root `R` (automatafl's
/// `board_new_root8`, tug's `winner`, the compose `outcome_commitment`) which `new8` covers only as
/// an opaque preimage — nothing forced `R` to EQUAL the field the cell stores. A prover picks BOTH
/// the field value it writes AND the `R` it publishes, so they trivially agree unless `R` is
/// FORCED to be the committed field, which the CellProgram vocabulary cannot express. This node is
/// that force, at the fold.
///
/// ## The four connects
///
/// The leg leaf carries `[segment(SEG_WIDTH) ‖ commitment(8) ‖ field_K(L)]` (minted via
/// [`crate::ivc_turn_chain::prove_descriptor_leaf_expose_segment_and_claims`] with claim slices
/// `[(CUSTOM_COMMIT_PI_LO, CUSTOM_COMMIT_LEN), (field_K_pi_lo, L)]`). The custom sub-proof leaf
/// carries `[commitment(8) ‖ old8 ‖ new8 ‖ R(L)]` (minted via
/// [`crate::custom_leaf_adapter::prove_custom_leaf_with_app_root_commitment`]). This node welds:
///
/// ```text
///   ev[SEG_WIDTH + k]        == cs[k]                  k in 0..8   the commitment (as before)
///   ev[SEG_FIRST_OLD + k]    == cs[8 + k]              k in 0..8   REAL old root == claimed old
///   ev[SEG_LAST_NEW  + k]    == cs[16 + k]             k in 0..8   REAL new root == claimed new
///   ev[SEG_WIDTH + 8 + k]    == cs[24 + k]             k in 0..L   REAL field[K] == published R  ← keystone
/// ```
///
/// Because `field_K` is FRI-bound to the same rotated pre-limbs the `new8` commitment absorbs (a
/// value carried faithfully in the wide block, e.g. a `fields[0..7]` octet), and `new8` is welded
/// to the leg's real root, the leg's exposed `field_K` IS the cell's committed value. So a sub-proof
/// whose published `R` is not the cell's real stored field is a per-lane `connect` CONFLICT ⇒ UNSAT
/// ⇒ no root ⇒ the light client never receives a verifying artifact. Every lane of `R` is connected.
///
/// ## Why a DEDICATED node, MANDATORY, not a conditional widening
///
/// The app-root connect requires the custom leaf to expose `24 + L` lanes and the leg to expose the
/// field slice. Making the connect CONDITIONAL on lane count inside a shared node would be the
/// forger's dodge: a forging prover would mint the narrow leaf and the connect would silently not
/// fire. So the app-root weld is its OWN node that REQUIRES the wide claim and ALWAYS connects
/// (fail-closed on a narrower leaf), exactly as the state node requires the 24-lane claim. `app_root_len`
/// is `L` (1 for a scalar register, 8 for an octet root).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_custom_binding_node_app_root_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    custom_subproof_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
    app_root_len: usize,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::custom_leaf_adapter::custom_app_root_claim_len;
    use crate::ivc_turn_chain::{
        SEG_ANCHOR_WIDTH, SEG_FIRST_OLD, SEG_LAST_NEW, SEG_WIDTH, expose_claim_instance_index,
    };
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend_with_coeff_lookups;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    if app_root_len == 0 {
        return Err(JointAggError::AggregationProofInvalid {
            reason:
                "app-root weld fold: app_root_len must be nonzero (a zero-width root cannot be \
                     welded)"
                    .to_string(),
        });
    }
    let cs_want = custom_app_root_claim_len(app_root_len); // 24 + L
    // The leg must carry: segment ++ commitment(8) ++ field_K(L).
    let ev_want = SEG_WIDTH + CUSTOM_COMMIT_LEN + app_root_len;

    let ev_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "app-root leg leaf carries no expose_claim table — it must be wrapped via \
                     prove_descriptor_leaf_expose_segment_and_claims (segment ++ commitment ++ \
                     field_K)"
                .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&custom_subproof_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "custom sub-proof leaf carries no exposed claim (expose_claim) table — the \
                     app-root weld requires a leaf minted via \
                     prove_custom_leaf_with_app_root_commitment (commitment ++ [old8 ‖ new8] ++ R)"
                .to_string(),
        }
    })?;

    // FAIL-CLOSED on a claim too narrow to carry the published root `R`: without the exposed `R`
    // lanes there is nothing to weld the field to, and silently degrading to a state-only connect
    // would hand back a proof that LOOKS app-root-bound and is not. (Read by op_type, not cs_idx —
    // see the note on `prove_custom_binding_node_state_segmented`.)
    let cs_lanes = custom_subproof_leaf
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .map(|e| e.public_values.len())
        .unwrap_or(0);
    if cs_lanes < cs_want {
        return Err(JointAggError::AggregationProofInvalid {
            reason: format!(
                "custom sub-proof leaf exposes {cs_lanes} claim lane(s) but the app-root weld fold \
                 requires {cs_want} (commitment(8) ‖ old8 ‖ new8 ‖ R({app_root_len})) — mint it \
                 with prove_custom_leaf_with_app_root_commitment. Refusing rather than degrading to \
                 a state-only connect."
            ),
        });
    }
    let ev_lanes = dual_expose_leg_leaf
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .map(|e| e.public_values.len())
        .unwrap_or(0);
    if ev_lanes < ev_want {
        return Err(JointAggError::AggregationProofInvalid {
            reason: format!(
                "app-root leg leaf exposes {ev_lanes} claim lane(s) but the app-root weld fold \
                 requires {ev_want} (segment({SEG_WIDTH}) ‖ commitment({CUSTOM_COMMIT_LEN}) ‖ \
                 field_K({app_root_len})) — mint it with \
                 prove_descriptor_leaf_expose_segment_and_claims([(commit_pi,8),(field_pi,{app_root_len})])."
            ),
        });
    }

    let left = dual_expose_leg_leaf.into_recursion_input::<BatchOnly>();
    let right = custom_subproof_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend_with_coeff_lookups();
    let params = ProveNextLayerParams::default();

    let l = app_root_len;
    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let ev = left_apt
            .get(ev_idx)
            .expect("app-root leg's claim instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("custom sub-proof's exposed claim instance present");
        debug_assert!(
            ev.len() >= SEG_WIDTH + CUSTOM_COMMIT_LEN + l && cs.len() >= cs_want,
            "leg must carry segment ++ commitment ++ field_K; custom leaf must carry commitment ++ \
             [old8 ‖ new8] ++ R"
        );

        // 1. THE COMMITMENT TOOTH.
        for k in 0..CUSTOM_COMMIT_LEN {
            cb.connect(ev[SEG_WIDTH + k], cs[k]);
        }
        // 2. THE STATE TOOTH: the sub-proof's declared pre/post roots == the leg's real roots.
        for k in 0..SEG_ANCHOR_WIDTH {
            cb.connect(ev[SEG_FIRST_OLD + k], cs[CUSTOM_COMMIT_LEN + k]);
            cb.connect(
                ev[SEG_LAST_NEW + k],
                cs[CUSTOM_COMMIT_LEN + SEG_ANCHOR_WIDTH + k],
            );
        }
        // 3. THE APP-ROOT TOOTH (the keystone): the sub-proof's PUBLISHED root R == the leg's
        //    EXPOSED committed field value for the declared key K. R is at custom-claim lanes
        //    [24 .. 24+L); the leg's field_K is at leg-claim lanes [SEG_WIDTH+8 .. SEG_WIDTH+8+L).
        for k in 0..l {
            cb.connect(
                ev[SEG_WIDTH + CUSTOM_COMMIT_LEN + k],
                cs[custom_app_root_claim_len(0) + k],
            );
        }

        // RE-EXPOSE ONLY THE SEGMENT, so this node folds into `aggregate_tree` exactly like a
        // plain per-turn segment leaf (identical parent shape to the state node).
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
        reason: format!("app-root weld custom fold aggregation node failed: {e:?}"),
    })
}

/// **THE CLAIM-LEN-PARAMETRIC SEGMENT-PRESERVING BINDING NODE** —
/// [`prove_custom_binding_node_segmented`] with the connected claim width made explicit.
/// The CUSTOM carrier binds the full 8-felt rotated `custom_proof_commitment`
/// (`claim_len = CUSTOM_COMMIT_LEN = 8`); the DSL/Dfa carrier binds the deployed 4-felt
/// `dfa_rc` route-commitment lanes (`claim_len = DFA_RC_LEN = 4` — the rc carrier is its own
/// deployed surface, NOT rotated by the proof-bind flag day; its lanes equal the FIRST squeeze
/// block, i.e. lanes `[0..4)` of the sub-proof leaf's 8-felt exposed commitment, so connecting
/// the first `claim_len` sub-proof lanes is exactly the host byte-identity).
pub fn prove_claim_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    custom_subproof_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
    claim_len: usize,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::{SEG_WIDTH, expose_claim_instance_index};
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend_with_coeff_lookups;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let ev_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "dual-expose custom leg leaf carries no expose_claim table — it must be \
                     wrapped via prove_descriptor_leaf_dual_expose (segment ++ commitment)"
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

    let left = dual_expose_leg_leaf.into_recursion_input::<BatchOnly>();
    let right = custom_subproof_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend_with_coeff_lookups();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let ev = left_apt
            .get(ev_idx)
            .expect("dual-expose leg's claim instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("custom sub-proof's exposed commitment instance present");
        debug_assert!(
            ev.len() >= SEG_WIDTH + claim_len && cs.len() >= claim_len,
            "dual-expose claim must carry segment ++ commitment; custom leaf carries commitment"
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED commitment (dual-expose lanes
        // [SEG_WIDTH .. SEG_WIDTH+claim_len)) must equal the sub-proof's GENUINE in-circuit
        // commitment, lane by lane. A forged claim with no backing sub-proof is a conflict
        // here ⇒ UNSAT ⇒ no root.
        for k in 0..claim_len {
            cb.connect(ev[SEG_WIDTH + k], cs[k]);
        }
        // RE-EXPOSE ONLY THE SEGMENT (lanes [0 .. SEG_WIDTH)) as the parent claim, so this node
        // folds into `aggregate_tree` exactly like a plain per-turn segment leaf.
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
        reason: format!("segmented custom-binding aggregation node failed: {e:?}"),
    })
}

// ============================================================================
// THE BRIDGE-ACTION FOLD-WIRE (mechanism + caller READY; the deployed-leg tuple emit is the named
// big-bang piece). The bridge analog of the custom fold-wire above: bind the bridge-mint leg's
// CLAIMED 26-slot full-fidelity tuple `(nullifier, recipient, dest_federation, amount)` to the
// RE-PROVEN bridge-action sub-proof's GENUINE in-circuit tuple, INSIDE the recursion tree a pure
// light client folds — so a re-executing validator's off-AIR `verify_bridge_action` is no longer
// the ONLY enforcer.
// ============================================================================
//
// The bridge-action binding is today verified OFF-AIR by `turn::executor::apply::apply_bridge_mint`
// (`verify_bridge_action` over the typed limbs). A PURE LIGHT CLIENT folding only the recursion tree
// never witnesses it. This fold-wire binds it IN the tree, EXACTLY mirroring the custom wire:
//   * the bridge-mint leg leaf RE-EXPOSES its CLAIMED tuple (segment ++ the 26 limbs) —
//     [`prove_bridge_binding_node_segmented`] consumes a DUAL-EXPOSE leg leaf whose `expose_claim`
//     carries the chain SEGMENT in lanes `[0 .. SEG_WIDTH)` AND the claimed tuple in lanes
//     `[SEG_WIDTH .. SEG_WIDTH+BRIDGE_TUPLE_LEN)`;
//   * the bridge SUB-PROOF leaf exposes its GENUINE in-circuit tuple
//     ([`crate::bridge_leaf_adapter::prove_bridge_leaf_tuple_claim`], lanes `[0 .. BRIDGE_TUPLE_LEN)`).
// The node `connect`s the 26 lanes (a forged claim no sub-proof backs is UNSAT ⇒ no root) and
// re-exposes the segment, folding into `aggregate_tree` like any per-turn segment leaf.
//
// ⚑ THE NAMED BIG-BANG PIECE (descriptor-emit, owned by another agent): the DEPLOYED bridge-mint
// wide leg today binds only a compressed `mint_hash` digest (the substrate `BridgeMint` row's
// `value_lo`), NOT the 26 full-fidelity limbs as descriptor PIs. So the DUAL-EXPOSE leg side
// (segment ++ the 26-limb tuple at known PI slots, the bridge twin of
// `prove_descriptor_leaf_dual_expose`) cannot be minted until the bridge-mint descriptor EMITS the
// tuple at fixed PI slots (`BRIDGE_TUPLE_PI_LO..`). That descriptor-emit rides the big-bang VK regen.
// The FOLD MECHANISM (`prove_bridge_binding_node` / `_segmented`) + the sub-proof leaf
// (`prove_bridge_leaf_tuple_claim`) + this caller are READY, and the witness SOCKET now exists
// (`CarrierWitness::Bridge` on `RotatedParticipantLeg::carrier_witness`, its fold arm explicitly
// FAIL-CLOSED in `prove_chain_core_rotated`): once the leg publishes the tuple, the production
// bridge-mint minter attaches the bridge witness and the bridge wave fills its arm — zero new
// mechanism.

/// Width of the bridge-action full-fidelity tuple claim (26 felts:
/// 8 nullifier ++ 8 recipient ++ 8 dest_federation ++ 2 amount).
pub const BRIDGE_TUPLE_LEN: usize = 26;

/// **THE BRIDGE-BINDING MECHANISM NODE (the minimal fold tooth — no segment).** Aggregate a bridge
/// turn's leg leaf (which must RE-EXPOSE its CLAIMED 26-slot tuple as an `expose_claim`, via
/// [`crate::ivc_turn_chain::prove_descriptor_leaf_with_pi_slice_expose`]) WITH the bridge sub-proof
/// leaf ([`crate::bridge_leaf_adapter::prove_bridge_leaf_tuple_claim`]), CONNECTING the two 26-felt
/// tuples in-circuit and re-exposing the now-bound tuple as the parent claim.
///
/// THE TOOTH: if the leg claims a tuple the bridge sub-proof does not back, the per-lane `connect` is
/// a conflict and the aggregation is UNSAT — no root. There is no separate, swappable backing: the
/// sub-proof's tuple is bound in-circuit to its REAL `PiBinding{First}` PIs, so a forged claim has no
/// satisfying partner. This is the term-for-term bridge twin of [`prove_custom_binding_node`].
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_bridge_binding_node(
    leg_tuple_leaf: &RecursionOutput<DreggRecursionConfig>,
    bridge_subproof_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::expose_claim_instance_index;
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let leg_idx = expose_claim_instance_index(&leg_tuple_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "bridge leg leaf carries no re-exposed tuple (expose_claim) table — it must be \
                     wrapped via prove_descriptor_leaf_with_pi_slice_expose (the 26-slot tuple)"
                    .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&bridge_subproof_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "bridge sub-proof leaf carries no exposed tuple (expose_claim) table — it must \
                     be minted via prove_bridge_leaf_tuple_claim"
                    .to_string(),
        }
    })?;

    let left = leg_tuple_leaf.into_recursion_input::<BatchOnly>();
    let right = bridge_subproof_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("bridge leg's re-exposed tuple instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("bridge sub-proof's exposed tuple instance present");
        debug_assert!(lg.len() >= BRIDGE_TUPLE_LEN && cs.len() >= BRIDGE_TUPLE_LEN);
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED tuple must equal the bridge sub-proof's
        // GENUINE in-circuit tuple, lane by lane. A forged claim with no backing sub-proof is a
        // conflict here ⇒ UNSAT ⇒ no root.
        for k in 0..BRIDGE_TUPLE_LEN {
            cb.connect(lg[k], cs[k]);
        }
        let bound: Vec<Target> = (0..BRIDGE_TUPLE_LEN).map(|k| lg[k]).collect();
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
        reason: format!("bridge-binding aggregation node failed: {e:?}"),
    })
}

/// **THE SEGMENT-PRESERVING BRIDGE BINDING NODE (deployed bridge-binding, caller-ready).** The
/// bridge twin of [`prove_custom_binding_node_segmented`]: aggregate a bridge turn's DUAL-EXPOSE leg
/// leaf (whose single `expose_claim` carries the chain SEGMENT in lanes `[0 .. SEG_WIDTH)` and the
/// CLAIMED 26-slot tuple in lanes `[SEG_WIDTH .. SEG_WIDTH+BRIDGE_TUPLE_LEN)`) WITH the bridge
/// sub-proof leaf ([`crate::bridge_leaf_adapter::prove_bridge_leaf_tuple_claim`], whose
/// `expose_claim` is the genuine tuple in lanes `[0 .. BRIDGE_TUPLE_LEN)`), and:
///
///   1. `connect`s the leg's claimed tuple lanes to the sub-proof's genuine tuple lanes (the binding
///      tooth — a forged claim no sub-proof backs is a conflict ⇒ UNSAT ⇒ no root), and
///   2. RE-EXPOSES the leg's SEGMENT lanes `[0 .. SEG_WIDTH)` as the parent claim.
///
/// The output exposes an ordinary `SEG_WIDTH`-lane chain segment, so it folds into
/// [`crate::ivc_turn_chain::aggregate_tree`] like any other per-turn segment leaf — making the bridge
/// full-fidelity binding REAL for a pure light client while preserving the chain endpoints/digest.
///
/// ⚑ The DUAL-EXPOSE leg leaf this consumes requires the deployed bridge-mint wide leg to PUBLISH the
/// 26-limb tuple at fixed PI slots (`BRIDGE_TUPLE_PI_LO..`); that descriptor-emit is the named
/// big-bang piece (see the module-level wire comment). This node + its mechanism are ready for it.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_bridge_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    bridge_subproof_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::{SEG_WIDTH, expose_claim_instance_index};
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let leg_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "dual-expose bridge leg leaf carries no expose_claim table — it must be wrapped \
                     to re-expose (segment ++ the 26-slot tuple)"
                    .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&bridge_subproof_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "bridge sub-proof leaf carries no exposed tuple (expose_claim) table — it must \
                     be minted via prove_bridge_leaf_tuple_claim"
                    .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input::<BatchOnly>();
    let right = bridge_subproof_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("dual-expose bridge leg's claim instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("bridge sub-proof's exposed tuple instance present");
        debug_assert!(
            lg.len() >= SEG_WIDTH + BRIDGE_TUPLE_LEN && cs.len() >= BRIDGE_TUPLE_LEN,
            "dual-expose claim must carry segment ++ tuple; bridge leaf carries the tuple"
        );
        for k in 0..BRIDGE_TUPLE_LEN {
            cb.connect(lg[SEG_WIDTH + k], cs[k]);
        }
        let seg: Vec<Target> = (0..SEG_WIDTH).map(|k| lg[k]).collect();
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
        reason: format!("segmented bridge-binding aggregation node failed: {e:?}"),
    })
}

/// **THE SEGMENT-PRESERVING SOVEREIGN BINDING NODE (the sovereign analog of
/// [`prove_custom_binding_node_segmented`]).** Aggregate a sovereign turn's DUAL-EXPOSE effect-vm leg
/// leaf (whose single `expose_claim` carries the chain SEGMENT in lanes `[0 .. SEG_WIDTH)` and the
/// CLAIMED `SOVEREIGN_WITNESS_KEY_COMMIT` teeth in lanes `[SEG_WIDTH .. SEG_WIDTH+KEY_CLAIM_LEN)`)
/// WITH the re-proved sovereign-authority leaf
/// ([`crate::sovereign_leaf_adapter::prove_sovereign_leaf_with_key_claim`], whose `expose_claim` is
/// the in-circuit-bound `key_commit` in lanes `[0 .. KEY_CLAIM_LEN)`), and:
///
///   1. `connect`s the leg's claimed `key_commit` lanes to the authority leaf's bound `key_commit`
///      (the binding tooth — a forged sovereign turn whose teeth name a `key_commit` no authority
///      leaf binds is a conflict ⇒ UNSAT ⇒ no root), and
///   2. RE-EXPOSES the leg's SEGMENT lanes `[0 .. SEG_WIDTH)` as the parent claim.
///
/// The output exposes an ordinary `SEG_WIDTH`-lane chain segment, so it folds into
/// [`crate::ivc_turn_chain::aggregate_tree`] like any other per-turn segment leaf. This is what makes
/// the sovereign authority REAL for a pure light client: the owner-key digest the deployed leg claims
/// is bound IN the deployed recursion tree the light client folds, to the authority tuple the
/// sovereign leaf proves, while the chain `[genesis_root, final_root, num_turns, chain_digest]` still
/// reaches the root.
///
/// THE NAMED SEAMS (honest):
///   * The deployed sovereign leg must DUAL-EXPOSE its `SOVEREIGN_WITNESS_KEY_COMMIT` teeth (lanes
///     `[SEG_WIDTH ..)`). Today the teeth are dead-zero (`EffectVmContext::default`); the teeth-fill
///     on the rotated producer + the leg's dual-expose of them is the BIG-BANG DESCRIPTOR PIECE (a
///     PI-exposure change, owned by the descriptor lane). This node is its consumer.
///   * The node binds `key_commit` (the owner digest, leg (b)). Connecting the anchor (leg (a)) +
///     sequence (leg (c)) teeth needs the leg to expose those slots too — the same big-bang piece,
///     widened. The authority leaf already binds all four in-circuit (anchor/sequence/new are pinned
///     PIs), so widening the connect is a lane-count change, not new soundness machinery.
///   * Ed25519 verification (the owner key actually signed the tuple) stays OFF-AIR — the
///     digest-of-attestation boundary (see `sovereign_leaf_adapter` module docs).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`]. Both children re-expose FRI-bound
/// PI lanes directly (no `recompose/coeff` table), so the plain backend suffices.
pub fn prove_sovereign_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    sovereign_authority_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::{SEG_WIDTH, expose_claim_instance_index};
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use crate::sovereign_leaf_adapter::SOVEREIGN_KEY_CLAIM_LEN;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let ev_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "dual-expose sovereign leg leaf carries no expose_claim table — it must be \
                     wrapped to expose segment ++ key_commit (the SOVEREIGN_WITNESS_KEY_COMMIT teeth)"
                .to_string(),
        }
    })?;
    let sa_idx = expose_claim_instance_index(&sovereign_authority_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "sovereign-authority leaf carries no exposed key_commit (expose_claim) table — \
                     it must be minted via prove_sovereign_leaf_with_key_claim"
                    .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input::<BatchOnly>();
    let right = sovereign_authority_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let ev = left_apt
            .get(ev_idx)
            .expect("dual-expose sovereign leg's claim instance present");
        let sa = right_apt
            .get(sa_idx)
            .expect("sovereign-authority leaf's exposed key_commit instance present");
        debug_assert!(
            ev.len() >= SEG_WIDTH + SOVEREIGN_KEY_CLAIM_LEN && sa.len() >= SOVEREIGN_KEY_CLAIM_LEN,
            "dual-expose claim must carry segment ++ key_commit; authority leaf carries key_commit"
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED key_commit (lanes
        // [SEG_WIDTH .. SEG_WIDTH+KEY_CLAIM_LEN)) must equal the authority leaf's BOUND key_commit,
        // lane by lane. A sovereign turn whose teeth name an owner digest no authority leaf binds is a
        // conflict here ⇒ UNSAT ⇒ no root.
        for k in 0..SOVEREIGN_KEY_CLAIM_LEN {
            cb.connect(ev[SEG_WIDTH + k], sa[k]);
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
        reason: format!("segmented sovereign-binding aggregation node failed: {e:?}"),
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
// These exercise the binding MECHANISM directly: the REAL custom sub-proof leaf
// (`prove_custom_leaf_with_commitment`, the custom-leaf adapter) folded against an
// effect-vm leg leaf that PUBLISHES a claimed 8-felt `custom_proof_commitment` at IR2 PI 46..53 —
// the exact slot semantics the deployed `customVmDescriptor2R24` `customPiExposure` uses (eight
// commit `PiBinding .first` pins; the proof-bind flag-day rotation). The leg leaf here is a minimal PiBinding-only IR2 descriptor STANDING
// IN for the 789-wide deployed trace at the SAME exposure surface. This proves the fold-wire + the
// tooth bite over the deployed slot + the real custom leaf via the single-claim
// `prove_custom_binding_node`. The DEPLOYED path (the 789-wide leg + the retained custom witness +
// the dual-claim leaf + `prove_custom_binding_node_segmented`, wired in `prove_chain_core_rotated`)
// is exercised end-to-end by `circuit-prove/tests/custom_binding_deployed_tooth.rs`; these in-lib
// teeth remain the minimal MECHANISM check.
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
    use dregg_circuit::refusal::must_refuse;
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

    /// Build an effect-vm leg leaf that PUBLISHES the 8-felt `claim` at IR2 PI 46..53 (the
    /// deployed `customVmDescriptor2R24` slot semantics after the proof-bind flag-day rotation —
    /// eight `PiBinding .first` commit pins) and re-exposes it for the fold. A minimal stand-in
    /// for the wide deployed trace at the SAME exposure surface.
    fn effectvm_leg_leaf(
        claim: crate::custom_proof_bind::ProofBindCommitment,
        config: &DreggRecursionConfig,
    ) -> RecursionOutput<DreggRecursionConfig> {
        let pi_count = CUSTOM_COMMIT_PI_LO + CUSTOM_COMMIT_LEN; // 54: slots 46..53 carry the claim.
        let constraints: Vec<VmConstraint2> = (0..CUSTOM_COMMIT_LEN)
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
            trace_width: CUSTOM_COMMIT_LEN,
            public_input_count: pi_count,
            tables: vec![],
            constraints,
            hash_sites: vec![],
            ranges: vec![],
        };
        let rows = 4;
        let trace: Vec<Vec<BabyBear>> = (0..rows).map(|_| claim.to_vec()).collect();
        let mut pis = vec![BabyBear::ZERO; pi_count];
        for k in 0..CUSTOM_COMMIT_LEN {
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
        .expect("effect-vm leg leaf re-exposes PI 46..53 as the 8-felt claim")
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
        // FLAG-DAY COMPLETE (8-felt commit): the leg claims the FULL 8-felt commitment at
        // PI 46..53 — both squeeze blocks, all eight lanes bound by the node's `connect`.
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
    /// genuine commitment is a conflict, so the aggregate is UNSAT and no root exists. This proves
    /// the binding MECHANISM bites over the single-claim node. The DEPLOYED bite (the segment-
    /// preserving `prove_custom_binding_node_segmented` wired into `prove_chain_core_rotated`) is
    /// pinned end-to-end by `circuit-prove/tests/custom_binding_deployed_tooth.rs`.
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
        assert_ne!(forged[0], real[0]);

        let custom_leaf = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
            .expect("the custom sub-proof leaf proves");
        let ev_leaf = effectvm_leg_leaf(forged, &config); // internally consistent, but FORGED claim

        must_refuse(
            "a FORGED custom_proof_commitment minted a verifying fold node",
            || prove_custom_binding_node(&ev_leaf, &custom_leaf, &config),
        );
    }

    /// THE PER-LANE TOOTH (flag-day spec: mutations targeted at EACH of the eight lanes make
    /// the custom binding node unsatisfiable). For every lane k ∈ 0..8 — the four FIRST-squeeze
    /// lanes AND the four SECOND-squeeze lanes the rotation added — a leg claiming the real
    /// commitment with ONLY lane k perturbed has no satisfying fold partner: the per-lane
    /// `connect` to the sub-proof's genuine in-circuit commitment is a conflict ⇒ UNSAT ⇒ no
    /// root. This is what makes the second squeeze block LOAD-BEARING (a node that bound only
    /// the first four lanes would accept the k ∈ 4..8 forgeries).
    #[test]
    fn every_forged_commitment_lane_is_rejected_by_the_fold() {
        let config = ir2_leaf_wrap_config();
        let program = demo_program();
        let (w, rows) = honest_witness();
        let pis: Vec<BabyBear> = vec![BabyBear::new(10), BabyBear::new(15)];
        let real = custom_proof_pi_commitment(&pis);

        // ONE genuine sub-proof leaf, reused against every forged leg.
        let custom_leaf = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
            .expect("the custom sub-proof leaf proves");

        for k in 0..CUSTOM_COMMIT_LEN {
            let mut forged = real;
            forged[k] = BabyBear::new((real[k].0 + 1) % BABYBEAR_P);
            assert_ne!(forged[k], real[k]);
            let ev_leaf = effectvm_leg_leaf(forged, &config);
            must_refuse(
                "a commitment forged ONLY in lane {k} minted a verifying fold node —  that lane is NOT bound",
                || prove_custom_binding_node(&ev_leaf, &custom_leaf, &config),
            );
        }
    }
}

// ============================================================================
// THE IN-CIRCUIT STATE-BINDING FOLD TEETH (in-lib — no rotated mint needed).
//
// These exercise the leg the `custom_state_binding` doc named as NOT LANDED: making a
// PURE LIGHT CLIENT (folding only the recursion tree) witness that a custom sub-proof's
// declared `[old8, new8]` prefix IS the leg's REAL descriptor-bound roots — not merely
// that some verifying sub-proof backs the claimed commitment.
//
// The leg leaf here is a minimal stand-in for the 789-wide deployed `customVmDescriptor2R24`
// at the SAME two exposure surfaces the real member has: the 8-felt commitment claim at IR2
// PI [46..54) and the 16 wide anchors in the LAST 16 PIs (the deployed custom member ships at
// 78 PIs = 62 base + 16 wide, so the claim and the anchors do not overlap — mirrored here).
// ============================================================================
#[cfg(test)]
// The `canary__*` name uses a double underscore to set the CANARY label off from the
// property it measures — clearer in `cargo test` output than one long snake run.
#[allow(non_snake_case)]
mod custom_state_fold_wire_tests {
    use super::*;
    use crate::custom_leaf_adapter::{
        prove_custom_leaf_with_state_commitment, read_exposed_pi_commitment,
        read_exposed_state_prefix,
    };
    use crate::custom_proof_bind::custom_proof_pi_commitment;
    use crate::ivc_turn_chain::{
        SEG_ANCHOR_WIDTH, ir2_leaf_wrap_config, prove_descriptor_leaf_dual_expose,
    };
    use dregg_circuit::descriptor_ir2::{
        EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, VmConstraint2,
        prove_vm_descriptor2_for_config,
    };
    use dregg_circuit::dsl::circuit::{
        CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
    };
    use dregg_circuit::effect_vm::custom_state_binding::{
        CUSTOM_PI_STATE_PREFIX_LEN, custom_pi_state_prefix,
    };
    use dregg_circuit::field::BABYBEAR_P;
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
    use dregg_circuit::refusal::must_refuse;
    use std::collections::HashMap;

    /// PI count of the stand-in leg — the deployed custom wide member's shape (62 base + 16
    /// wide anchors). Keeps the claim slice [46..54) and the anchors [62..78) disjoint, and is
    /// >= `WIDE_PI_COUNT` (66) so `prove_descriptor_leaf_dual_expose` takes the WIDE anchor
    /// branch (sourcing the genuine 8-felt roots rather than broadcasting a single felt).
    const STANDIN_LEG_PI_COUNT: usize = 78;

    /// A STATE-BINDING custom program: the same minimal-but-REAL conservation shape as the
    /// demo, but publishing the `custom_state_binding` ABI's public inputs —
    /// `[old_commit8 ‖ new_commit8 ‖ old_bal, new_bal]` (18 PIs). The 2-PI demo program is NOT
    /// a state-binding program and cannot serve this fold (it cannot express the prefix).
    fn state_binding_program() -> CellProgram {
        let p_minus_1 = BabyBear::new(BABYBEAR_P - 1);
        let descriptor = CircuitDescriptor {
            name: "dregg-custom-state-binding-demo-v1".to_string(),
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
            // [old8 ‖ new8] ‖ two app PIs — the ABI shape (16 + 2).
            public_input_count: CUSTOM_PI_STATE_PREFIX_LEN + 2,
            lookup_tables: vec![],
        };
        CellProgram::new(descriptor, 1)
    }

    fn honest_witness() -> (HashMap<String, Vec<BabyBear>>, usize) {
        let rows = 4;
        let mut w = HashMap::new();
        w.insert("old".into(), vec![BabyBear::new(10); rows]);
        w.insert("amt".into(), vec![BabyBear::new(5); rows]);
        w.insert("new".into(), vec![BabyBear::new(15); rows]);
        w.insert("dir".into(), vec![BabyBear::ZERO; rows]);
        (w, rows)
    }

    /// A distinct 8-felt root fixture.
    fn root8(base: u32) -> [BabyBear; 8] {
        core::array::from_fn(|k| BabyBear::new(base + k as u32))
    }

    /// The state-binding sub-proof's public inputs: `[old8 ‖ new8 ‖ 10, 15]`.
    fn state_pis(old8: &[BabyBear; 8], new8: &[BabyBear; 8]) -> Vec<BabyBear> {
        let mut pis = custom_pi_state_prefix(old8, new8).to_vec();
        pis.push(BabyBear::new(10));
        pis.push(BabyBear::new(15));
        pis
    }

    /// A DUAL-EXPOSE stand-in leg leaf carrying BOTH surfaces the deployed custom member has:
    /// the claimed 8-felt commitment at IR2 PI [46..54), and the REAL 8-felt rotated roots in
    /// the last 16 PIs. Every published lane is pinned to a trace column by a `PiBinding`, so
    /// the exposed values are FRI-bound, not free scalars.
    fn dual_expose_leg_leaf(
        claim: crate::custom_proof_bind::ProofBindCommitment,
        real_old8: &[BabyBear; 8],
        real_new8: &[BabyBear; 8],
        config: &DreggRecursionConfig,
    ) -> RecursionOutput<DreggRecursionConfig> {
        let n = STANDIN_LEG_PI_COUNT;
        let old_first = n - 2 * SEG_ANCHOR_WIDTH; // 62
        let new_first = n - SEG_ANCHOR_WIDTH; // 70

        // cols 0..8 = the claim; 8..16 = old8; 16..24 = new8.
        let mut constraints: Vec<VmConstraint2> = (0..CUSTOM_COMMIT_LEN)
            .map(|k| {
                VmConstraint2::Base(VmConstraint::PiBinding {
                    row: VmRow::First,
                    col: k,
                    pi_index: CUSTOM_COMMIT_PI_LO + k,
                })
            })
            .collect();
        for k in 0..SEG_ANCHOR_WIDTH {
            constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: CUSTOM_COMMIT_LEN + k,
                pi_index: old_first + k,
            }));
            constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: CUSTOM_COMMIT_LEN + SEG_ANCHOR_WIDTH + k,
                pi_index: new_first + k,
            }));
        }

        let trace_width = CUSTOM_COMMIT_LEN + 2 * SEG_ANCHOR_WIDTH; // 24
        let desc = EffectVmDescriptor2 {
            name: "customVmDescriptor2R24-dual-expose-standin".to_string(),
            trace_width,
            public_input_count: n,
            tables: vec![],
            constraints,
            hash_sites: vec![],
            ranges: vec![],
        };

        let mut row: Vec<BabyBear> = Vec::with_capacity(trace_width);
        row.extend_from_slice(&claim);
        row.extend_from_slice(real_old8);
        row.extend_from_slice(real_new8);
        let trace: Vec<Vec<BabyBear>> = (0..4).map(|_| row.clone()).collect();

        let mut pis = vec![BabyBear::ZERO; n];
        for k in 0..CUSTOM_COMMIT_LEN {
            pis[CUSTOM_COMMIT_PI_LO + k] = claim[k];
        }
        for k in 0..SEG_ANCHOR_WIDTH {
            pis[old_first + k] = real_old8[k];
            pis[new_first + k] = real_new8[k];
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
        .expect("dual-expose leg stand-in proves (its published lanes are internally consistent)");

        prove_descriptor_leaf_dual_expose(&desc, &inner, &pis, config)
            .expect("dual-expose leg leaf exposes segment ++ the claimed commitment")
    }

    /// The custom leaf's exposed claim IS `[commitment(8) ‖ old8 ‖ new8]`, and the prefix lanes
    /// are the leaf's REAL bound PIs — so exposure and execution are welded. (The cheap
    /// structural pole, before the folds.)
    #[test]
    #[ignore = "mints a STARK + leaf-wrap (minutes); run with --ignored on the build box"]
    fn state_leaf_exposes_the_commitment_and_the_bound_state_prefix() {
        let config = ir2_leaf_wrap_config();
        let program = state_binding_program();
        let (w, rows) = honest_witness();
        let (old8, new8) = (root8(100), root8(200));
        let pis = state_pis(&old8, &new8);

        let leaf = prove_custom_leaf_with_state_commitment(&program, &w, rows, &pis, &config)
            .expect("the state-binding custom leaf proves");

        assert_eq!(
            read_exposed_pi_commitment(&leaf).expect("commitment lanes present"),
            custom_proof_pi_commitment(&pis),
            "lanes [0..8) must be the host-identical PI commitment"
        );
        assert_eq!(
            read_exposed_state_prefix(&leaf).expect("state prefix lanes present"),
            (old8, new8),
            "lanes [8..24) must re-expose the sub-proof's OWN bound [old8, new8] prefix"
        );
    }

    /// A sub-program that cannot express the binding (fewer than 16 PIs) is REFUSED — never
    /// zero-padded into a false prefix. The in-circuit mirror of `extract_custom_pi_state_roots`
    /// returning `None`.
    #[test]
    fn a_program_too_narrow_for_the_state_prefix_is_refused() {
        let config = ir2_leaf_wrap_config();
        // The 2-PI demo shape — a real program, but not a state-binding one.
        let mut program = state_binding_program();
        program.descriptor.public_input_count = 2;
        let (w, rows) = honest_witness();
        let pis = vec![BabyBear::new(10), BabyBear::new(15)];

        must_refuse(
            "a sub-program with 2 PIs minted a state-binding leaf",
            || prove_custom_leaf_with_state_commitment(&program, &w, rows, &pis, &config),
        );
    }

    /// **THE POSITIVE POLE.** An HONEST custom turn — the sub-proof's declared `[old8, new8]`
    /// prefix IS the leg's real descriptor-bound roots, and the leg's claimed commitment is the
    /// genuine one — binds in the state fold.
    #[test]
    #[ignore = "folds two leaves through an aggregation layer (minutes); run with --ignored"]
    fn honest_state_bound_custom_turn_binds_in_the_fold() {
        let config = ir2_leaf_wrap_config();
        let program = state_binding_program();
        let (w, rows) = honest_witness();
        let (old8, new8) = (root8(100), root8(200));
        let pis = state_pis(&old8, &new8);
        let real = custom_proof_pi_commitment(&pis);

        let custom_leaf =
            prove_custom_leaf_with_state_commitment(&program, &w, rows, &pis, &config)
                .expect("the state-binding custom sub-proof leaf proves");
        // The leg publishes the SAME roots the sub-proof declares.
        let leg = dual_expose_leg_leaf(real, &old8, &new8, &config);

        prove_custom_binding_node_state_segmented(&leg, &custom_leaf, &config)
            .expect("an honest state-bound custom turn must bind in the fold");
    }

    /// **THE TOOTH.** A custom sub-proof about a DIFFERENT transition — it VERIFIES, and the
    /// leg honestly claims ITS commitment (so the commitment connect PASSES) — has no
    /// satisfying partner: its declared roots are not the leg's real roots, so the state
    /// `connect` is a conflict ⇒ UNSAT ⇒ no root ⇒ the light client never receives a verifying
    /// artifact.
    ///
    /// This is the exact forgery `custom_state_binding`'s module doc describes: "a custom AIR
    /// could prove a beautiful transition `R1 -> R2` while the turn commits `S1 -> S2`, and
    /// every existing gate passed."
    #[test]
    #[ignore = "folds two leaves through an aggregation layer (minutes); run with --ignored"]
    fn forged_root_custom_proof_is_rejected_by_the_state_fold() {
        let config = ir2_leaf_wrap_config();
        let program = state_binding_program();
        let (w, rows) = honest_witness();

        // The leg's REAL transition.
        let (real_old8, real_new8) = (root8(100), root8(200));
        // The sub-proof is about an UNRELATED transition.
        let (forged_old8, forged_new8) = (root8(900), root8(950));
        let forged_pis = state_pis(&forged_old8, &forged_new8);
        // The leg claims the sub-proof's GENUINE commitment — so the commitment tooth passes
        // and ONLY the state tooth can bite. (Isolating the new gate.)
        let claim = custom_proof_pi_commitment(&forged_pis);

        let custom_leaf =
            prove_custom_leaf_with_state_commitment(&program, &w, rows, &forged_pis, &config)
                .expect("the forged-root sub-proof still PROVES — that is the whole problem");
        let leg = dual_expose_leg_leaf(claim, &real_old8, &real_new8, &config);

        must_refuse(
            "a custom proof about a DIFFERENT transition minted a verifying state-bound fold",
            || prove_custom_binding_node_state_segmented(&leg, &custom_leaf, &config),
        );
    }

    /// **THE CANARY — the connects are load-bearing, shown without editing code.**
    ///
    /// The SAME forged-root inputs that the state fold above REFUSES are ACCEPTED by the
    /// commitment-only node (`prove_custom_binding_node_segmented`). That is not a bug in the
    /// old node — it is precisely its documented reach ("binds WHICH public inputs the
    /// sub-proof used ... does NOT bind what those public inputs SAY"). Running both over one
    /// forgery measures exactly what the state connects add: disable them (i.e. use the old
    /// node) and the forged-root proof folds cleanly.
    #[test]
    #[ignore = "folds the same forgery through two aggregation nodes (minutes); run with --ignored"]
    fn canary__the_commitment_only_node_accepts_the_forgery_the_state_node_refuses() {
        let config = ir2_leaf_wrap_config();
        let program = state_binding_program();
        let (w, rows) = honest_witness();

        let (real_old8, real_new8) = (root8(100), root8(200));
        let (forged_old8, forged_new8) = (root8(900), root8(950));
        let forged_pis = state_pis(&forged_old8, &forged_new8);
        let claim = custom_proof_pi_commitment(&forged_pis);

        let custom_leaf =
            prove_custom_leaf_with_state_commitment(&program, &w, rows, &forged_pis, &config)
                .expect("the forged-root sub-proof proves");
        let leg = dual_expose_leg_leaf(claim, &real_old8, &real_new8, &config);

        // THE CANARY: the state connects DISABLED (the pre-leg node) => the forgery PASSES.
        prove_custom_binding_node_segmented(&leg, &custom_leaf, &config).expect(
            "CANARY BROKEN: the commitment-only node was expected to ACCEPT this forged-root \
             proof (that acceptance is the gap the state leg closes). If this now refuses, the \
             forged-root tooth below is passing for some OTHER reason and no longer measures \
             the state connects.",
        );

        // THE LEG: the state connects ENABLED => the same forgery is UNSAT.
        must_refuse(
            "the state-bound node accepted a forged-root proof the canary proves is forgeable",
            || prove_custom_binding_node_state_segmented(&leg, &custom_leaf, &config),
        );
    }

    /// **THE PER-LANE TOOTH.** Every one of the 16 state-prefix lanes is load-bearing: a node
    /// binding only some would accept a forgery in the rest. For each lane k, the sub-proof
    /// declares roots differing from the leg's ONLY in lane k, and the fold must be UNSAT.
    #[test]
    #[ignore = "16 fold attempts (very slow); run with --ignored on the build box"]
    fn every_state_prefix_lane_is_bound_by_the_state_fold() {
        let config = ir2_leaf_wrap_config();
        let program = state_binding_program();
        let (w, rows) = honest_witness();
        let (real_old8, real_new8) = (root8(100), root8(200));

        for k in 0..CUSTOM_PI_STATE_PREFIX_LEN {
            let mut old8 = real_old8;
            let mut new8 = real_new8;
            if k < SEG_ANCHOR_WIDTH {
                old8[k] = BabyBear::new((old8[k].0 + 1) % BABYBEAR_P);
            } else {
                new8[k - SEG_ANCHOR_WIDTH] =
                    BabyBear::new((new8[k - SEG_ANCHOR_WIDTH].0 + 1) % BABYBEAR_P);
            }
            let pis = state_pis(&old8, &new8);
            let claim = custom_proof_pi_commitment(&pis); // honest for the forged PIs
            let custom_leaf =
                prove_custom_leaf_with_state_commitment(&program, &w, rows, &pis, &config)
                    .expect("the lane-forged sub-proof proves");
            let leg = dual_expose_leg_leaf(claim, &real_old8, &real_new8, &config);
            must_refuse(
                "a root forged in ONE state-prefix lane minted a verifying state-bound fold — \
                 that lane is NOT bound",
                || prove_custom_binding_node_state_segmented(&leg, &custom_leaf, &config),
            );
        }
    }

    /// FAIL-CLOSED: an 8-lane (commitment-only) custom leaf cannot be laundered through the
    /// state-binding node — it is REFUSED rather than silently degraded to a commitment-only
    /// connect that would LOOK state-bound and not be.
    #[test]
    #[ignore = "mints a STARK + leaf-wrap (minutes); run with --ignored"]
    fn a_commitment_only_leaf_is_refused_by_the_state_node() {
        use crate::custom_leaf_adapter::prove_custom_leaf_with_commitment;
        let config = ir2_leaf_wrap_config();
        let program = state_binding_program();
        let (w, rows) = honest_witness();
        let (old8, new8) = (root8(100), root8(200));
        let pis = state_pis(&old8, &new8);
        let claim = custom_proof_pi_commitment(&pis);

        // A leaf minted with the 8-lane (commitment-only) wrap.
        let thin_leaf = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
            .expect("the commitment-only leaf proves");
        let leg = dual_expose_leg_leaf(claim, &old8, &new8, &config);

        must_refuse(
            "a commitment-only leaf was accepted by the state-binding node",
            || prove_custom_binding_node_state_segmented(&leg, &thin_leaf, &config),
        );
    }
}

// ============================================================================
// THE APP-ROOT WELD FOLD TEETH (in-lib — no rotated mint needed).
//
// The keystone four consumers converged on: a custom sub-proof PUBLISHES an application root R
// (a board root, an outcome commitment, a winner) which the state weld does NOT tie to what the
// cell actually stores. These teeth exercise the fold that closes it — a pure light client
// witnesses that the PUBLISHED root R EQUALS the cell's REAL committed field for a declared key K.
//
// The leg leaf here is the minimal stand-in the existing state teeth use, WIDENED to also publish
// the leg's committed field octet at a fixed PI ahead of the wide anchors — the same exposure
// surface the deployed wide member would carry once its descriptor pins the field octet (the named
// big-bang leg-emit piece; see the module-level app-root doc). The custom sub-proof leaf is REAL
// (`prove_custom_leaf_with_app_root_commitment` over a genuine conservation `CellProgram`).
// ============================================================================
#[cfg(test)]
#[allow(non_snake_case)]
mod app_root_weld_fold_tests {
    use super::*;
    use crate::custom_leaf_adapter::{
        custom_app_root_claim_len, prove_custom_leaf_with_app_root_commitment,
        prove_custom_leaf_with_state_commitment, read_exposed_app_root,
    };
    use crate::custom_proof_bind::custom_proof_pi_commitment;
    use crate::ivc_turn_chain::{
        SEG_ANCHOR_WIDTH, ir2_leaf_wrap_config, prove_descriptor_leaf_dual_expose,
        prove_descriptor_leaf_expose_segment_and_claims,
    };
    use dregg_circuit::descriptor_ir2::{
        EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, VmConstraint2,
        prove_vm_descriptor2_for_config,
    };
    use dregg_circuit::dsl::circuit::{
        CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
    };
    use dregg_circuit::effect_vm::custom_state_binding::{
        AppRootBinding, CUSTOM_PI_STATE_PREFIX_LEN, custom_pi_state_prefix,
    };
    use dregg_circuit::field::BABYBEAR_P;
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
    use dregg_circuit::refusal::must_refuse;
    use std::collections::HashMap;

    /// Width of the published app root R this battery welds (an 8-felt octet root — automatafl's
    /// `board_new_root8` / the compose `outcome_commitment` shape).
    const APP_ROOT_LEN: usize = 8;
    /// The app declaration: R at PI [16..24) (the first app PI past the state prefix), welded to
    /// the leg's committed field key 0.
    fn binding() -> AppRootBinding {
        AppRootBinding {
            app_root_pi_offset: CUSTOM_PI_STATE_PREFIX_LEN,
            app_root_len: APP_ROOT_LEN,
            field_key: 0,
        }
    }

    /// Stand-in leg PI count: the deployed custom wide member's shape (62 base + 16 wide anchors),
    /// widened so the field octet claim [54..62) sits ahead of the anchors [62..78).
    const STANDIN_LEG_PI_COUNT: usize = 78;
    /// Fixed PI offset of the leg's committed field octet (ahead of the wide anchors).
    const FIELD_PI_LO: usize = 54;

    /// An APP-ROOT custom program: the same conservation shape as the state demo, publishing the
    /// state prefix AND an 8-felt app root — `[old8 ‖ new8 ‖ R8]` (24 PIs).
    fn app_root_program() -> CellProgram {
        let p_minus_1 = BabyBear::new(BABYBEAR_P - 1);
        let descriptor = CircuitDescriptor {
            name: "dregg-custom-app-root-demo-v1".to_string(),
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
            // [old8 ‖ new8 ‖ R8] — the ABI prefix plus one 8-felt app root.
            public_input_count: CUSTOM_PI_STATE_PREFIX_LEN + APP_ROOT_LEN,
            lookup_tables: vec![],
        };
        CellProgram::new(descriptor, 1)
    }

    fn honest_witness() -> (HashMap<String, Vec<BabyBear>>, usize) {
        let rows = 4;
        let mut w = HashMap::new();
        w.insert("old".into(), vec![BabyBear::new(10); rows]);
        w.insert("amt".into(), vec![BabyBear::new(5); rows]);
        w.insert("new".into(), vec![BabyBear::new(15); rows]);
        w.insert("dir".into(), vec![BabyBear::ZERO; rows]);
        (w, rows)
    }

    fn root8(base: u32) -> [BabyBear; 8] {
        core::array::from_fn(|k| BabyBear::new(base + k as u32))
    }

    /// The sub-proof's public inputs: `[old8 ‖ new8 ‖ R8]`.
    fn app_root_pis(
        old8: &[BabyBear; 8],
        new8: &[BabyBear; 8],
        r8: &[BabyBear; 8],
    ) -> Vec<BabyBear> {
        let mut pis = custom_pi_state_prefix(old8, new8).to_vec();
        pis.extend_from_slice(r8);
        pis
    }

    /// A stand-in leg leaf exposing `[segment ‖ commitment(8) ‖ field_K(8)]`: it publishes the
    /// claimed commitment at IR2 PI [46..54), the committed field octet at [54..62), and the REAL
    /// rotated roots in the last 16 PIs — every published lane pinned to a trace column by a
    /// `PiBinding` (FRI-bound, not free scalars).
    fn app_root_leg_leaf(
        claim: crate::custom_proof_bind::ProofBindCommitment,
        field8: &[BabyBear; 8],
        real_old8: &[BabyBear; 8],
        real_new8: &[BabyBear; 8],
        config: &DreggRecursionConfig,
    ) -> RecursionOutput<DreggRecursionConfig> {
        let n = STANDIN_LEG_PI_COUNT;
        let old_first = n - 2 * SEG_ANCHOR_WIDTH; // 62
        let new_first = n - SEG_ANCHOR_WIDTH; // 70

        // cols: 0..8 = commit, 8..16 = field_K, 16..24 = old8, 24..32 = new8.
        let mut constraints: Vec<VmConstraint2> = (0..CUSTOM_COMMIT_LEN)
            .map(|k| {
                VmConstraint2::Base(VmConstraint::PiBinding {
                    row: VmRow::First,
                    col: k,
                    pi_index: CUSTOM_COMMIT_PI_LO + k,
                })
            })
            .collect();
        for k in 0..APP_ROOT_LEN {
            constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: CUSTOM_COMMIT_LEN + k,
                pi_index: FIELD_PI_LO + k,
            }));
        }
        for k in 0..SEG_ANCHOR_WIDTH {
            constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: CUSTOM_COMMIT_LEN + APP_ROOT_LEN + k,
                pi_index: old_first + k,
            }));
            constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: CUSTOM_COMMIT_LEN + APP_ROOT_LEN + SEG_ANCHOR_WIDTH + k,
                pi_index: new_first + k,
            }));
        }

        let trace_width = CUSTOM_COMMIT_LEN + APP_ROOT_LEN + 2 * SEG_ANCHOR_WIDTH; // 32
        let desc = EffectVmDescriptor2 {
            name: "customVmDescriptor2R24-app-root-standin".to_string(),
            trace_width,
            public_input_count: n,
            tables: vec![],
            constraints,
            hash_sites: vec![],
            ranges: vec![],
        };

        let mut row: Vec<BabyBear> = Vec::with_capacity(trace_width);
        row.extend_from_slice(&claim);
        row.extend_from_slice(field8);
        row.extend_from_slice(real_old8);
        row.extend_from_slice(real_new8);
        let trace: Vec<Vec<BabyBear>> = (0..4).map(|_| row.clone()).collect();

        let mut pis = vec![BabyBear::ZERO; n];
        for k in 0..CUSTOM_COMMIT_LEN {
            pis[CUSTOM_COMMIT_PI_LO + k] = claim[k];
        }
        for k in 0..APP_ROOT_LEN {
            pis[FIELD_PI_LO + k] = field8[k];
        }
        for k in 0..SEG_ANCHOR_WIDTH {
            pis[old_first + k] = real_old8[k];
            pis[new_first + k] = real_new8[k];
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
        .expect("app-root leg stand-in proves (its published lanes are internally consistent)");

        prove_descriptor_leaf_expose_segment_and_claims(
            &desc,
            &inner,
            &pis,
            config,
            &[
                (CUSTOM_COMMIT_PI_LO, CUSTOM_COMMIT_LEN),
                (FIELD_PI_LO, APP_ROOT_LEN),
            ],
        )
        .expect("app-root leg leaf exposes segment ++ commitment ++ field_K")
    }

    /// The app-root leaf's exposed claim IS `[commitment(8) ‖ old8 ‖ new8 ‖ R8]`, and the R lanes
    /// are the leaf's REAL bound PIs — exposure and execution welded. (Cheap structural pole.)
    #[test]
    #[ignore = "mints a STARK + leaf-wrap (minutes); run with --ignored on the build box"]
    fn app_root_leaf_exposes_the_bound_published_root() {
        let config = ir2_leaf_wrap_config();
        let program = app_root_program();
        let (w, rows) = honest_witness();
        let (old8, new8, r8) = (root8(100), root8(200), root8(300));
        let pis = app_root_pis(&old8, &new8, &r8);

        let leaf = prove_custom_leaf_with_app_root_commitment(
            &program,
            &w,
            rows,
            &pis,
            &binding(),
            &config,
        )
        .expect("the app-root custom leaf proves");

        assert_eq!(
            read_exposed_app_root(&leaf, APP_ROOT_LEN).expect("R lanes present"),
            r8.to_vec(),
            "lanes [24..32) must re-expose the sub-proof's OWN bound published root R"
        );
    }

    /// **THE POSITIVE POLE.** An HONEST turn — the sub-proof's published R IS the leg's exposed
    /// committed field, the declared roots ARE the leg's real roots, and the claimed commitment is
    /// genuine — binds in the app-root weld fold.
    #[test]
    #[ignore = "folds two leaves through an aggregation layer (minutes); run with --ignored"]
    fn honest_app_root_bound_turn_binds_in_the_fold() {
        let config = ir2_leaf_wrap_config();
        let program = app_root_program();
        let (w, rows) = honest_witness();
        let (old8, new8, r8) = (root8(100), root8(200), root8(300));
        let pis = app_root_pis(&old8, &new8, &r8);
        let real = custom_proof_pi_commitment(&pis);

        let custom_leaf = prove_custom_leaf_with_app_root_commitment(
            &program,
            &w,
            rows,
            &pis,
            &binding(),
            &config,
        )
        .expect("the app-root custom sub-proof leaf proves");
        // The leg publishes the SAME field octet the sub-proof publishes as R.
        let leg = app_root_leg_leaf(real, &r8, &old8, &new8, &config);

        prove_custom_binding_node_app_root_segmented(&leg, &custom_leaf, &config, APP_ROOT_LEN)
            .expect("an honest app-root-bound turn must bind in the fold");
    }

    /// **THE HEADLINE TOOTH.** A custom sub-proof that PUBLISHES a root R which DISAGREES with the
    /// cell's real committed field — its commitment and its declared roots are honest (so tooth 1
    /// and tooth 2 pass), only R != field — has no satisfying partner: the app-root `connect` is a
    /// conflict ⇒ UNSAT ⇒ no root ⇒ the light client never receives a verifying artifact. This is
    /// the forgery ADMITTED today (the state node folds it green) and REFUSED by the keystone.
    #[test]
    #[ignore = "folds two leaves through an aggregation layer (minutes); run with --ignored"]
    fn disagreeing_published_root_is_rejected_by_the_app_root_fold() {
        let config = ir2_leaf_wrap_config();
        let program = app_root_program();
        let (w, rows) = honest_witness();
        let (old8, new8) = (root8(100), root8(200));
        // The cell's REAL committed field.
        let real_field = root8(300);
        // The sub-proof PUBLISHES a DIFFERENT root.
        let forged_r = root8(700);
        assert_ne!(real_field, forged_r);
        let pis = app_root_pis(&old8, &new8, &forged_r);
        // Honest commitment for the (forged-R) PIs, honest roots — so ONLY the app-root tooth bites.
        let claim = custom_proof_pi_commitment(&pis);

        let custom_leaf = prove_custom_leaf_with_app_root_commitment(
            &program,
            &w,
            rows,
            &pis,
            &binding(),
            &config,
        )
        .expect("the disagreeing-R sub-proof still PROVES — that is the whole problem");
        let leg = app_root_leg_leaf(claim, &real_field, &old8, &new8, &config);

        must_refuse(
            "a published root disagreeing with the cell's real field minted a verifying fold",
            || {
                prove_custom_binding_node_app_root_segmented(
                    &leg,
                    &custom_leaf,
                    &config,
                    APP_ROOT_LEN,
                )
            },
        );
    }

    /// **THE CANARY — the app-root connect is load-bearing, shown without editing code.**
    ///
    /// The SAME disagreeing-R turn the app-root fold REFUSES is ACCEPTED by the STATE node — which
    /// welds the commitment and the roots but never looks at R. Running both over one forgery
    /// measures exactly what the app-root connect adds: use the state node (R invisible) and the
    /// disagreeing-R turn folds cleanly.
    #[test]
    #[ignore = "folds the same forgery through two aggregation nodes (minutes); run with --ignored"]
    fn canary__the_state_node_accepts_the_app_root_forgery_the_keystone_refuses() {
        let config = ir2_leaf_wrap_config();
        let program = app_root_program();
        let (w, rows) = honest_witness();
        let (old8, new8) = (root8(100), root8(200));
        let real_field = root8(300);
        let forged_r = root8(700);
        let pis = app_root_pis(&old8, &new8, &forged_r);
        let claim = custom_proof_pi_commitment(&pis);

        // THE CANARY: the STATE node (no app-root connect) folds the disagreeing-R turn cleanly —
        // it welds commitment + roots (both honest here) and never sees R. A 24-lane state leaf +
        // a plain dual-expose leg (segment ++ commitment) is exactly the pre-keystone deployed pair.
        let state_leaf = prove_custom_leaf_with_state_commitment(&program, &w, rows, &pis, &config)
            .expect("the state leaf proves over the disagreeing-R PIs");
        // The plain dual-expose leg reads the descriptor's real rotated roots for its segment; a
        // minimal roots-only stand-in serves it (same construction the state teeth use).
        let state_leg = {
            // Reuse the app-root leg's descriptor but expose only [segment ++ commitment] via the
            // plain dual-expose — the field octet is simply not consumed.
            let n = STANDIN_LEG_PI_COUNT;
            let old_first = n - 2 * SEG_ANCHOR_WIDTH;
            let new_first = n - SEG_ANCHOR_WIDTH;
            let mut constraints: Vec<VmConstraint2> = (0..CUSTOM_COMMIT_LEN)
                .map(|k| {
                    VmConstraint2::Base(VmConstraint::PiBinding {
                        row: VmRow::First,
                        col: k,
                        pi_index: CUSTOM_COMMIT_PI_LO + k,
                    })
                })
                .collect();
            for k in 0..SEG_ANCHOR_WIDTH {
                constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
                    row: VmRow::First,
                    col: CUSTOM_COMMIT_LEN + k,
                    pi_index: old_first + k,
                }));
                constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
                    row: VmRow::First,
                    col: CUSTOM_COMMIT_LEN + SEG_ANCHOR_WIDTH + k,
                    pi_index: new_first + k,
                }));
            }
            let trace_width = CUSTOM_COMMIT_LEN + 2 * SEG_ANCHOR_WIDTH;
            let desc = EffectVmDescriptor2 {
                name: "customVmDescriptor2R24-state-standin".to_string(),
                trace_width,
                public_input_count: n,
                tables: vec![],
                constraints,
                hash_sites: vec![],
                ranges: vec![],
            };
            let mut row: Vec<BabyBear> = Vec::with_capacity(trace_width);
            row.extend_from_slice(&claim);
            row.extend_from_slice(&old8);
            row.extend_from_slice(&new8);
            let trace: Vec<Vec<BabyBear>> = (0..4).map(|_| row.clone()).collect();
            let mut lpis = vec![BabyBear::ZERO; n];
            for k in 0..CUSTOM_COMMIT_LEN {
                lpis[CUSTOM_COMMIT_PI_LO + k] = claim[k];
            }
            for k in 0..SEG_ANCHOR_WIDTH {
                lpis[old_first + k] = old8[k];
                lpis[new_first + k] = new8[k];
            }
            let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
                &desc,
                &trace,
                &lpis,
                &MemBoundaryWitness::default(),
                &[],
                &UMemBoundaryWitness::default(),
                &config,
            )
            .expect("state leg stand-in proves");
            prove_descriptor_leaf_dual_expose(&desc, &inner, &lpis, &config)
                .expect("state leg exposes segment ++ commitment")
        };
        prove_custom_binding_node_state_segmented(&state_leg, &state_leaf, &config).expect(
            "CANARY BROKEN: the state node was expected to ACCEPT this disagreeing-R turn (that \
             acceptance is the gap the app-root weld closes). If this now refuses, the headline \
             tooth is passing for some OTHER reason and no longer measures the app-root connect.",
        );

        // THE KEYSTONE: the app-root connect ENABLED ⇒ the same forgery is UNSAT.
        let custom_leaf = prove_custom_leaf_with_app_root_commitment(
            &program,
            &w,
            rows,
            &pis,
            &binding(),
            &config,
        )
        .expect("the app-root leaf proves");
        let leg = app_root_leg_leaf(claim, &real_field, &old8, &new8, &config);
        must_refuse(
            "the app-root node accepted a disagreeing-R turn the canary proves is forgeable",
            || {
                prove_custom_binding_node_app_root_segmented(
                    &leg,
                    &custom_leaf,
                    &config,
                    APP_ROOT_LEN,
                )
            },
        );
    }

    /// **THE PER-LANE TOOTH.** Every one of the 8 published-root lanes is load-bearing: a node
    /// binding only some would accept a forgery in the rest.
    #[test]
    #[ignore = "8 fold attempts (very slow); run with --ignored on the build box"]
    fn every_published_root_lane_is_bound_by_the_app_root_fold() {
        let config = ir2_leaf_wrap_config();
        let program = app_root_program();
        let (w, rows) = honest_witness();
        let (old8, new8) = (root8(100), root8(200));
        let real_field = root8(300);

        for k in 0..APP_ROOT_LEN {
            let mut r = real_field;
            r[k] = BabyBear::new((r[k].0 + 1) % BABYBEAR_P);
            let pis = app_root_pis(&old8, &new8, &r);
            let claim = custom_proof_pi_commitment(&pis); // honest for the forged PIs
            let custom_leaf = prove_custom_leaf_with_app_root_commitment(
                &program,
                &w,
                rows,
                &pis,
                &binding(),
                &config,
            )
            .expect("the lane-forged sub-proof proves");
            let leg = app_root_leg_leaf(claim, &real_field, &old8, &new8, &config);
            must_refuse(
                "a published root forged in ONE lane minted a verifying app-root fold — that lane \
                 is NOT bound",
                || {
                    prove_custom_binding_node_app_root_segmented(
                        &leg,
                        &custom_leaf,
                        &config,
                        APP_ROOT_LEN,
                    )
                },
            );
        }
    }

    /// FAIL-CLOSED: a 24-lane (state-only) custom leaf cannot be laundered through the app-root
    /// node — it is REFUSED rather than silently degraded to a state-only connect that would LOOK
    /// app-root-bound and not be.
    #[test]
    #[ignore = "mints a STARK + leaf-wrap (minutes); run with --ignored"]
    fn a_state_only_leaf_is_refused_by_the_app_root_node() {
        let config = ir2_leaf_wrap_config();
        let program = app_root_program();
        let (w, rows) = honest_witness();
        let (old8, new8, r8) = (root8(100), root8(200), root8(300));
        let pis = app_root_pis(&old8, &new8, &r8);
        let claim = custom_proof_pi_commitment(&pis);

        // A 24-lane state leaf (no exposed R).
        let state_leaf = prove_custom_leaf_with_state_commitment(&program, &w, rows, &pis, &config)
            .expect("the state-only leaf proves");
        let leg = app_root_leg_leaf(claim, &r8, &old8, &new8, &config);

        must_refuse(
            "a state-only leaf was accepted by the app-root node",
            || {
                prove_custom_binding_node_app_root_segmented(
                    &leg,
                    &state_leaf,
                    &config,
                    APP_ROOT_LEN,
                )
            },
        );
    }
}
