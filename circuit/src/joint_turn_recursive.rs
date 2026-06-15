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
//!     ([`RecursionVk`]) must equal a caller-held trust anchor;
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

#![cfg(feature = "recursion")]

use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing as _;
use p3_recursion::ProveNextLayerParams;
use p3_recursion::build_and_prove_next_layer;
use p3_recursion::{BatchOnly, RecursionInput, RecursionOutput};

use crate::field::BabyBear;
use crate::joint_turn_aggregation::{
    DescriptorParticipant, JointAggError, JointTurnAggregationAir, verify_descriptor_participant,
};
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, RecursionCompatibleProof, RecursionVk, create_recursion_backend,
    prove_inner_for_air_with_config, recursion_vk_fingerprint, verify_inner_for_air_with_config,
    verify_recursive_batch_proof_with_config,
};

const D: usize = 4;

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
/// reads [`pi::TURN_HASH_BASE`](crate::effect_vm::pi) (the shared turn id)
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
    let (binding_matrix, binding_pis) =
        recursion_binding_trace_descriptor_rotated(&participants)?;
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
// Tests
// ============================================================================
//
// Bucket-F (PATH-PRESERVE Phase 5a): the in-lib `#[cfg(test)] mod tests` (the 3-cell
// recursive joint, disagreeing-turn-id CG-2, tampered-participant, ungated-forged-cell-commit,
// and in-circuit-wrap teeth) RELOCATED to the integration test
// `circuit/tests/joint_turn_recursive_rotated.rs`, which mints the mandatory ROTATED
// participant through `dregg_turn::rotation_witness::mint_rotated_participant_leg` (the
// circuit lib cannot — no `dregg-cell` / `dregg-turn` dep, the cycle).
