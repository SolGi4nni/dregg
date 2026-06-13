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
use crate::ivc_turn_chain::prove_descriptor_leaf;
use crate::joint_turn_aggregation::{
    DescriptorParticipant, JointAggError, JointTurnAggregationAir,
    recursion_binding_trace_descriptor, verify_descriptor_participant,
};
use crate::lean_descriptor_air::EffectVmDescriptorAir;
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, RecursionCompatibleProof, RecursionVk, create_recursion_backend,
    create_recursion_config, prove_inner_for_air, recursion_vk_fingerprint, verify_inner_for_air,
    verify_recursive_batch_proof,
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

// ============================================================================
// Binding leaf: the shared-turn-id agreement + commitment digest.
// ============================================================================

/// Build the [`JointTurnAggregationAir`] inner proof binding the N
/// participants' shared turn id (CG-2) and the commitment hash-chain digest.
/// The trace generator performs the host-side mismatch check and the AIR's own
/// CG-2 constraint rejects a disagreement in-circuit too.
fn prove_binding_leaf(
    participants: &[&DescriptorParticipant],
) -> Result<(RecursionCompatibleProof, Vec<BabyBear>), JointAggError> {
    let (matrix, pis) = recursion_binding_trace_descriptor(participants)?;
    let air = JointTurnAggregationAir;
    let proof = prove_inner_for_air(&air, matrix, &pis);
    verify_inner_for_air(&air, &proof, &pis)
        .map_err(|reason| JointAggError::AggregationProofInvalid { reason })?;
    Ok((proof, pis))
}

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
/// whole-turn DESCRIPTOR proofs and the shared-turn-id binding into ONE
/// succinct recursive proof.
///
/// Steps:
///   1. host admission: >= 2 cells; every cell's production descriptor proof
///      verifies SELECTOR-BOUND through the Lean descriptor verifier
///      ([`verify_descriptor_participant`], which also determines each cell's
///      selector); all cells agree on the shared turn id (CG-2, host side);
///   2. prove the binding leaf (rejects disagreeing turn ids in-circuit too);
///   3. re-prove each cell's REAL descriptor AIR over its OWN execution trace
///      as a recursion-compatible uni-STARK
///      ([`prove_descriptor_leaf`](crate::ivc_turn_chain) — the whole-chain
///      recipe, applied per cell);
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
    prove_joint_core(&refs, &selectors)
}

/// **THE UNGATED PROVER (tamper surface).** Fold a joint turn WITHOUT the
/// host-side descriptor admission, taking the prover's CLAIMED selectors at
/// face value. Exists to make the soundness claim falsifiable: a malicious
/// prover that skips the gate and feeds a forged `cell_commit` still has to
/// satisfy the REAL descriptor AIR at the leaf — and a forged commitment has
/// no satisfying witness, so the fold fails and no verifying root exists
/// (`ungated_joint_prover_with_forged_cell_commit_cannot_produce_a_root`).
pub fn prove_joint_turn_recursive_without_host_gate(
    cells: &[JointCell],
    claimed_selectors: &[usize],
) -> Result<RecursiveJointTurnProof, JointAggError> {
    let refs: Vec<&JointCell> = cells.iter().collect();
    prove_joint_core(&refs, claimed_selectors)
}

/// The shared fold core (steps 2–5 of [`prove_joint_turn_recursive`]).
fn prove_joint_core(
    cells: &[&JointCell],
    selectors: &[usize],
) -> Result<RecursiveJointTurnProof, JointAggError> {
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

    let config = create_recursion_config();
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // (2) binding leaf (shared-tid agreement + digest), proven in-circuit-ready.
    let (binding_inner, binding_pis) = prove_binding_leaf(&participants)?;
    let shared_turn_id = binding_pis[0];
    let bundle_digest = binding_pis[2];

    // (3) one REAL descriptor leaf per cell — FAIL FAST before any wrap: a
    // forged cell has no satisfying leaf, so no recursion work happens for it.
    let mut leaves: Vec<(
        EffectVmDescriptorAir,
        RecursionCompatibleProof,
        Vec<BabyBear>,
    )> = Vec::with_capacity(cells.len());
    for (i, c) in cells.iter().enumerate() {
        let leaf = prove_descriptor_leaf(c, selectors[i])
            .map_err(|reason| JointAggError::ParticipantProofInvalid { index: i, reason })?;
        leaves.push(leaf);
    }

    // (4) wrap every leaf in its own in-circuit verifier layer (uni→batch).
    let mut batch_leaves: Vec<RecursionOutput<DreggRecursionConfig>> =
        Vec::with_capacity(cells.len() + 1);
    for (i, (air, leaf_inner, leaf_pis)) in leaves.iter().enumerate() {
        let p3_pis: Vec<P3BabyBear> = leaf_pis.iter().map(|&v| to_p3(v)).collect();
        let input = RecursionInput::UniStark {
            proof: leaf_inner,
            air,
            public_inputs: p3_pis,
            preprocessed_commit: None,
        };
        let wrapped =
            build_and_prove_next_layer::<DreggRecursionConfig, EffectVmDescriptorAir, _, D>(
                &input, &config, &backend, &params,
            )
            .map_err(|e| JointAggError::ParticipantProofInvalid {
                index: i,
                reason: format!("recursive descriptor leaf failed: {e:?}"),
            })?;
        batch_leaves.push(wrapped);
    }

    // The binding leaf wrapped uni→batch (its own recursive layer).
    {
        let air = JointTurnAggregationAir;
        let p3_pis: Vec<P3BabyBear> = binding_pis.iter().map(|&v| to_p3(v)).collect();
        let input = RecursionInput::UniStark {
            proof: &binding_inner,
            air: &air,
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

// ============================================================================
// C4 — THE ROTATED joint fold (the v1-deletion path).
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
    let (binding_matrix, binding_pis) =
        recursion_binding_trace_descriptor_rotated(&participants)?;
    let binding_air = JointTurnAggregationAir;
    let binding_inner = prove_inner_for_air(&binding_air, binding_matrix, &binding_pis);
    verify_inner_for_air(&binding_air, &binding_inner, &binding_pis)
        .map_err(|reason| JointAggError::AggregationProofInvalid { reason })?;
    let shared_turn_id = binding_pis[0];
    let bundle_digest = binding_pis[2];

    // (3)+(4) one rotated descriptor leaf per cell.
    let mut batch_leaves: Vec<RecursionOutput<DreggRecursionConfig>> =
        Vec::with_capacity(cells.len() + 1);
    for (i, c) in cells.iter().enumerate() {
        let leg = c.participant.rotated.as_ref().ok_or_else(|| {
            JointAggError::ParticipantProofInvalid {
                index: i,
                reason: "rotated joint fold: cell carries no rotated leg".to_string(),
            }
        })?;
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

    // (2) Claimed publics, read against the carried binding proof.
    let claimed_pis = vec![proof.shared_turn_id, BabyBear::ZERO, proof.bundle_digest];
    verify_inner_for_air(&JointTurnAggregationAir, &proof.binding_proof, &claimed_pis)
        .map_err(|reason| JointAggError::ClaimedPublicsUnattested { reason })?;

    // (3) The root.
    verify_recursive_batch_proof(&proof.root.0)
        .map_err(|reason| JointAggError::AggregationProofInvalid { reason })
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effect_vm::pi;
    use crate::effect_vm::{CellState, Effect, generate_effect_vm_trace, sel};
    use crate::effect_vm_descriptors::descriptor_for_selector;
    use crate::field::BabyBear;
    use crate::lean_descriptor_air::{parse_vm_descriptor, prove_vm_descriptor};

    /// Build a REAL per-cell joint participant on the production descriptor
    /// path: execute a `Transfer` debit, write the shared turn id into
    /// [`pi::TURN_HASH_BASE`] BEFORE proving (the descriptor PI prefix covers
    /// it, so the proof Fiat–Shamir-binds the turn id), prove the 186-column
    /// trace through the Lean transfer descriptor, and carry the trace as the
    /// leaf witness.
    fn make_cell(balance: u64, nonce: u32, turn_id: u32) -> JointCell {
        let state = CellState::new(balance, nonce);
        let effects = vec![Effect::Transfer {
            amount: 5,
            direction: 1,
        }];
        let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);
        public_inputs[pi::TURN_HASH_BASE] = BabyBear::new(turn_id);
        let json = descriptor_for_selector(sel::TRANSFER).expect("transfer descriptor registered");
        let desc = parse_vm_descriptor(json).expect("transfer descriptor parses");
        let dpis = &public_inputs[..desc.public_input_count];
        let proof =
            prove_vm_descriptor(&desc, &trace, dpis).expect("descriptor proves honest transfer");
        JointCell::new(
            DescriptorParticipant::v1(proof, public_inputs),
            trace,
        )
    }

    /// GOLD: a 3-cell joint turn — REAL descriptor leaves, each the full
    /// `EffectVmDescriptorAir` constraint set re-proven over its own execution
    /// trace and verified IN-CIRCUIT by the wrap layer — folded into ONE
    /// recursive proof that verifies under its honest VK anchor.
    ///
    /// Piggybacked REFUSED cases (no extra proving): a mismatched VK anchor is
    /// refused; relabeled carried publics (`bundle_digest`, `shared_turn_id`)
    /// are refused by the claimed-publics attestation.
    #[test]
    fn three_cell_joint_turn_recursive_proves_and_verifies() {
        let cells = vec![
            make_cell(100, 0, 0x5151),
            make_cell(200, 1, 0x5151),
            make_cell(300, 2, 0x5151),
        ];

        let mut gold = prove_joint_turn_recursive(&cells)
            .expect("agreeing 3-cell joint turn must prove recursively");
        assert_eq!(gold.num_cells, 3);
        assert_eq!(gold.shared_turn_id, BabyBear::new(0x5151));

        let vk = gold.root_vk_fingerprint();
        verify_joint_turn_recursive(&gold, &vk)
            .expect("recursive 3-cell joint-turn root proof must verify under its anchor");

        // REFUSED: a mismatched VK anchor.
        let mut wrong = vk;
        wrong.0[0] ^= 0xFF;
        match verify_joint_turn_recursive(&gold, &wrong) {
            Err(JointAggError::VkFingerprintMismatch { .. }) => {}
            other => panic!("a mismatched VK anchor must be refused; got {other:?}"),
        }

        // REFUSED: relabeled bundle_digest (claiming a different cell bundle).
        let honest_digest = gold.bundle_digest;
        gold.bundle_digest = honest_digest + BabyBear::ONE;
        match verify_joint_turn_recursive(&gold, &vk) {
            Err(JointAggError::ClaimedPublicsUnattested { .. }) => {}
            other => panic!("a relabeled bundle_digest must be refused; got {other:?}"),
        }
        gold.bundle_digest = honest_digest;

        // REFUSED: relabeled shared_turn_id.
        let honest_tid = gold.shared_turn_id;
        gold.shared_turn_id = honest_tid + BabyBear::ONE;
        match verify_joint_turn_recursive(&gold, &vk) {
            Err(JointAggError::ClaimedPublicsUnattested { .. }) => {}
            other => panic!("a relabeled shared_turn_id must be refused; got {other:?}"),
        }
        gold.shared_turn_id = honest_tid;

        // The restored artifact still verifies.
        verify_joint_turn_recursive(&gold, &vk).expect("restored honest artifact verifies again");
    }

    /// GOLD teeth (turn-id): disagreeing turn ids are rejected (the binding
    /// leaf's CG-2 is unsatisfiable / the host check fires) before any tree.
    #[test]
    fn recursive_rejects_disagreeing_turn_ids() {
        let cells = vec![
            make_cell(100, 0, 0xABCD),
            make_cell(200, 7, 0x1234), // DIFFERENT turn id
            make_cell(300, 2, 0xABCD),
        ];

        match prove_joint_turn_recursive(&cells) {
            Err(JointAggError::SharedTurnIdMismatch {
                expected, found, ..
            }) => {
                assert_eq!(expected, 0xABCD);
                assert_eq!(found, 0x1234);
            }
            Ok(_) => panic!("disagreeing turn ids must not produce a recursive root proof"),
            Err(other) => panic!("expected SharedTurnIdMismatch, got {other:?}"),
        }
    }

    /// GOLD teeth (tampered participant): forging a cell's claimed post-state
    /// commitment makes the host-side descriptor admission reject it at its
    /// index — the first line of defense. (The in-circuit line is
    /// `ungated_joint_prover_with_forged_cell_commit_cannot_produce_a_root`.)
    #[test]
    fn recursive_rejects_tampered_participant_proof() {
        let mut cells = vec![
            make_cell(100, 0, 0x77),
            make_cell(200, 1, 0x77),
            make_cell(300, 2, 0x77),
        ];
        // Forge cell 1's claimed post-state commitment (turn ids still agree).
        cells[1].participant.public_inputs[pi::NEW_COMMIT] =
            cells[1].participant.public_inputs[pi::NEW_COMMIT] + BabyBear::ONE;

        match prove_joint_turn_recursive(&cells) {
            Err(JointAggError::ParticipantProofInvalid { index, .. }) => {
                assert_eq!(index, 1, "the tampered cell must be the one rejected");
            }
            Ok(_) => panic!("a tampered participant must not produce a recursive root proof"),
            Err(other) => panic!("expected ParticipantProofInvalid, got {other:?}"),
        }
    }

    /// **THE LEAF TOOTH, NOW BITING (formerly the `#[ignore]`d
    /// `gold_joint_leaf_is_still_a_shape_stub_no_in_circuit_execution_tooth`).**
    /// The per-cell leaves are no longer `EffectVmShapeAir` stubs: they are
    /// the REAL descriptor AIR re-proven over each cell's own execution trace.
    /// So an UNGATED joint prover — skipping the host-side descriptor
    /// admission entirely — that forges a `cell_commit` (a post-state that
    /// execution never reached) has NO satisfying leaf: the descriptor's
    /// Poseidon2 hash sites force the commit cells to be the genuine digests.
    /// The fold fails (prover refuses the unsatisfiable trace in debug;
    /// self-verify rejects in release) and no verifying root exists — per-cell
    /// execution soundness no longer rests on the host gate.
    #[test]
    fn ungated_joint_prover_with_forged_cell_commit_cannot_produce_a_root() {
        // The forged cell FIRST so the fold fails at its leaf before any
        // expensive wrap runs for the honest cell.
        let mut forged = make_cell(100, 0, 0x77);
        let honest = make_cell(200, 1, 0x77);

        // The lie: claim a post-state commitment execution never reached.
        forged.participant.public_inputs[pi::NEW_COMMIT] =
            forged.participant.public_inputs[pi::NEW_COMMIT] + BabyBear::ONE;
        let cells = [forged, honest];

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_joint_turn_recursive_without_host_gate(&cells, &[sel::TRANSFER, sel::TRANSFER])
        }));
        let rejected = match result {
            Ok(Ok(_)) => false, // a verifying root over a forged cell — soundness hole!
            Ok(Err(_)) => true,
            Err(_) => true,
        };
        assert!(
            rejected,
            "a host-gate-skipping joint prover with a forged cell_commit must NOT obtain a \
             root — the descriptor leaf is the in-circuit tooth"
        );
    }

    /// GOLD teeth (in-circuit wrap, the load-bearing one): a descriptor leaf
    /// honestly proven for its real commitments but fed to the recursive
    /// verifier layer with public inputs claiming a FORGED commitment. The
    /// wrap layer's IN-CIRCUIT verifier pins the claimed PIs against the
    /// proof, so the mismatched-PI leaf is unsatisfiable and
    /// `build_and_prove_next_layer` MUST fail — even a "valid proof object"
    /// cannot be re-labelled with a different cell_commit at the wrap.
    #[test]
    fn recursive_layer_rejects_mismatched_leaf_public_inputs() {
        let cell = make_cell(100, 0, 0x99);
        let (air, inner, dpis) =
            prove_descriptor_leaf(&cell, sel::TRANSFER).expect("honest descriptor leaf proves");

        let config = create_recursion_config();
        let backend = create_recursion_backend();
        let params = ProveNextLayerParams::default();

        // FORGE the post-state commitment in the PIs fed to the wrap layer.
        let mut forged = dpis.clone();
        forged[pi::NEW_COMMIT] = forged[pi::NEW_COMMIT] + BabyBear::ONE;
        let p3_forged: Vec<P3BabyBear> = forged.iter().map(|&v| to_p3(v)).collect();
        let input = RecursionInput::UniStark {
            proof: &inner,
            air: &air,
            public_inputs: p3_forged,
            preprocessed_commit: None,
        };

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            build_and_prove_next_layer::<DreggRecursionConfig, EffectVmDescriptorAir, _, D>(
                &input, &config, &backend, &params,
            )
        }));
        let rejected = match result {
            Ok(Ok(_)) => false, // wrapped a forged-PI leaf — soundness hole!
            Ok(Err(_)) => true, // recursion returned an error — rejected.
            Err(_) => true,     // unsatisfiable verifier circuit panicked — rejected.
        };
        assert!(
            rejected,
            "a descriptor leaf fed a forged cell_commit must be rejected by the IN-CIRCUIT \
             recursive verifier — the recursion, not the host check, is the tooth"
        );
    }
}
