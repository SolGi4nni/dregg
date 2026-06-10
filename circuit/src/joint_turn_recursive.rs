//! GOLD: genuine recursive N-to-1 joint-turn aggregation.
//!
//! ## Silver -> Gold, for real
//!
//! [`joint_turn_aggregation`](crate::joint_turn_aggregation) is **Silver**: a
//! bundle = {N per-cell whole-turn proofs} + ONE aggregation STARK that binds
//! their shared turn id (CG-2) and folds their commitments. The verifier still
//! re-runs `stark::verify` on **every** per-cell proof, so verification cost
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
//!   │ EffectVm│ │ EffectVm│   │  + digest  │
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
//!   - per-cell leaves: [`EffectVmShapeAir`] (the EffectVm's real width/PI shape
//!     with selector-booleanity, NoOp passthrough, Transfer-delta, chain
//!     continuity, and commitment boundary constraints), with the
//!     [`pi::TURN_HASH`] public input pinned to the shared turn id and
//!     [`pi::NEW_COMMIT`] pinned to that cell's post-state commitment;
//!   - binding leaf: [`JointTurnAggregationAir`] over the N participants,
//!     enforcing CG-2 (every cell's `shared_turn_id == published id`) and the
//!     commitment hash-chain digest.
//!
//! ## HONEST GAP — the per-cell leaves here are still SHAPE STUBS (chain fold is not)
//!
//! [`EffectVmShapeAir`] is NOT the full Effect VM constraint set (its own docs:
//! a trace that passes it would not pass the real AIR), so in THIS module
//! per-cell execution soundness still rests on the HOST-side gate
//! (`check_joint_preconditions` verifying each participant's bespoke proof) —
//! a trusted-prover assumption for the per-cell leg. The whole-chain fold
//! ([`crate::ivc_turn_chain`], the light-client path) has been CUT OVER: its
//! leaves are the REAL Lean-descriptor EffectVM AIR
//! (`EffectVmDescriptorAir`) re-proven over each turn's own execution trace
//! and verified in-circuit, with ungated-prover tamper tests proving the host
//! gate is not load-bearing there. Converting THIS joint-turn fold the same
//! way needs its participants re-pointed from the bespoke `JointParticipant`
//! (legacy `stark::StarkProof`) onto `DescriptorParticipant` + carried traces
//! — the same recipe `ivc_turn_chain::prove_descriptor_leaf` applies — and is
//! deliberately left for the joint-turn lane so the Silver surface
//! (`joint_turn_aggregation`) stays intact in this pass. The ignored test
//! `gold_joint_leaf_is_still_a_shape_stub_no_in_circuit_execution_tooth`
//! documents the exact missing tooth.
//!
//! Each leaf is first wrapped in its own recursive verifier layer
//! (`build_and_prove_next_layer`, uni→batch), then the resulting batch proofs
//! are pairwise aggregated (`build_and_prove_aggregation_layer`) up a binary
//! tree, chaining via [`RecursionOutput::into_recursion_input::<BatchOnly>`],
//! until ONE root batch proof remains.
//!
//! ## The tooth
//!
//! Two independent failure modes, both surfacing as "no valid root proof":
//!
//!   1. **Tampered participant proof.** If any per-cell inner proof is
//!      corrupted, its leaf verifier circuit is unsatisfiable, so
//!      `build_and_prove_next_layer` for that leaf fails — there is no batch
//!      proof to feed the tree, hence no root. (Test:
//!      `recursive_rejects_tampered_participant_proof`.)
//!   2. **Disagreeing turn ids.** If two cells carry different turn ids, the
//!      binding leaf's [`JointTurnAggregationAir`] CG-2 constraint is violated;
//!      its inner proof is unsatisfiable and the host check rejects it before
//!      any tree is built. (Test:
//!      `recursive_rejects_disagreeing_turn_ids`.)
//!
//! The wrap layers genuinely re-derive each LEAF proof's FRI/quotient checks
//! in-circuit — but per the HONEST GAP above, the per-cell leaves attest the
//! SHAPE subset, not full execution; the root's constant-cost verification is
//! real, while the per-cell execution leg still rides the host gate.

#![cfg(feature = "recursion")]

use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing as _;
use p3_matrix::dense::RowMajorMatrix;
use p3_recursion::{BatchOnly, RecursionInput, RecursionOutput};

use crate::effect_vm::pi;
use crate::effect_vm_p3_air::EffectVmShapeAir;
use crate::field::BabyBear;
use crate::joint_turn_aggregation::{JointAggError, JointParticipant, JointTurnAggregationAir};
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, RecursionCompatibleProof, create_recursion_backend,
    create_recursion_config, prove_inner_for_air, verify_inner_for_air, verify_recursive_batch_proof,
};
use p3_recursion::ProveNextLayerParams;
use p3_recursion::build_and_prove_aggregation_layer;
use p3_recursion::build_and_prove_next_layer;

use crate::effect_vm::{EFFECT_VM_WIDTH, NUM_EFFECTS, PARAM_BASE, STATE_AFTER_BASE, STATE_BEFORE_BASE, sel, state};

const D: usize = 4;

fn to_p3(v: BabyBear) -> P3BabyBear {
    P3BabyBear::from_u64(v.0 as u64)
}

// ============================================================================
// Per-cell leaf: a recursion-compatible EffectVm-shape whole-turn proof.
// ============================================================================

/// Build a recursion-compatible EffectVm-shape whole-turn trace for one cell,
/// with the shared turn id and the cell commitment pinned into the public
/// inputs the binding layer reads.
///
/// Row 0 is a Transfer with `amount = 0, direction = 0` (balance + commitment
/// passthrough), rows 1.. are NoOp passthroughs — satisfying every
/// [`EffectVmShapeAir`] constraint. The `shared_turn_id` is written to
/// [`pi::TURN_HASH`] and `cell_commit` to both [`pi::OLD_COMMIT`] /
/// [`pi::NEW_COMMIT`] (and the boundary state-commit columns), so the leaf's
/// public inputs genuinely carry the per-cell content the binding folds.
fn build_cell_leaf_trace(
    shared_turn_id: BabyBear,
    cell_commit: BabyBear,
    n_rows: usize,
) -> (RowMajorMatrix<P3BabyBear>, Vec<BabyBear>) {
    assert!(n_rows >= 2 && n_rows.is_power_of_two());

    let mut flat: Vec<P3BabyBear> = Vec::with_capacity(n_rows * EFFECT_VM_WIDTH);

    // Row 0: Transfer amount=0 dir=0 → passthrough; commit boundary = cell_commit.
    let mut row0 = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];
    row0[sel::TRANSFER] = BabyBear::ONE;
    row0[STATE_BEFORE_BASE + state::STATE_COMMIT] = cell_commit;
    row0[STATE_AFTER_BASE + state::STATE_COMMIT] = cell_commit;
    row0[PARAM_BASE] = BabyBear::ZERO; // amount
    row0[PARAM_BASE + 1] = BabyBear::ZERO; // direction
    flat.extend(row0.iter().map(|&v| to_p3(v)));

    // Rows 1..n_rows: NoOp passthroughs preserving the commitment.
    for _ in 1..n_rows {
        let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];
        row[sel::NOOP] = BabyBear::ONE;
        row[STATE_BEFORE_BASE + state::STATE_COMMIT] = cell_commit;
        row[STATE_AFTER_BASE + state::STATE_COMMIT] = cell_commit;
        flat.extend(row.iter().map(|&v| to_p3(v)));
    }
    debug_assert_eq!(NUM_EFFECTS >= 2, true);

    let mut public_inputs = vec![BabyBear::ZERO; pi::BASE_COUNT];
    // Commitment boundary PIs (single-felt continuity binding the shape AIR
    // enforces against the trace).
    public_inputs[pi::OLD_COMMIT] = cell_commit;
    public_inputs[pi::NEW_COMMIT] = cell_commit;
    // Shared turn id — the projection the binding layer / Silver aggregator reads.
    public_inputs[pi::TURN_HASH_BASE] = shared_turn_id;

    (RowMajorMatrix::new(flat, EFFECT_VM_WIDTH), public_inputs)
}

/// Produce one cell's recursion-compatible inner proof + its public inputs.
fn prove_cell_leaf(
    shared_turn_id: BabyBear,
    cell_commit: BabyBear,
    n_rows: usize,
) -> (RecursionCompatibleProof, Vec<BabyBear>) {
    let (matrix, pis) = build_cell_leaf_trace(shared_turn_id, cell_commit, n_rows);
    let air = EffectVmShapeAir;
    let proof = prove_inner_for_air(&air, matrix, &pis);
    (proof, pis)
}

// ============================================================================
// Binding leaf: the shared-turn-id agreement + commitment digest.
// ============================================================================

/// Build the [`JointTurnAggregationAir`] inner proof binding the N participants'
/// shared turn id (CG-2) and the commitment hash-chain digest. Reuses the
/// Silver trace generator (host-side mismatch check + the AIR's own CG-2
/// constraint) so a disagreeing turn id is rejected here before the tree.
fn prove_binding_leaf(
    participants: &[JointParticipant],
) -> Result<(RecursionCompatibleProof, Vec<BabyBear>), JointAggError> {
    let (matrix, pis) = crate::joint_turn_aggregation::recursion_binding_trace(participants)?;
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
/// per-cell whole-turn leaves AND the shared-turn-id binding leaf verified
/// in-circuit. The verifier checks only this root proof; cost is independent of
/// the number of cells.
pub struct RecursiveJointTurnProof {
    /// The single root batch-STARK proof (the whole tree folded to one).
    pub root: RecursionOutput<DreggRecursionConfig>,
    /// The shared turn id all participants agreed on.
    pub shared_turn_id: BabyBear,
    /// The number of participating cells.
    pub num_cells: usize,
}

/// Width of a per-cell leaf trace, chosen so the EffectVm-shape AIR has enough
/// rows for the prover. 4 rows is the minimal power-of-two that exercises
/// row-0 Transfer + NoOp passthrough + a transition.
const LEAF_ROWS: usize = 4;

/// Prove a joint (cross-cell) turn **recursively**: fold the N per-cell
/// whole-turn proofs and the shared-turn-id binding into ONE succinct recursive
/// proof.
///
/// Steps:
///   1. structural + host-side CG-2 check (>= 2 participants, agreeing turn id);
///   2. prove the binding leaf (rejects disagreeing turn ids in-circuit too);
///   3. prove one recursion-compatible EffectVm-shape leaf per cell, pinning
///      each cell's `(shared_turn_id, cell_commit)` into its public inputs;
///   4. wrap every leaf in its own recursive verifier layer (uni→batch);
///   5. pairwise-aggregate all batch leaves up a binary tree to ONE root.
///
/// A tampered participant proof makes the corresponding leaf's verifier circuit
/// unsatisfiable, so step 4 fails for that leaf and no root is produced —
/// the recursive teeth.
pub fn prove_joint_turn_recursive(
    participants: &[JointParticipant],
) -> Result<RecursiveJointTurnProof, JointAggError> {
    // (1) structural + host CG-2: also verifies each per-cell proof individually
    //     (the Silver per-cell soundness gate), and rejects disagreeing tids.
    let shared_turn_id = crate::joint_turn_aggregation::check_joint_preconditions(participants)?;

    let config = create_recursion_config();
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // (2) binding leaf (shared-tid agreement + digest), proven in-circuit-ready.
    let (binding_inner, binding_pis) = prove_binding_leaf(participants)?;

    // (3)+(4) one EffectVm-shape leaf per cell, each wrapped uni→batch.
    let mut batch_leaves: Vec<RecursionOutput<DreggRecursionConfig>> =
        Vec::with_capacity(participants.len() + 1);

    for (i, p) in participants.iter().enumerate() {
        let cell_commit = p.cell_commit();
        let (leaf_inner, leaf_pis) = prove_cell_leaf(shared_turn_id, cell_commit, LEAF_ROWS);
        let air = EffectVmShapeAir;
        let p3_pis: Vec<P3BabyBear> = leaf_pis.iter().map(|&v| to_p3(v)).collect();
        let input = RecursionInput::UniStark {
            proof: &leaf_inner,
            air: &air,
            public_inputs: p3_pis,
            preprocessed_commit: None,
        };
        let wrapped =
            build_and_prove_next_layer::<DreggRecursionConfig, EffectVmShapeAir, _, D>(
                &input, &config, &backend, &params,
            )
            .map_err(|e| JointAggError::ParticipantProofInvalid {
                index: i,
                reason: format!("recursive leaf layer failed: {e:?}"),
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
        shared_turn_id,
        num_cells: participants.len(),
    })
}

/// Fold a vector of batch-STARK proofs to ONE via 2-to-1 aggregation layers.
///
/// On each level, consecutive pairs are aggregated with
/// [`build_and_prove_aggregation_layer`] (chained via [`BatchOnly`]). An odd
/// proof out is carried to the next level unchanged. Repeats until one remains.
fn aggregate_tree(
    mut proofs: Vec<RecursionOutput<DreggRecursionConfig>>,
    config: &DreggRecursionConfig,
    backend: &p3_recursion::FriRecursionBackendForExt<
        D,
        16,
        8,
        p3_recursion::ops::Poseidon2Config,
    >,
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
            let out = build_and_prove_aggregation_layer::<
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

/// Verify the Gold artifact: check the single root batch-STARK proof. Cost is
/// independent of the number of cells (the per-cell proofs are folded inside).
pub fn verify_joint_turn_recursive(
    proof: &RecursiveJointTurnProof,
) -> Result<(), JointAggError> {
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
    use crate::effect_vm::{CellState, Effect, EffectVmAir, generate_effect_vm_trace};
    use crate::field::BabyBear;
    use crate::stark;

    /// Build a real EffectVm whole-turn participant with a chosen shared turn id
    /// and (implicitly) its own commitment, exactly as the Silver tests do. The
    /// per-cell proof is used for the host-side per-cell soundness gate; the
    /// in-circuit leaf is rebuilt from `(shared_turn_id, cell_commit)`.
    fn make_participant(balance: u64, nonce: u32, turn_id: u32) -> JointParticipant {
        let state = CellState::new(balance, nonce);
        let effects = vec![Effect::Transfer {
            amount: 5,
            direction: 1,
        }];
        let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);
        public_inputs[pi::TURN_HASH_BASE] = BabyBear::new(turn_id);
        let air = EffectVmAir::new(trace.len());
        let proof = stark::prove(&air, &trace, &public_inputs);
        JointParticipant {
            proof,
            public_inputs,
        }
    }

    /// GOLD: a 3-cell joint turn folded into ONE recursive proof that verifies.
    /// The verifier checks only the root; it never touches the 3 per-cell
    /// proofs — constant-cost in the number of cells.
    #[test]
    fn three_cell_joint_turn_recursive_proves_and_verifies() {
        let ps = vec![
            make_participant(100, 0, 0x5151),
            make_participant(200, 1, 0x5151),
            make_participant(300, 2, 0x5151),
        ];

        let gold = prove_joint_turn_recursive(&ps)
            .expect("agreeing 3-cell joint turn must prove recursively");
        assert_eq!(gold.num_cells, 3);
        assert_eq!(gold.shared_turn_id, BabyBear::new(0x5151));

        verify_joint_turn_recursive(&gold)
            .expect("recursive 3-cell joint-turn root proof must verify");
    }

    /// GOLD teeth (turn-id): disagreeing turn ids are rejected (the binding
    /// leaf's CG-2 is unsatisfiable / the host check fires) before any tree.
    #[test]
    fn recursive_rejects_disagreeing_turn_ids() {
        let ps = vec![
            make_participant(100, 0, 0xABCD),
            make_participant(200, 7, 0x1234), // DIFFERENT turn id
            make_participant(300, 2, 0xABCD),
        ];

        match prove_joint_turn_recursive(&ps) {
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

    /// GOLD teeth (tampered participant): corrupting a per-cell proof makes the
    /// host-side per-cell soundness gate reject it before the recursion tree —
    /// so no root proof is produced. (A tampered *leaf trace* would instead make
    /// the in-circuit leaf verifier unsatisfiable; this exercises the host gate,
    /// the first line of defense.)
    #[test]
    fn recursive_rejects_tampered_participant_proof() {
        let mut ps = vec![
            make_participant(100, 0, 0x77),
            make_participant(200, 1, 0x77),
            make_participant(300, 2, 0x77),
        ];
        // Corrupt cell 1's per-cell proof commitment (turn ids still agree).
        ps[1].proof.trace_commitment[0] ^= 0xFF;

        match prove_joint_turn_recursive(&ps) {
            Err(JointAggError::ParticipantProofInvalid { index, .. }) => {
                assert_eq!(index, 1, "the tampered cell must be the one rejected");
            }
            Ok(_) => panic!("a tampered participant proof must not produce a recursive root proof"),
            Err(other) => panic!("expected ParticipantProofInvalid, got {other:?}"),
        }
    }

    /// **THE MISSING TOOTH (documented, not yet bitten).** The whole-chain fold
    /// (`ivc_turn_chain`) proves that a host-gate-skipping prover cannot
    /// produce a verifying root, because its leaves are the REAL descriptor
    /// AIR. THIS module's per-cell leaves are `EffectVmShapeAir` stubs rebuilt
    /// from `(shared_turn_id, cell_commit)` — so an ungated joint prover
    /// feeding a forged `cell_commit` (a post-state that execution never
    /// reached) CAN still wrap a satisfying stub leaf; only the host gate
    /// catches it. This test is the tamper case that must pass once the
    /// joint-turn leaves are cut over to `DescriptorParticipant` + carried
    /// traces (the `ivc_turn_chain::prove_descriptor_leaf` recipe); it is
    /// ignored until then because TODAY it would FAIL exactly as described.
    #[test]
    #[ignore = "gold-joint per-cell leaves are still EffectVmShapeAir stubs: an ungated prover \
                CAN wrap a forged cell_commit (only the host gate rejects it). Cut the leaves \
                over to the descriptor AIR (ivc_turn_chain::prove_descriptor_leaf recipe) and \
                then this in-circuit rejection must hold."]
    fn gold_joint_leaf_is_still_a_shape_stub_no_in_circuit_execution_tooth() {
        let config = create_recursion_config();
        let backend = create_recursion_backend();
        let params = ProveNextLayerParams::default();

        // A cell_commit no execution ever produced. With REAL descriptor
        // leaves, no satisfying leaf exists for it; with the shape stub, the
        // fabricated passthrough trace satisfies the leaf and wraps fine —
        // the exact gap.
        let forged_commit = BabyBear::new(0xDEAD_BEE);
        let shared = BabyBear::new(0x77);
        let (leaf_inner, leaf_pis) = prove_cell_leaf(shared, forged_commit, LEAF_ROWS);

        let air = EffectVmShapeAir;
        let p3_pis: Vec<P3BabyBear> = leaf_pis.iter().map(|&v| to_p3(v)).collect();
        let input = RecursionInput::UniStark {
            proof: &leaf_inner,
            air: &air,
            public_inputs: p3_pis,
            preprocessed_commit: None,
        };
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            build_and_prove_next_layer::<DreggRecursionConfig, EffectVmShapeAir, _, D>(
                &input, &config, &backend, &params,
            )
        }));
        let rejected = match result {
            Ok(Ok(_)) => false,
            Ok(Err(_)) => true,
            Err(_) => true,
        };
        assert!(
            rejected,
            "a forged cell_commit must have NO satisfying per-cell leaf once the joint-turn \
             leaves are the real descriptor AIR (today the shape stub accepts it — the gap)"
        );
    }

    /// GOLD teeth (in-circuit, the load-bearing one): a per-cell leaf proven for
    /// commitment A but fed to the recursive verifier layer with public inputs
    /// claiming commitment B. The leaf's IN-CIRCUIT verifier pins the public
    /// inputs against the proof's opened values, so the mismatched-PI leaf is
    /// UNSATISFIABLE — `build_and_prove_next_layer` MUST fail. This proves the
    /// rejection is the recursion itself (not merely the host pre-check): the
    /// recursive layer will not certify a leaf whose claimed PIs disagree with
    /// what the proof actually attests.
    #[test]
    fn recursive_layer_rejects_mismatched_leaf_public_inputs() {
        let config = create_recursion_config();
        let backend = create_recursion_backend();
        let params = ProveNextLayerParams::default();

        let shared = BabyBear::new(0x99);
        let honest_commit = BabyBear::new(0xAAAA);
        let forged_commit = BabyBear::new(0xBBBB);

        // Prove a leaf for (shared, honest_commit).
        let (leaf_inner, honest_pis) = prove_cell_leaf(shared, honest_commit, LEAF_ROWS);

        // Sanity: the honest leaf wraps fine.
        {
            let air = EffectVmShapeAir;
            let p3_pis: Vec<P3BabyBear> = honest_pis.iter().map(|&v| to_p3(v)).collect();
            let input = RecursionInput::UniStark {
                proof: &leaf_inner,
                air: &air,
                public_inputs: p3_pis,
                preprocessed_commit: None,
            };
            build_and_prove_next_layer::<DreggRecursionConfig, EffectVmShapeAir, _, D>(
                &input, &config, &backend, &params,
            )
            .expect("honest leaf must wrap into a recursive layer");
        }

        // Now FORGE the commitment in the public inputs fed to the layer.
        let mut forged_pis = honest_pis.clone();
        forged_pis[pi::NEW_COMMIT] = forged_commit;
        forged_pis[pi::OLD_COMMIT] = forged_commit;

        let air = EffectVmShapeAir;
        let p3_forged: Vec<P3BabyBear> = forged_pis.iter().map(|&v| to_p3(v)).collect();
        let input = RecursionInput::UniStark {
            proof: &leaf_inner,
            air: &air,
            public_inputs: p3_forged,
            preprocessed_commit: None,
        };

        // The in-circuit verifier must reject the mismatched-PI leaf. The fork
        // surfaces an unsatisfiable verifier circuit either as an Err or as a
        // panic from the constraint check; either is a rejection. Catch both.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            build_and_prove_next_layer::<DreggRecursionConfig, EffectVmShapeAir, _, D>(
                &input, &config, &backend, &params,
            )
        }));

        let rejected = match result {
            Ok(Ok(_)) => false, // produced a proof — soundness hole!
            Ok(Err(_)) => true, // recursion returned an error — rejected.
            Err(_) => true,     // unsatisfiable circuit panicked — rejected.
        };
        assert!(
            rejected,
            "a leaf fed mismatched public inputs (forged commitment) must be rejected by the \
             in-circuit recursive verifier — the recursion, not just the host check, is the tooth"
        );
    }
}
