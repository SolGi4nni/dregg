//! RECURSIVE JOINT-TURN FOLD soundness teeth, on the MANDATORY ROTATED leg.
//!
//! Bucket-F (PATH-PRESERVE Phase 5a): the in-lib `#[cfg(test)]` recursive joint-turn
//! teeth were DELETED when the v1 `DescriptorParticipant::v1(proof, trace)` leg was
//! dropped — the per-cell leaf is now the rotated multi-table `Ir2BatchProof`
//! (`RotatedParticipantLeg`), minted by
//! `dregg_turn::rotation_witness::mint_rotated_participant_leg`. The lib could not host
//! these as integration tests (`circuit/tests/` may depend on `dregg-cell` +
//! `dregg-turn`, which the lib cannot — a dependency cycle — and the rotated mint lives
//! in `dregg-turn`), so the teeth are re-expressed HERE through the rotated mint,
//! preserving the SAME assertions the deleted module made.
//!
//! A joint (cross-cell) turn is N per-cell whole-turn proofs of ONE shared turn id,
//! folded to ONE recursive root. These teeth pin:
//!   - 3 cells AGREEING on the shared turn id fold + verify under the honest anchor,
//!     and RELABELED carried publics / a mismatched anchor are refused;
//!   - cells DISAGREEING on the turn id are refused (`SharedTurnIdMismatch`, CG-2) —
//!     per-cell validity does not make a foreign-turn proof a participant;
//!   - an UNGATED prover that FORGES a cell's rotated commitment cannot obtain a
//!     verifying root (the rotated descriptor leaf is the in-circuit tooth).
//!
//! The fold teeth run a REAL recursion fold (minutes); they are `#[ignore]`. The cheap
//! host-side rejection (`recursive_rejects_disagreeing_turn_ids`) stays runnable in CI.
//!
//! Run the slow ones with:
//!   cargo test -p dregg-circuit --features recursion --test joint_turn_recursive_rotated -- --ignored --nocapture

#![cfg(feature = "prover")]

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::FinalizedTurn;
use dregg_circuit_prove::joint_turn_aggregation::{
    DescriptorParticipant, JointAggError, RotatedParticipantLeg,
};
use dregg_circuit_prove::joint_turn_recursive::{
    JointCell, RecursiveJointTurnProof, prove_joint_turn_recursive,
    prove_joint_turn_recursive_without_host_gate, verify_joint_turn_recursive,
};
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

// A transfer's effect selector, handed to the ungated joint prover per rotated leg.
use dregg_circuit::effect_vm::sel;

// `RecursiveJointTurnProof` is named via the `prove_*` return types only; keep it
// imported for doc clarity without tripping the unused-import lint.
#[allow(unused_imports)]
use dregg_circuit_prove::joint_turn_recursive::RecursiveJointTurnProof as _RecursiveJointTurnProof;

// ============================================================================
// THE CANONICAL ROTATED MINT FIXTURE (copied from `circuit/tests/proof_economics.rs`,
// adapted to mint with a SHARED turn id for joint participants).
//
// A `JointCell` is a `FinalizedTurn` (the type alias). Each cell carries the rotated
// multi-table `Ir2BatchProof` leg, minted with `Some(turn_id)` so the carried
// `TURN_HASH` slot (the aggregator's shared-turn-id projection) is overridden to the
// shared id every participant must agree on.
// ============================================================================

/// OPEN permissions so the rotated producer-witness path admits the actor cell
/// without auth gating (mirrors `rotation_batchstark_leaf_smoke.rs`).
fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// The transfer actor cell at `(balance, nonce)` with open permissions.
fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// Build a REAL per-cell joint participant on the rotated descriptor path: execute a
/// `Transfer` debit of a fixed amount (5), mint the rotated leg with the SHARED turn
/// id written into the `TURN_HASH` slot via `mint_rotated_participant_leg(..,
/// Some(turn_id))` (the descriptor PI prefix covers it, so the proof Fiat–Shamir-binds
/// the turn id), and wrap it as a `JointCell` (= `FinalizedTurn`).
fn make_cell(balance: u64, nonce: u32, turn_id: u32) -> JointCell {
    let amount: u64 = 5;
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        Some(BabyBear::new(turn_id)),
    )
    .expect("rotated transfer leg mints + self-verifies under the shared turn id");
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

// ============================================================================
// THE TEETH
// ============================================================================

/// GOLD: a 3-cell joint turn — REAL rotated descriptor leaves, each the full
/// multi-table `Ir2Air` set re-proven over its own execution trace and verified
/// IN-CIRCUIT by the wrap layer — folded into ONE recursive proof that verifies under
/// its honest VK anchor.
///
/// Piggybacked REFUSED cases (no extra proving): a mismatched VK anchor is refused;
/// relabeled carried publics (`bundle_digest`, `shared_turn_id`) are refused by the
/// claimed-publics attestation.
#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]
fn three_cell_joint_turn_recursive_proves_and_verifies() {
    let cells = vec![
        make_cell(100, 0, 0x5151),
        make_cell(200, 1, 0x5151),
        make_cell(300, 2, 0x5151),
    ];

    let mut gold: RecursiveJointTurnProof = prove_joint_turn_recursive(&cells)
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

/// GOLD teeth (turn-id): disagreeing turn ids are rejected (the host CG-2 check fires)
/// before any tree.
///
/// CHEAP enough for CI: it mints 3 rotated legs, but `SharedTurnIdMismatch` fires in
/// the host CG-2 loop (step 1b of `prove_joint_turn_recursive`) BEFORE any recursion
/// proving. (The leg mints take a few seconds each; kept non-ignored because no FULL
/// fold runs.)
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

/// **THE LEAF TOOTH (host-gate-skipping prover, forged cell_commit).** The per-cell
/// leaves are the REAL rotated descriptor AIR re-proven over each cell's own execution
/// trace. So an UNGATED joint prover — skipping the host-side descriptor admission
/// entirely — that forges a cell's rotated commitment (a post-state that execution
/// never reached) has NO satisfying leaf: the descriptor's Poseidon2 hash sites force
/// the commit cells to be the genuine digests. The fold fails (prover refuses the
/// unsatisfiable trace in debug; self-verify rejects in release) and no verifying root
/// exists — per-cell execution soundness no longer rests on the host gate.
#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]
fn ungated_joint_prover_with_forged_cell_commit_cannot_produce_a_root() {
    // The forged cell FIRST so the fold fails at its leaf before any expensive wrap
    // runs for the honest cell.
    let forged_cell = make_cell(100, 0, 0x77);
    let honest = make_cell(200, 1, 0x77);

    // FORGE the rotated NEW commitment (PI 35 = V1_PI_COUNT + 1) on the cell's leg.
    // Destructure the leg (all fields `pub`), mutate the claimed PI, rebuild — the
    // proof object is unchanged; the lie is purely in the claimed PI the in-circuit
    // verifier pins against the proof.
    const PI_ROTATED_NEW: usize = dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT + 1;
    let DescriptorParticipant { rotated } = forged_cell.participant;
    let RotatedParticipantLeg {
        proof,
        descriptor,
        mut public_inputs,
    } = rotated;
    let lie = public_inputs[PI_ROTATED_NEW] + BabyBear::ONE;
    public_inputs[PI_ROTATED_NEW] = lie;
    let forged_leg = RotatedParticipantLeg {
        proof,
        descriptor,
        public_inputs,
    };
    let forged = FinalizedTurn::new(DescriptorParticipant::rotated(forged_leg));
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
        "a host-gate-skipping joint prover with a forged rotated cell_commit must NOT obtain a \
         root — the rotated descriptor leaf is the in-circuit tooth"
    );
}

// SKIPPED teeth (vs the deleted in-lib module): `recursive_rejects_tampered_participant_proof`
// (host-gate forged-PI rejection — the gated path; subsumed by the ungated leaf tooth above,
// which is strictly stronger) and `recursive_layer_rejects_mismatched_leaf_public_inputs`
// (the in-circuit-wrap variant) are NOT re-expressed. The latter depended on the v1
// `prove_descriptor_leaf` + `RecursionInput::UniStark` + `EffectVmDescriptorAir` wrap, which the
// rotated cutover DELETED (no v1 leaf exists). The in-circuit-wrap rejection for the rotated leaf
// is covered by the lib's own `rotation_batchstark_leaf_smoke.rs` (the rotated native-batch leaf
// folds + self-verifies in-circuit). The surviving forged-commit tooth carries the SAME
// load-bearing content — a forged commitment has no satisfying in-circuit leaf.
