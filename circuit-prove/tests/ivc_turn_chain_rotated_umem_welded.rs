//! WHOLE-CHAIN IVC FOLD over the WELDED ROTATED+UMEM leg (STAGED, VK-RISK-FREE) — the IVC half of
//! the flag-day weld, the last precursor before the gated VK epoch.
//!
//! The sibling `ivc_turn_chain_rotated.rs` folds a multi-turn history through the DEPLOYED rotated
//! leg. THIS file proves the same fold runs through the WELDED rotated+umem leg
//! (`mint_welded_umem_rotated_participant_leg` → `RotatedParticipantLeg::mint_welded_from_block_witnesses`):
//! each finalized turn carries ONE leaf that proves BOTH the rotated cohort semantics AND the
//! universal-memory reconciliation (the cohort `umemOp` over 7 appended columns + the real
//! `UMemBoundaryWitness`), and the chain fold reads the SAME rotated `old_root`/`new_root` (PI
//! 34/35 — intact through the weld) it always did. That intactness is exactly what resolves the
//! 0-PI cohort leg's IVC incompatibility (the cohort form carried no PIs for the fold to chain).
//!
//! - `welded_umem_chain_folds_host` — a continuous 3-turn welded history folds (continuity tooth +
//!   ordered-history digest) through `fold_welded_umem_turn_chain_staged`. CI-runnable (no
//!   recursion aggregation; the welded legs mint under the leaf-wrap config).
//! - `welded_umem_broken_order_rejected` — a spliced out-of-order welded turn is refused at the
//!   continuity tooth (`ChainBreak`). CI-runnable.
//! - `welded_umem_chain_folds_recursive` — the full in-circuit recursion fold over the welded
//!   leaves (`prove_welded_umem_turn_chain_recursive_staged`), `#[ignore]` (minutes).

use dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT;
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, TurnChainError, fold_welded_umem_turn_chain_staged,
    prove_welded_umem_turn_chain_recursive_staged, verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_turn_prover::rotation_witness::mint_welded_umem_rotated_participant_leg;

/// OPEN permissions so the rotated producer-witness path admits the actor cell without auth gating.
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

/// Build a REAL finalized turn on the WELDED rotated+umem path: a `Transfer` DEBIT of `amount`
/// from `(balance, nonce)`. The pre→post Balance change IS the turn's single-domain universal-
/// memory touch the weld reconciles. Returns the turn + its rotated `(old_root, new_root)`.
fn make_welded_turn(balance: u64, nonce: u32, amount: u64) -> (FinalizedTurn, BabyBear, BabyBear) {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let leg = mint_welded_umem_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &[[1u8; 32], [2u8; 32]],
        None,
    )
    .expect("welded rotated+umem transfer leg mints + self-verifies");
    // ⚑ THIS LEG IS NARROW, AND SAYING OTHERWISE READ TWO UNRELATED PIs AS AN ANCHOR.
    // `mint_welded_umem_rotated_participant_leg` welds the umem leg onto the ROTATED member out of
    // `V3_STAGED_REGISTRY_TSV` (50 PIs on the deployed transfer) — the WIDE twin is
    // `mint_welded_wide_umem_rotated_participant_leg`, and only IT publishes the 16-felt anchor
    // tail. The lines here read `wide_old_root8()` / `wide_new_root8()`, which used to answer
    // `Some(...)` for any leg with >= 16 PIs, so this chained PI 34 against PI 42: measured
    // 2026-07-29 as `left: BB(0), right: BB(301152428)` on all three tests. The accessors REFUSE a
    // narrow leg now, and the chain rides the rotated commits the welded fold actually binds
    // (`turn_anchors8` broadcasts exactly these across the eight lanes for a narrow leg).
    let old_root = leg.old_root();
    let new_root = leg.new_root();
    (
        FinalizedTurn::new(DescriptorParticipant::rotated(leg)),
        old_root,
        new_root,
    )
}

/// A continuous chain of `k` welded turns (each debits `step`, advancing balance + nonce so the
/// rotated state-commit roots link `old_root[i+1] == new_root[i]`).
fn make_welded_chain(
    start_balance: u64,
    start_nonce: u32,
    step: u64,
    k: usize,
) -> (Vec<FinalizedTurn>, BabyBear, BabyBear) {
    let mut turns = Vec::with_capacity(k);
    let mut balance = start_balance;
    let mut nonce = start_nonce;
    let mut genesis = BabyBear::ZERO;
    let mut final_root = BabyBear::ZERO;
    // `nonce`/`balance` are intertwined chain accumulators here; an enumerate rewrite isn't clean.
    #[allow(clippy::explicit_counter_loop)]
    for i in 0..k {
        let (turn, old_root, new_root) = make_welded_turn(balance, nonce, step);
        if i == 0 {
            genesis = old_root;
        } else {
            assert_eq!(old_root, final_root, "real welded chain must already link");
        }
        final_root = new_root;
        turns.push(turn);
        balance -= step;
        nonce += 1;
    }
    (turns, genesis, final_root)
}

/// THE STAGED WELDED IVC FOLD (HOST): a continuous 3-turn history of WELDED rotated+umem legs folds
/// — the temporal tooth (`prev.new_root == next.old_root`) over the welded legs' rotated roots and
/// the ordered-history digest. This proves the welded leg supplies the IVC's `old_root`/`new_root`
/// accessors (the 0-PI cohort leg could not), so a multi-turn history folds through the rotated+umem
/// form exactly as through the deployed rotated form.
#[test]
fn welded_umem_chain_folds_host() {
    let (turns, genesis, final_root) = make_welded_chain(1000, 0, 7, 3);
    assert_eq!(turns.len(), 3);

    let summary = fold_welded_umem_turn_chain_staged(&turns)
        .expect("a continuous 3-turn welded rotated+umem history must fold (host)");
    assert_eq!(summary.num_turns, 3);
    // The NARROW welded leg publishes no 8-felt anchor tail; the fold broadcasts its rotated
    // commit felt across the eight lanes (`turn_anchors8`), and the accessors REFUSE it — asserted
    // here so a leg that silently became wide-anchored cannot pass this comparison by accident.
    assert!(
        turns[0].participant.rotated.wide_old_root8().is_none(),
        "a welded ROTATED leg is narrow — it must not answer the 8-felt wide anchor accessor"
    );
    let genesis8 = [turns[0].participant.rotated.old_root(); 8];
    let final8 = [turns[turns.len() - 1].participant.rotated.new_root(); 8];
    assert_eq!(summary.genesis_root, genesis8);
    assert_eq!(summary.final_root, final8);
    assert_eq!(
        summary.genesis_root[0], genesis,
        "the head felt matches make_welded_chain's scalar"
    );
    assert_eq!(summary.final_root[0], final_root);
    assert!(
        summary.chain_digest.iter().any(|&x| x != BabyBear::ZERO),
        "the ordered-history digest is a real Poseidon2 commitment"
    );
}

/// TEMPORAL TOOTH (host): a welded turn whose rotated old_root != previous new_root breaks the
/// finalized order and is refused at the continuity check.
#[test]
fn welded_umem_broken_order_rejected() {
    let (mut turns, _g, _f) = make_welded_chain(1000, 0, 7, 3);
    let (foreign, foreign_old, _foreign_new) = make_welded_turn(500, 50, 3);
    // Continuity binds the broadcast rotated commit for a narrow welded leg; compare that felt.
    let prev_new = turns[0].participant.rotated.new_root();
    assert_ne!(
        foreign_old, prev_new,
        "the foreign welded turn must NOT continue the chain"
    );
    turns[1] = foreign;

    match fold_welded_umem_turn_chain_staged(&turns) {
        Err(TurnChainError::ChainBreak {
            index,
            expected_old_root,
            found_old_root,
        }) => {
            assert_eq!(index, 1);
            assert_eq!(expected_old_root, prev_new.0);
            assert_eq!(found_old_root, foreign_old.0);
        }
        Ok(_) => panic!("a broken welded order must not fold"),
        Err(other) => panic!("expected ChainBreak, got {other:?}"),
    }
}

/// THE WELDED-FORM LEAF TOOTH: a welded leg whose claimed rotated post-state commitment (PI 35) is
/// FORGED no longer verifies against its welded descriptor (the after-block `state_commit` pin
/// fails), so the staged fold's host admission refuses it BEFORE any aggregation — the weld does not
/// weaken the rotated post-commit binding.
#[test]
fn welded_umem_forged_post_commit_refused() {
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;

    let (t0, _o0, n0) = make_welded_turn(1000, 0, 7);
    // turn 1's before-state must be (993, 1) for the rotated roots to chain.
    let (t1, o1, n1) = make_welded_turn(993, 1, 7);
    assert_eq!(o1, n0, "honest welded turns chain by construction");

    // FORGE the rotated NEW commitment on the LAST welded leg (so continuity still holds — the
    // forgery is purely the claimed chain head, exactly the lie that would advance the chain to a
    // state that never happened). On this NARROW welded leg the bound carrier IS the single-felt
    // rotated AFTER commit at `V1_PI_COUNT + 1`; the line below forged `len - 8`, which on a 50-PI
    // leg is PI 42 — the BEFORE commit — so the "forged post-commit" arm was tampering with the
    // wrong end of the chain.
    let DescriptorParticipant { rotated } = t1.participant;
    let RotatedParticipantLeg {
        proof,
        descriptor,
        mut public_inputs,
        carrier_witness,
    } = rotated;
    let pi_rot_new = V1_PI_COUNT + 1; // the rotated AFTER state_commit this member pins
    public_inputs[pi_rot_new] = n1 + BabyBear::ONE;
    let forged_leg = RotatedParticipantLeg {
        proof,
        descriptor,
        public_inputs,
        carrier_witness,
    };
    let t1_forged = FinalizedTurn::new(DescriptorParticipant::rotated(forged_leg));
    let turns = [t0, t1_forged];

    match fold_welded_umem_turn_chain_staged(&turns) {
        Err(TurnChainError::TurnProofInvalid { index, .. }) => assert_eq!(index, 1),
        Ok(_) => panic!("a forged welded post-commit must not fold"),
        Err(other) => panic!("expected TurnProofInvalid at index 1, got {other:?}"),
    }
}

/// THE FULL IN-CIRCUIT FOLD: the welded (umem-bearing) descriptor leaves re-verify IN-CIRCUIT and
/// aggregate to ONE whole-chain root that verifies under its honest VK anchor — the genuine
/// end-to-end IVC fold over the rotated+umem form (staged; the only remaining deployment step is the
/// gated VK epoch).
#[test]
#[ignore = "SLOW: real recursion fold over welded leaves (~minutes); run with --ignored"]
fn welded_umem_chain_folds_recursive() {
    let (turns, genesis, final_root) = make_welded_chain(1000, 0, 7, 3);
    let whole = prove_welded_umem_turn_chain_recursive_staged(&turns)
        .expect("a continuous 3-turn welded history must fold recursively");
    assert_eq!(whole.num_turns, 3);
    // The NARROW welded leg publishes no 8-felt anchor tail; the fold broadcasts its rotated
    // commit felt across the eight lanes (`turn_anchors8`), and the accessors REFUSE it — asserted
    // here so a leg that silently became wide-anchored cannot pass this comparison by accident.
    assert!(
        turns[0].participant.rotated.wide_old_root8().is_none(),
        "a welded ROTATED leg is narrow — it must not answer the 8-felt wide anchor accessor"
    );
    let genesis8 = [turns[0].participant.rotated.old_root(); 8];
    let final8 = [turns[turns.len() - 1].participant.rotated.new_root(); 8];
    assert_eq!(whole.genesis_root, genesis8);
    assert_eq!(whole.final_root, final8);
    assert_eq!(
        whole.genesis_root[0], genesis,
        "the head felt matches make_welded_chain's scalar"
    );
    assert_eq!(whole.final_root[0], final_root);
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the welded whole-chain root proof must verify under its honest anchor");
}
