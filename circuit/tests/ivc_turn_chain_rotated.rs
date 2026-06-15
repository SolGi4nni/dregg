//! WHOLE-CHAIN IVC FOLD soundness teeth, on the MANDATORY ROTATED leg.
//!
//! Bucket-F (PATH-PRESERVE Phase 5a): the in-lib `#[cfg(test)]` whole-chain fold
//! teeth were DELETED when the v1 `DescriptorParticipant::v1(proof, trace)` leg was
//! dropped — the leaf is now the rotated multi-table `Ir2BatchProof`
//! (`RotatedParticipantLeg`), minted by
//! `dregg_turn::rotation_witness::mint_rotated_participant_leg`. The lib crate could
//! not host these teeth as integration tests because `circuit/tests/` can depend on
//! `dregg-cell` + `dregg-turn` (which the lib cannot — a dependency cycle), and the
//! rotated mint lives in `dregg-turn`. So the teeth are re-expressed HERE, through
//! the rotated mint, preserving the SAME assertions the deleted in-lib module made.
//!
//! The fold is the artifact that travels to a light client; these teeth pin its
//! soundness:
//!   - a continuous K-turn chain folds + verifies under its honest VK anchor, and
//!     RELABELED carried publics / a mismatched anchor are refused (the
//!     claimed-publics attestation + VK pin);
//!   - a BROKEN temporal order is refused at the chain check (`ChainBreak`);
//!   - an UNGATED prover that FORGES a rotated post-commit cannot obtain a verifying
//!     root (the rotated descriptor leaf is the in-circuit tooth, not the host gate);
//!   - a FOREIGN circuit's recursive root is refused by the VK pin even though the
//!     bare engine accepts it;
//!   - the 2-step inductive core folds a continuous pair and refuses a discontinuous one.
//!
//! Most teeth run a REAL recursion fold (minutes); they are `#[ignore]`. The cheap
//! host-side rejections (`broken_order_rejected`) stay runnable in CI.
//!
//! Run the slow ones with:
//!   cargo test -p dregg-circuit --features recursion --test ivc_turn_chain_rotated -- --ignored --nocapture

#![cfg(feature = "recursion")]

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::ivc_turn_chain::{
    FinalizedTurn, TurnChainError, WholeChainProof, fold_two_turns, prove_turn_chain_recursive,
    prove_turn_chain_recursive_without_host_gate, verify_turn_chain_recursive,
};
use dregg_circuit::joint_turn_aggregation::{DescriptorParticipant, RotatedParticipantLeg};
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

// A transfer's effect selector (`effect_vm::columns::sel::TRANSFER`), the selector
// the ungated chain prover is handed for each rotated transfer leg.
use dregg_circuit::effect_vm::sel;

// `WholeChainProof` is imported for type clarity even though it is only named via the
// `prove_*` return types; silence the unused-import lint without dropping the doc value.
#[allow(unused_imports)]
use dregg_circuit::ivc_turn_chain::WholeChainProof as _WholeChainProof;

// ============================================================================
// THE CANONICAL ROTATED MINT FIXTURE (copied verbatim from
// `circuit/tests/proof_economics.rs` — the audited Bucket-F mint pattern).
//
// A finalized turn carries the MANDATORY ROTATED leg: the rotated multi-table
// `Ir2BatchProof` minted by `mint_rotated_participant_leg` over before/after actor
// `Cell`s. The chain roots are the ROTATED commitments read off the leg (PI 34/35).
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

/// The transfer actor cell at `(balance, nonce)` with open permissions — the
/// before/after `Cell` the rotated mint runs `rotation_witness::produce` over.
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

/// Build a REAL finalized turn on the rotated descriptor path: execute a `Transfer`
/// DEBIT of `amount` from `(balance, nonce)`, mint the rotated multi-table
/// `Ir2BatchProof` leg via `mint_rotated_participant_leg` (which self-verifies), and
/// carry it as the mandatory leaf. Returns the turn plus its REAL ROTATED
/// `(old_root, new_root)` commitments (PI 34/35) — the genuine Poseidon2 state
/// commitments the rotated generator derives, NOT fabricated values.
fn make_turn(balance: u64, nonce: u32, amount: u64) -> (FinalizedTurn, BabyBear, BabyBear) {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    // The rotated transfer DEBIT keeps the nonce and decreases the balance by
    // `amount`: before/after actor cells at the same nonce, balance - amount.
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let nullifier_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &nullifier_root,
        &receipt_log,
        None,
    )
    .expect("rotated transfer leg mints + self-verifies");
    // Read the ROTATED chain roots off the leg BEFORE it moves into the participant.
    let old_root = leg.old_root();
    let new_root = leg.new_root();
    (
        FinalizedTurn::new(DescriptorParticipant::rotated(leg)),
        old_root,
        new_root,
    )
}

/// Build a continuous chain of `k` real finalized turns: each turn debits `step`
/// from the balance and the next turn starts from the post-state. The rotated
/// trace's welded scalars (balance/nonce/...) come from the v1 sub-trace, which
/// BUMPS the nonce by 1 per non-NoOp (Transfer) effect — so turn i's after-state is
/// `(balance - step, nonce + 1)`. The next turn's before-state must therefore be
/// `(balance - step, nonce + 1)` for the rotated state-commit roots to link
/// (`old_root[i+1] == new_root[i]`): we advance BOTH balance and nonce per turn.
/// Returns the turns + genesis/final.
fn make_chain(
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
    for i in 0..k {
        let (turn, old_root, new_root) = make_turn(balance, nonce, step);
        if i == 0 {
            genesis = old_root;
        } else {
            assert_eq!(old_root, final_root, "real chain must already link");
        }
        final_root = new_root;
        turns.push(turn);
        balance -= step;
        nonce += 1; // the v1 sub-trace bumps the nonce by 1 per Transfer row.
    }
    (turns, genesis, final_root)
}

// ============================================================================
// THE TEETH
// ============================================================================

/// GOLD whole-chain: fold K=3 REAL rotated finalized turns into ONE recursive proof
/// that verifies under its honest VK anchor. Each turn's real ROTATED post-state
/// commitment is the next turn's real pre-state commitment (genesis -> r1 -> r2 ->
/// final). The verifier checks only the root (+ the VK pin and the carried binding
/// attestation).
///
/// Piggybacked REFUSED cases (no extra proving): a mismatched VK anchor is refused,
/// and RELABELED carried publics (final_root / chain_digest / num_turns /
/// genesis_root spliced after the fold) are refused by the claimed-publics
/// attestation — the verify path reads the publics against the carried binding proof
/// instead of trusting bare fields.
#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]
fn k_fold_turn_chain_proves_and_verifies() {
    let (turns, genesis, final_root) = make_chain(1000, 0, 7, 3);
    assert_eq!(turns.len(), 3);

    let mut whole: WholeChainProof = prove_turn_chain_recursive(&turns)
        .expect("a continuous 3-turn rotated finalized chain must fold recursively");
    assert_eq!(whole.num_turns, 3);
    assert_eq!(whole.genesis_root, genesis);
    assert_eq!(whole.final_root, final_root);

    // The trust anchor an honest setup would distribute.
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the whole-chain root proof must verify under its honest anchor");

    // REFUSED: a mismatched VK anchor (the caller pinned a different circuit).
    let mut wrong = vk;
    wrong.0[0] ^= 0xFF;
    match verify_turn_chain_recursive(&whole, &wrong) {
        Err(TurnChainError::VkFingerprintMismatch { .. }) => {}
        other => panic!("a mismatched VK anchor must be refused; got {other:?}"),
    }

    // REFUSED: relabeled final_root (splicing a foreign endpoint onto the artifact).
    let honest_final = whole.final_root;
    whole.final_root = honest_final + BabyBear::ONE;
    match verify_turn_chain_recursive(&whole, &vk) {
        Err(TurnChainError::ClaimedPublicsUnattested { .. }) => {}
        other => panic!("a relabeled final_root must be refused; got {other:?}"),
    }
    whole.final_root = honest_final;

    // REFUSED: relabeled chain_digest (claiming a different ordered history).
    let honest_digest = whole.chain_digest;
    whole.chain_digest = honest_digest + BabyBear::ONE;
    match verify_turn_chain_recursive(&whole, &vk) {
        Err(TurnChainError::ClaimedPublicsUnattested { .. }) => {}
        other => panic!("a relabeled chain_digest must be refused; got {other:?}"),
    }
    whole.chain_digest = honest_digest;

    // REFUSED: relabeled num_turns (the binding proof Fiat–Shamir-binds pv[2]).
    let honest_n = whole.num_turns;
    whole.num_turns = honest_n + 1;
    match verify_turn_chain_recursive(&whole, &vk) {
        Err(TurnChainError::ClaimedPublicsUnattested { .. }) => {}
        other => panic!("a relabeled num_turns must be refused; got {other:?}"),
    }
    whole.num_turns = honest_n;

    // REFUSED: relabeled genesis_root.
    let honest_genesis = whole.genesis_root;
    whole.genesis_root = honest_genesis + BabyBear::ONE;
    match verify_turn_chain_recursive(&whole, &vk) {
        Err(TurnChainError::ClaimedPublicsUnattested { .. }) => {}
        other => panic!("a relabeled genesis_root must be refused; got {other:?}"),
    }
    whole.genesis_root = honest_genesis;

    // And the restored artifact still verifies (the refusals were the lies, not
    // collateral damage).
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the restored honest artifact must verify again");
}

/// TEMPORAL TOOTH (host): a turn whose real ROTATED old_root != previous new_root
/// breaks the finalized order and is rejected at the chain check — before any tree.
/// We splice an out-of-sequence turn (a fresh, unrelated chain's turn, whose rotated
/// pre-state commitment does not match) into the middle.
///
/// CHEAP enough to run in CI: it mints 3 chain legs + 1 foreign leg, but `ChainBreak`
/// fires in `prove_chain_core_rotated`'s host-side continuity check (after the host
/// admission loop) BEFORE any recursion proving begins. (The mints themselves take a
/// few seconds; kept non-ignored because no FULL fold runs.)
#[test]
fn broken_order_rejected() {
    let (mut turns, _g, _f) = make_chain(1000, 0, 7, 3);
    // Replace turn 1 with a turn from an UNRELATED chain (different starting balance),
    // so its real rotated old_root does not continue turn 0's new_root.
    let (foreign, foreign_old, _foreign_new) = make_turn(500, 50, 3);
    let prev_new = turns[0].new_root();
    assert_ne!(
        foreign_old, prev_new,
        "the foreign turn must NOT continue the chain (that is the point)"
    );
    turns[1] = foreign;

    match prove_turn_chain_recursive(&turns) {
        Err(TurnChainError::ChainBreak {
            index,
            expected_old_root,
            found_old_root,
        }) => {
            assert_eq!(index, 1);
            assert_eq!(expected_old_root, prev_new.0);
            assert_eq!(found_old_root, foreign_old.0);
        }
        Ok(_) => panic!("a broken finalized order must not produce a whole-chain proof"),
        Err(other) => panic!("expected ChainBreak, got {other:?}"),
    }
}

/// **THE LEAF TOOTH (host-gate-skipping prover, forged post-commit).** The claim is
/// that per-turn execution soundness does NOT rest on the prover having run the
/// host-side descriptor admission. So: run the UNGATED prover on a chain whose second
/// turn LIES about its rotated post-state root in the PIs (the execution witness is
/// honest; only the claimed rotated `NEW_COMMIT` at PI 35 is forged — exactly the lie
/// a malicious prover tells to advance the chain to a state that never happened). The
/// rotated descriptor AIR's PI binding + Poseidon2 state-commit hash sites make that
/// leaf UNSATISFIABLE, so the in-circuit re-proof fails and NO verifying root can be
/// produced — the host gate was never load-bearing.
///
/// We assert BOTH:
///   (a) the GATED prover rejects at host admission — the forged rotated PI no longer
///       verifies the production descriptor proof (`verify_descriptor_participant`
///       re-verifies the WHOLE 38-PI vector). The host runs admission BEFORE the
///       continuity check, so `TurnProofInvalid { index: 1 }` fires first; we accept
///       EITHER `TurnProofInvalid` OR `ChainBreak` at index 1 to stay robust to the
///       order in which the host reads roots vs re-verifies proofs.
///   (b) the UNGATED prover (which never runs the host gate) ALSO fails, at the
///       in-circuit leaf (catch_unwind: rejected if Err or panic).
#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]
fn ungated_prover_with_forged_post_commit_cannot_produce_a_root() {
    // The v1 sub-trace bumps the nonce by 1 per Transfer, so turn 0's after-state is (993, 1);
    // turn 1's before-state must be (993, 1) for the rotated roots to chain.
    let (t0, _o0, n0) = make_turn(1000, 0, 7);
    let (t1, o1, n1) = make_turn(993, 1, 7);
    assert_eq!(o1, n0, "honest rotated turns chain by construction");

    // FORGE the rotated NEW commitment (PI 35 = V1_PI_COUNT + 1) on turn 1's leg.
    // The leg's `proof`/`descriptor`/`public_inputs` are all `pub`, so we destructure
    // the participant, mutate the PI vector, and rebuild the leg — the proof object is
    // unchanged (the lie is purely in the claimed PI, which the in-circuit verifier
    // pins against the proof).
    const PI_ROTATED_NEW: usize = dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT + 1;
    let DescriptorParticipant { rotated } = t1.participant;
    let RotatedParticipantLeg {
        proof,
        descriptor,
        mut public_inputs,
    } = rotated;
    let lie = n1 + BabyBear::ONE;
    public_inputs[PI_ROTATED_NEW] = lie;
    let forged_leg = RotatedParticipantLeg {
        proof,
        descriptor,
        public_inputs,
    };
    let t1_forged = FinalizedTurn::new(DescriptorParticipant::rotated(forged_leg));
    let turns = [t0, t1_forged];

    // (a) The GATED prover rejects at host admission (the forged PI no longer verifies
    //     the production rotated descriptor proof). Accept TurnProofInvalid (host
    //     re-verify) OR ChainBreak (continuity) at index 1.
    match prove_turn_chain_recursive(&turns) {
        Err(TurnChainError::TurnProofInvalid { index, .. }) => assert_eq!(index, 1),
        Err(TurnChainError::ChainBreak { index, .. }) => assert_eq!(index, 1),
        Ok(_) => panic!("the gated prover accepted a forged rotated post-commit"),
        Err(other) => {
            panic!("expected TurnProofInvalid or ChainBreak at index 1, got {other:?}")
        }
    }

    // (b) THE TOOTH: the UNGATED prover — which never runs the host gate — must ALSO
    //     fail, at the in-circuit leaf. The unsatisfiable leaf surfaces as a prover
    //     panic (debug: check_constraints refuses) or an Err (release: self-verify
    //     rejects). Either is "no root".
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_turn_chain_recursive_without_host_gate(&turns, &[sel::TRANSFER, sel::TRANSFER])
    }));
    let rejected = match result {
        Ok(Ok(_)) => false, // a verifying root for a forged turn — soundness hole!
        Ok(Err(_)) => true,
        Err(_) => true,
    };
    assert!(
        rejected,
        "a host-gate-skipping prover with a forged rotated post-commit must NOT obtain a \
         whole-chain root — the rotated descriptor leaf is the in-circuit tooth"
    );
}

/// **THE VK-PIN TOOTH (from-scratch prover, REFUSED).** `verify_recursive_batch_proof`
/// reconstructs circuit common data FROM the proof, so ANY valid recursive proof —
/// here a wrap of the unrelated `AggregationAir` — passes the bare root check. The
/// pinned verifier must refuse it: its verifier-key fingerprint is not the chain
/// fold's. Both halves are asserted: the bare engine ACCEPTS the foreign root (the pin
/// is load-bearing), and `verify_turn_chain_recursive` REFUSES it with
/// `VkFingerprintMismatch`.
#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]
fn foreign_circuit_root_is_refused_by_vk_pin() {
    use dregg_circuit::plonky3_recursion::AggregationAir;
    use dregg_circuit::plonky3_recursion_impl::recursive::{
        prove_inner_for_air, prove_recursive_layer_for_air, verify_recursive_batch_proof,
    };
    use p3_baby_bear::BabyBear as P3BabyBear;
    use p3_field::PrimeCharacteristicRing;
    use p3_matrix::dense::RowMajorMatrix;

    // An honest K=2 fold (the artifact whose carried publics + binding proof the
    // attacker will try to pair with a foreign root).
    let (turns, _g, _f) = make_chain(1000, 0, 7, 2);
    let mut whole = prove_turn_chain_recursive(&turns).expect("the honest 2-turn chain must fold");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk).expect("honest artifact verifies");

    // A from-scratch prover's root: a perfectly VALID recursive proof — of a DIFFERENT
    // circuit (the AggregationAir smoke wrap).
    let foreign = {
        let pv1 = P3BabyBear::from_u64(0xC0FFEE);
        let rows: Vec<P3BabyBear> = vec![
            P3BabyBear::ZERO,
            P3BabyBear::from_u64(1),
            P3BabyBear::from_u64(2),
            P3BabyBear::from_u64(10),
            P3BabyBear::from_u64(10),
            P3BabyBear::from_u64(3),
            P3BabyBear::from_u64(4),
            P3BabyBear::from_u64(20),
            P3BabyBear::from_u64(20),
            P3BabyBear::from_u64(5),
            P3BabyBear::from_u64(6),
            P3BabyBear::from_u64(30),
            P3BabyBear::from_u64(30),
            P3BabyBear::from_u64(7),
            P3BabyBear::from_u64(8),
            pv1,
        ];
        let matrix = RowMajorMatrix::new(rows, 4);
        let pis = vec![BabyBear::ZERO, BabyBear::new(0xC0FFEE)];
        let air = AggregationAir;
        let inner = prove_inner_for_air(&air, matrix, &pis);
        prove_recursive_layer_for_air(&air, &inner, &pis)
            .expect("the foreign AIR wraps fine — it is a VALID recursive proof")
    };

    // The bare engine check ACCEPTS the foreign root — the exact reason the pin exists.
    verify_recursive_batch_proof(&foreign.0)
        .expect("the bare engine accepts ANY valid recursive proof — the pre-pin hole");

    // Splice the foreign root under the honest carried publics/binding.
    whole.root = foreign;
    match verify_turn_chain_recursive(&whole, &vk) {
        Err(TurnChainError::VkFingerprintMismatch { .. }) => {}
        Ok(()) => panic!("a foreign circuit's root must NOT verify as the chain fold"),
        Err(other) => panic!("expected VkFingerprintMismatch, got {other:?}"),
    }
}

/// 2-step inductive core: `fold_two_turns` over a continuous pair yields a verifying
/// whole-chain proof of the 2-turn window (the unbounded loop's inductive step).
#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]
fn two_step_inductive_core_proves_and_verifies() {
    let (turns, genesis, final_root) = make_chain(1000, 0, 11, 2);

    let folded =
        fold_two_turns(&turns[0], &turns[1]).expect("a continuous pair must fold via the core");
    assert_eq!(folded.num_turns, 2);
    assert_eq!(folded.genesis_root, genesis);
    assert_eq!(folded.final_root, final_root);
    let vk = folded.root_vk_fingerprint();
    verify_turn_chain_recursive(&folded, &vk).expect("the 2-step folded proof must verify");
}

/// `fold_two_turns` rejects a discontinuous pair (the inductive step refuses to extend
/// the running chain with a turn that does not consume its root).
///
/// CHEAP: the host-side `ChainBreak` fires before any recursion proving (only two leg
/// mints; no full fold), so this stays runnable in CI.
#[test]
fn two_step_core_rejects_discontinuity() {
    let (running, _o, _n) = make_turn(1000, 0, 11);
    let (bad_next, _bo, _bn) = make_turn(500, 50, 3); // unrelated chain

    match fold_two_turns(&running, &bad_next) {
        Err(TurnChainError::ChainBreak { index, .. }) => assert_eq!(index, 1),
        Ok(_) => panic!("a discontinuous pair must not fold"),
        Err(other) => panic!("expected ChainBreak, got {other:?}"),
    }
}

// SKIPPED tooth (vs the deleted in-lib module): `broken_order_unsat_in_circuit`,
// `ungated_prover_with_stub_leaf_cannot_produce_a_root`, and
// `recursive_layer_rejects_forged_leaf_public_inputs` are NOT re-expressed here.
// They depended on lib-internal items that are NOT publicly exported for an
// integration test — `generate_chain_trace_unchecked` / `TurnChainBindingAir` /
// `trace_to_matrix` / `verify_inner_for_air` (the in-circuit binding-trace tooth), and
// the v1 `prove_descriptor_leaf` + `RecursionInput::UniStark` + `EffectVmDescriptorAir`
// wrap (which the rotated cutover DELETED — the v1 leaf no longer exists). The
// surviving forged-PI tooth (`ungated_prover_with_forged_post_commit_cannot_produce_a_root`,
// above) carries the SAME load-bearing assertion — a forged commitment has no
// satisfying in-circuit leaf — through the rotated path; the in-circuit-wrap variant is
// covered by the lib's own `rotation_batchstark_leaf_smoke.rs`.
