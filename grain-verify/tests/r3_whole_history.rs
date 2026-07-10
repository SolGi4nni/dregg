//! # R3 end-to-end — a grain's whole history, unfoolable, decided by the Lean verifier.
//!
//! Drives [`grain_verify::r3_verify`] over a SMALL real rotated finalized-turn chain
//! (mirroring `lightclient/src/bin/whole_history_demo.rs`): the fold is the expensive
//! recursive-STARK step (~minutes even at K=2), so the whole test is `#[ignore]`'d —
//! run it with `cargo test -p grain-verify --test r3_whole_history -- --ignored`.
//!
//! Three poles, each biting a distinct way, and in EVERY case the ACCEPT decision is
//! the Lean-proven `Dregg2.Grain.R3Verify.r3VerifyCore` (`shadow_grain_r3_verify`),
//! never Rust:
//!   (i)   HONEST — a genuine chain folded, anchored at its GENUINE head → the Lean
//!         verifier returns `"1"` → `R3Verified` (no host trust in the decision).
//!   (ii)  WRONG-HEAD — the same genuine chain anchored at head+1 → the Lean verifier
//!         returns `"0"` (the anti-ghost head tooth) → `R3Error::Rejected`.
//!   (iii) FABRICATION — a chain whose last turn's post-state PI is forged → the fold
//!         does not verify → verified-status false → the Lean verifier rejects.

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::FinalizedTurn;
use dregg_circuit_prove::joint_turn_aggregation::{DescriptorParticipant, RotatedParticipantLeg};
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

use grain_verify::{R3Error, r3_verify};

// ── The canonical rotated mint fixture (copied from whole_history_demo). ──────────────

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

/// ONE real finalized turn on the production descriptor path (mandatory rotated leg).
/// Returns the turn + its REAL rotated `(old_root, new_root)` head-lane commitments.
fn make_turn(balance: u64, nonce: u32, amount: u64) -> (FinalizedTurn, BabyBear, BabyBear) {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        None,
    )
    .expect("rotated transfer leg mints + self-verifies");
    let old_root = leg.wide_old_root8().expect("deployed leg is wide-anchored")[0];
    let new_root = leg.wide_new_root8().expect("deployed leg is wide-anchored")[0];
    (
        FinalizedTurn::new(DescriptorParticipant::rotated(leg)),
        old_root,
        new_root,
    )
}

/// A continuous chain of `k` real finalized turns (each debits `step`, the next starts
/// from the post-state). Returns the turns + genesis/final head-lane roots.
fn make_chain(
    start_balance: u64,
    start_nonce: u32,
    step: u64,
    k: usize,
) -> (Vec<FinalizedTurn>, BabyBear, BabyBear) {
    let mut turns = Vec::with_capacity(k);
    let mut balance = start_balance;
    let mut genesis = BabyBear::ZERO;
    let mut final_root = BabyBear::ZERO;
    for i in 0..k {
        let nonce = start_nonce + i as u32;
        let (turn, old_root, new_root) = make_turn(balance, nonce, step);
        if i == 0 {
            genesis = old_root;
        } else {
            assert_eq!(
                old_root, final_root,
                "real chain: turn {i} continues the previous"
            );
        }
        final_root = new_root;
        turns.push(turn);
        balance -= step;
    }
    (turns, genesis, final_root)
}

/// Forge the LAST turn's claimed post-state (the genuine 8-felt wide AFTER-commit PI):
/// the execution witness is honest, only the CLAIM is forged, so the leaf re-verify is
/// UNSAT and the fold does not verify. Mirrors whole_history_demo case (A).
fn forge_last_post_state(mut chain: Vec<FinalizedTurn>) -> Vec<FinalizedTurn> {
    let last = chain.len() - 1;
    let DescriptorParticipant { rotated } = chain.remove(last).participant;
    let RotatedParticipantLeg {
        proof,
        descriptor,
        mut public_inputs,
        carrier_witness,
    } = rotated;
    let pi_wide_new = public_inputs.len() - 8;
    public_inputs[pi_wide_new] = public_inputs[pi_wide_new] + BabyBear::ONE;
    chain.push(FinalizedTurn::new(DescriptorParticipant::rotated(
        RotatedParticipantLeg {
            proof,
            descriptor,
            public_inputs,
            carrier_witness,
        },
    )));
    chain
}

// ── THE R3 END-TO-END TEST (SLOW: real recursion folds; #[ignore]'d). ─────────────────

#[test]
#[ignore = "SLOW: real recursion folds (~minutes each, 3 folds); run with --ignored"]
fn r3_whole_history_unfoolable_decided_by_lean() {
    // The DECISION is the Lean-proven verifier: without the extracted core in the linked
    // archive there is NO Rust fallback (by design). If it is absent, the archive needs a
    // rebuild that splices `Dregg2.Grain.R3Verify` — report and stop rather than assert a
    // Rust decision we deliberately do not have.
    if !dregg_lean_ffi::grain_r3_verify_core_available() {
        eprintln!(
            "R3: the Lean-proven core `dregg_grain_r3_verify` is not in the linked archive — \
             rebuild dregg-lean-ffi to splice Dregg2.Grain.R3Verify, then re-run. \
             (No Rust fallback for the R3 accept decision by design.)"
        );
        return;
    }

    // A small genuine chain (K = 2 — the minimum non-trivial recursion tree).
    let (turns, _genesis, final_root) = make_chain(1_000, 0, 7, 2);
    let genuine_head = final_root.as_u32();

    // (i) HONEST — anchored at the GENUINE head → the Lean verifier returns "1".
    let t0 = std::time::Instant::now();
    let v = r3_verify(&turns, genuine_head).expect("a genuine whole history R3-verifies");
    let honest_fold = t0.elapsed();
    assert_eq!(v.num_turns, 2);
    assert_eq!(v.anchored_head, genuine_head);
    assert_eq!(
        v.aggregate_head, genuine_head,
        "the aggregate's committed head IS the genuine fold head (head-binding holds)"
    );

    // (ii) WRONG-HEAD — the SAME genuine chain anchored at head+1 → the Lean anti-ghost
    // head tooth rejects (aggregate verified true, but the head does not bind).
    let t1 = std::time::Instant::now();
    let wrong = r3_verify(&turns, genuine_head.wrapping_add(1));
    let wrong_fold = t1.elapsed();
    match wrong {
        Err(R3Error::Rejected {
            aggregate_verified,
            anchored_head,
            ..
        }) => {
            assert!(
                aggregate_verified,
                "the aggregate itself DID verify — only the foreign anchor is rejected"
            );
            assert_eq!(anchored_head, genuine_head.wrapping_add(1));
        }
        other => panic!("a foreign anchor must be Lean-REJECTED; got {other:?}"),
    }

    // (iii) FABRICATION — a chain whose last turn's post-state is forged → the fold does
    // not verify → verified-status false → the Lean verifier rejects. Anchor at the
    // (honest) head so ONLY the verified-status differs.
    let forged = forge_last_post_state(make_chain(1_000, 0, 7, 2).0);
    let t2 = std::time::Instant::now();
    let fab = r3_verify(&forged, genuine_head);
    let fab_fold = t2.elapsed();
    match fab {
        Err(R3Error::Rejected {
            aggregate_verified, ..
        }) => assert!(
            !aggregate_verified,
            "a forged history's aggregate must NOT verify — verified-status is false"
        ),
        other => panic!("a fabricated history must be R3-REJECTED; got {other:?}"),
    }

    eprintln!(
        "R3 folds (K=2): honest {honest_fold:?}, wrong-head {wrong_fold:?}, fabrication {fab_fold:?} \
         — all three ACCEPT decisions rendered by the Lean-proven r3VerifyCore."
    );
}
