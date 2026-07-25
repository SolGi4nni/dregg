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
use dregg_turn_prover::rotation_witness::mint_rotated_participant_leg;

use dregg_circuit_prove::ivc_turn_chain::RecursionVk;
use grain_verify::{R3Error, r3_setup_anchor, r3_verify};

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
/// Returns the turn + its REAL rotated `(old_root, new_root)` commitments as the FULL
/// 8-felt (~124-bit) wide anchors — `wide_old_root8()` / `wide_new_root8()`, not a lane-0
/// projection of them (wound #22).
fn make_turn(
    balance: u64,
    nonce: u32,
    amount: u64,
) -> (FinalizedTurn, [BabyBear; 8], [BabyBear; 8]) {
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
    let old_root = leg.wide_old_root8().expect("deployed leg is wide-anchored");
    let new_root = leg.wide_new_root8().expect("deployed leg is wide-anchored");
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
) -> (Vec<FinalizedTurn>, [BabyBear; 8], [BabyBear; 8]) {
    let mut turns = Vec::with_capacity(k);
    let mut balance = start_balance;
    let mut genesis = [BabyBear::ZERO; 8];
    let mut final_root = [BabyBear::ZERO; 8];
    for i in 0..k {
        let nonce = start_nonce + i as u32;
        let (turn, old_root, new_root) = make_turn(balance, nonce, step);
        if i == 0 {
            genesis = old_root;
        } else {
            assert_eq!(
                old_root, final_root,
                "real chain: turn {i} continues the previous (all 8 lanes)"
            );
        }
        final_root = new_root;
        turns.push(turn);
        balance -= step;
    }
    (turns, genesis, final_root)
}

/// The 8-felt wide anchor as the canonical `u32` lanes `r3_verify` takes.
fn lanes(w: &[BabyBear; 8]) -> [u32; 8] {
    core::array::from_fn(|i| w[i].as_u32())
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
#[ignore = "SLOW: real recursion folds (~minutes each, 5 folds: 1 honest-setup anchor + 4 poles); run with --ignored"]
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
    let genuine_head = lanes(&final_root);

    // SETUP — the honest party mints its OWN trust anchor from a fold IT produced. This is
    // the `fold_and_attest` role; verifying against the presented proof's own fingerprint
    // (what the pre-fix seam did) establishes nothing (wound #22).
    let ts = std::time::Instant::now();
    let anchor = r3_setup_anchor(&turns).expect("the honest setup fold mints an anchor");
    let setup_fold = ts.elapsed();

    // (i) HONEST — anchored at the GENUINE 8-felt head, under the honest anchor → "1".
    let t0 = std::time::Instant::now();
    let v = r3_verify(&turns, &genuine_head, &anchor).expect("a genuine whole history R3-verifies");
    let honest_fold = t0.elapsed();
    assert_eq!(v.num_turns, 2);
    assert_eq!(v.anchored_head, genuine_head);
    assert_eq!(
        v.aggregate_head, genuine_head,
        "the aggregate's committed 8-felt head IS the genuine fold head, in every lane"
    );

    // (ii) WOUND #22 FALSIFICATION — THE WIDTH TOOTH. The SAME genuine chain anchored at a
    // head that is byte-identical in LANE 0 and differs only at lane 1: exactly the product
    // of the ~2^31 offline grind the wound described. The pre-fix seam compared lane 0 ONLY,
    // so it ACCEPTED this; the widened binding must REJECT it.
    let mut lane1_forged = genuine_head;
    lane1_forged[1] = lane1_forged[1].wrapping_add(1);
    assert_eq!(
        lane1_forged[0], genuine_head[0],
        "the forgery must be INDISTINGUISHABLE to the pre-fix lane-0 seam"
    );
    let t1 = std::time::Instant::now();
    let wrong = r3_verify(&turns, &lane1_forged, &anchor);
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
            assert_eq!(anchored_head, lane1_forged);
        }
        other => panic!(
            "a foreign anchor differing ONLY OUTSIDE LANE 0 must be Lean-REJECTED (wound #22); \
             got {other:?}"
        ),
    }

    // (iii) WOUND #22 FALSIFICATION — THE ANTI-SELF-ANCHOR TOOTH. The SAME genuine chain,
    // the GENUINE head, but a trust anchor that is not the one this fold shape carries. The
    // pre-fix seam read the anchor off the proof, so this input was indistinguishable from
    // the honest one; now it must REJECT.
    let mut swapped = anchor.0;
    swapped[0] ^= 0x01;
    let swapped_vk = RecursionVk(swapped);
    assert_ne!(swapped_vk, anchor, "the swapped anchor must differ");
    let t2 = std::time::Instant::now();
    let foreign = r3_verify(&turns, &genuine_head, &swapped_vk);
    let foreign_fold = t2.elapsed();
    match foreign {
        Err(R3Error::Rejected {
            presented_vk,
            expected_vk,
            ..
        }) => {
            assert_eq!(expected_vk, swapped_vk, "the caller's anchor is reported");
            assert_eq!(
                presented_vk,
                Some(anchor),
                "the fingerprint RECOMPUTED from the presented root is reported as a claim, \
                 and it is NOT the anchor the decision ran against"
            );
        }
        other => panic!(
            "a root whose fingerprint is not the caller's anchor must be Lean-REJECTED \
             (wound #22); got {other:?}"
        ),
    }

    // (iv) FABRICATION — a chain whose last turn's post-state is forged → the fold does
    // not verify → verified-status false → the Lean verifier rejects. Anchor at the
    // (honest) head and anchor so ONLY the verified-status differs.
    let forged = forge_last_post_state(make_chain(1_000, 0, 7, 2).0);
    let t3 = std::time::Instant::now();
    let fab = r3_verify(&forged, &genuine_head, &anchor);
    let fab_fold = t3.elapsed();
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
        "R3 folds (K=2): setup-anchor {setup_fold:?}, honest {honest_fold:?}, \
         lane-1-only forged head {wrong_fold:?}, foreign anchor {foreign_fold:?}, \
         fabrication {fab_fold:?} — every ACCEPT decision rendered by the Lean-proven \
         r3VerifyCore, now binding all 8 anchor lanes and a caller-held VK."
    );
}
