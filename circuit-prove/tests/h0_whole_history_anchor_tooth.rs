//! **H0 — THE WHOLE-HISTORY ANCHOR CLOSURE TOOTH (~15-bit → ~124-bit).**
//!
//! Before the H0 deployed-wide flip, the deployed whole-history light-client fold
//! (`mint_rotated_participant_leg` → `prove_turn_chain_recursive`) broadcast a SINGLE ~31-bit
//! rotated commit felt (PI 42/43) across the eight segment-anchor lanes, so the genesis/final/
//! continuity of an ENTIRE history were bound at a ~15-bit-birthday floor — two distinct cell states
//! that collide on that one felt were INDISTINGUISHABLE to the fold. The flip mints the deployed leaf
//! as the WIDE (8-felt / ~124-bit faithful commit) form: the single-felt rotated roots are RETIRED to
//! zero and the segment anchors (`turn_anchors8` wide branch / `leg_is_wide_anchored`) bind the
//! GENUINE 8-felt `wide_old_root8`/`wide_new_root8`.
//!
//! THE TOOTH (the acceptance gate — prove the catastrophe is closed): two DISTINCT cell states whose
//! single-felt rotated commit COLLIDES (both retired to zero on the deployed wide leg — the OLD
//! 1-felt path equates ALL states) now produce DISTINCT genuine 8-felt anchors, so the whole-history
//! fold DISTINGUISHES them. An equivocating chain that the retired 1-felt commit would fold (vacuous
//! `0 == 0` continuity) is now REJECTED at the 8-felt continuity tooth (`ChainBreak`). CI-cheap: the
//! rejection surfaces at the host continuity pre-check, before any recursion proving.

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, TurnChainError, prove_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{DescriptorParticipant, RotatedParticipantLeg};
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

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

/// Mint ONE deployed-default (now WIDE) rotated leg for a `Transfer` DEBIT of `amount` from
/// `(balance, nonce)`. This is the EXACT primitive the whole-history light client mints
/// (`mint_rotated_participant_leg`), so the leg is whatever the deployed path produces.
fn deployed_leg(balance: u64, nonce: u32, amount: u64) -> RotatedParticipantLeg {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &[[1u8; 32], [2u8; 32]],
        None,
    )
    .expect("deployed rotated transfer leg mints + self-verifies (now WIDE)")
}

/// THE TOOTH. Two distinct states collide at the retired single felt but are distinguished at the
/// genuine 8-felt anchor, and an equivocating chain is rejected at the 8-felt continuity tooth.
#[test]
fn h0_wide_anchor_distinguishes_what_the_one_felt_commit_collides() {
    // Two genuinely DIFFERENT cell states.
    let leg_a = deployed_leg(1000, 0, 7); // after ≈ (993, …)
    let leg_b = deployed_leg(2000, 5, 11); // a different state entirely

    // (1) THE OLD 1-FELT PATH COLLIDES. The deployed wide leg RETIRES the single-felt rotated
    //     commit (PI 42/43) to zero — so EVERY state maps to the SAME single felt. The
    //     pre-flip whole-history fold bound continuity/anchors at this one felt: indistinguishable.
    assert_eq!(
        leg_a.old_root(),
        leg_b.old_root(),
        "the retired single-felt rotated OLD commit collides across distinct states (both zero)"
    );
    assert_eq!(
        leg_a.new_root(),
        leg_b.new_root(),
        "the retired single-felt rotated NEW commit collides across distinct states (both zero)"
    );
    assert_eq!(
        leg_a.new_root(),
        BabyBear::new(0),
        "the single felt is RETIRED to zero on the deployed wide leg"
    );

    // (2) THE NEW WIDE PATH DISTINGUISHES. The genuine 8-felt (~124-bit) anchors differ.
    let a_old8 = leg_a
        .wide_old_root8()
        .expect("deployed leg is wide-anchored");
    let a_new8 = leg_a
        .wide_new_root8()
        .expect("deployed leg is wide-anchored");
    let b_old8 = leg_b
        .wide_old_root8()
        .expect("deployed leg is wide-anchored");
    assert_ne!(
        a_old8, b_old8,
        "the GENUINE 8-felt wide anchors distinguish the distinct states the single felt collided"
    );
    assert!(
        a_new8.iter().any(|&x| x != BabyBear::new(0)),
        "the wide anchor is a real ~124-bit commit, not the retired single-felt zero"
    );
    // The eight lanes carry genuine per-lane entropy (not a degenerate broadcast of one felt).
    assert!(
        a_new8.iter().any(|&x| x != a_new8[0]),
        "the wide anchor's eight lanes are genuinely distinct (no single-felt broadcast)"
    );

    // (3) THE EQUIVOCATION IS REJECTED. Build a 2-turn chain whose second turn does NOT continue the
    //     first at the 8-felt anchor (`leg_b.wide_old_root8 != leg_a.wide_new_root8`). Under the
    //     RETIRED single felt the continuity was a vacuous `0 == 0` and this chain would have folded;
    //     under the genuine 8-felt continuity tooth it is caught as a `ChainBreak`.
    assert_ne!(
        b_old8, a_new8,
        "the second turn's wide before-anchor must NOT continue the first's wide after-anchor"
    );
    assert_eq!(
        leg_b.old_root(),
        leg_a.new_root(),
        "...yet under the RETIRED single felt they would have folded (vacuous 0 == 0 continuity)"
    );

    let chain = vec![
        FinalizedTurn::new(DescriptorParticipant::rotated(leg_a)),
        FinalizedTurn::new(DescriptorParticipant::rotated(leg_b)),
    ];
    match prove_turn_chain_recursive(&chain) {
        Err(TurnChainError::ChainBreak { index, .. }) => assert_eq!(
            index, 1,
            "the equivocating chain is REJECTED at the now-8-felt continuity tooth (turn 1)"
        ),
        Ok(_) => panic!(
            "CATASTROPHE NOT CLOSED: an equivocating whole-history fold (8-felt-distinct, \
             1-felt-colliding) was ACCEPTED"
        ),
        Err(other) => panic!("expected ChainBreak at the 8-felt continuity tooth; got {other:?}"),
    }
}

/// The honest CONTINUOUS pair links at the genuine 8-felt anchor — the positive control showing the
/// wide continuity is real (not vacuously satisfied). Cheap: anchor comparison only, no fold.
#[test]
fn h0_honest_continuous_pair_links_at_the_wide_anchor() {
    let leg0 = deployed_leg(1000, 0, 7); // (1000,0) --7--> (993, …)
    let leg1 = deployed_leg(993, 1, 7); // continues turn 0's after-state
    let new8_0 = leg0.wide_new_root8().expect("wide");
    let old8_1 = leg1.wide_old_root8().expect("wide");
    assert_eq!(
        new8_0, old8_1,
        "the honest successor's 8-felt before-anchor IS the predecessor's 8-felt after-anchor"
    );
}
