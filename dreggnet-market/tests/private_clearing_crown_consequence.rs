//! A private Dark Bazaar result changes a real dungeon, not just asset ownership.
//!
//! The fixed N=4,K=4 HidingFRI proof authorizes the existing executor-backed
//! Bazaar clear. A process-local consequence gate then corroborates its receipt
//! against that settled session and lets the proven winner claim the Warden's
//! Keep crown for a deployment-selected faction. Crown ownership is a real
//! WriteOnce game field, and the claim is one real cap-bounded executor turn.
//!
//! Honest boundary: this uses the existing Tier-1 `private-clearing` producer,
//! which sees the order witness. The consequence gate is not a transferable
//! proof verifier; it requires the live settled market beside the receipt.

#![cfg(feature = "private-clearing")]

use std::cell::{Cell, RefCell};

use dregg_app_framework::TurnReceipt;
use dreggnet_market::private_clearing::{PrivateClearingExpectation, PrivateClearingReceipt};
use dreggnet_market::private_clearing_consequence::{
    PrivateClearingCommittedObservation, PrivateClearingConsequenceDisposition,
    PrivateClearingConsequenceError, PrivateClearingConsequenceGate,
    PrivateClearingConsequenceSource, PrivateClearingConsequenceTag,
};
use dreggnet_market::{DarkBazaarOffering, DarkBazaarSession, TURN_BID, TURN_LIST};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dungeon_on_dregg::{
    KP_CLAIM_BLUE, KP_CLAIM_RED, ROOM_HALL, choice_at, deploy_keep, keep_scene,
};
const SELLER: &str = "descent-player:alice";
const LOW_BIDDER: &str = "bazaar-bidder:bob";
const WINNER: &str = "bazaar-bidder:carol";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CrownFaction {
    Red = 1,
    Blue = 2,
}

impl CrownFaction {
    const fn owner_value(self) -> u64 {
        self as u64
    }
}

fn red_crown_tag() -> PrivateClearingConsequenceTag {
    PrivateClearingConsequenceTag::from_label("wardens-keep/crown/red/v1")
}

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_owned())
}

fn land(
    offering: &DarkBazaarOffering,
    session: &mut DarkBazaarSession,
    turn: &str,
    value: i64,
    who: &str,
) {
    let outcome = offering.advance(session, Action::new(turn, turn, value, true), actor(who));
    assert!(matches!(outcome, Outcome::Landed { .. }), "{outcome:?}");
}

fn privately_settled_market() -> (DarkBazaarSession, PrivateClearingReceipt) {
    let offering = DarkBazaarOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(0xC2_0A_71))
        .expect("Dark Bazaar opens");
    land(&offering, &mut session, TURN_LIST, 1, SELLER);
    land(&offering, &mut session, TURN_BID, 2, LOW_BIDDER);
    land(&offering, &mut session, TURN_BID, 3, WINNER);

    let authorization = session
        .prepare_private_clearing_zk()
        .expect("real HidingFRI private clearing proof");
    let statement = authorization.statement();
    assert_eq!((statement.p_star, statement.v_star), (3, 1));
    let receipt = offering
        .settle_private_verified(
            &mut session,
            authorization,
            PrivateClearingExpectation::from_statement(statement),
        )
        .expect("private proof authorizes authoritative SETTLE");
    (session, receipt)
}

#[test]
fn proven_bazaar_winner_claims_the_writeonce_keep_crown_exactly_once() {
    let (session, receipt) = privately_settled_market();
    assert_eq!(receipt.winner, actor(WINNER));
    assert_eq!(receipt.price(), 3);

    let scene = keep_scene();
    let keep = deploy_keep(0x52);
    let target = keep.cell_id();
    let claim_red = choice_at(&scene, ROOM_HALL, KP_CLAIM_RED);
    let source = PrivateClearingConsequenceSource::from_verified_receipt(&receipt)
        .expect("pin authoritative private settlement output");
    let mut gate = PrivateClearingConsequenceGate::new(target, source.clone(), red_crown_tag());

    // A lookalike receipt with a rewritten public output is refused against the
    // authoritative settled market before the game closure can run.
    let mut wrong_price = receipt.clone();
    wrong_price.statement.p_star = 2;
    let forged_ran = Cell::new(false);
    let forged = gate
        .apply_game_turn(&session, &wrong_price, target, || {
            forged_ran.set(true);
            unreachable!("a mismatched receipt cannot reach the dungeon")
        })
        .expect_err("rewritten private output is refused");
    assert!(matches!(
        forged,
        PrivateClearingConsequenceError::ReceiptMismatch(
            "receipt differs from pinned verified source"
        )
    ));
    assert!(!forged_ran.get());
    assert_eq!(gate.consumed_count(), 0);
    assert_eq!(keep.read_var("relic_owner"), 0);

    // Root and settlement-turn substitutions are also pinned. Without these
    // checks either field could be changed to derive a fresh replay id.
    let tampered_ran = Cell::new(false);
    let mut wrong_root = receipt.clone();
    wrong_root.statement.order_root[0] ^= 1;
    let root_error = gate
        .apply_game_turn(&session, &wrong_root, target, || {
            tampered_ran.set(true);
            unreachable!("a substituted root cannot reach the dungeon")
        })
        .expect_err("substituted private root is refused");
    assert!(matches!(
        root_error,
        PrivateClearingConsequenceError::ReceiptMismatch(
            "receipt differs from pinned verified source"
        )
    ));
    let mut wrong_settlement_turn = receipt.clone();
    wrong_settlement_turn.settlement_turn.turn_hash[0] ^= 1;
    let turn_error = gate
        .apply_game_turn(&session, &wrong_settlement_turn, target, || {
            tampered_ran.set(true);
            unreachable!("a substituted settlement turn cannot reach the dungeon")
        })
        .expect_err("substituted settlement turn is refused");
    assert!(matches!(
        turn_error,
        PrivateClearingConsequenceError::ReceiptMismatch(
            "receipt differs from pinned verified source"
        )
    ));
    assert!(!tampered_ran.get());
    assert_eq!(gate.consumed_count(), 0);

    // A valid result cannot be redirected to another deterministic game cell.
    let other_keep = deploy_keep(0x53);
    let redirected_ran = Cell::new(false);
    let redirected = gate
        .apply_game_turn(&session, &receipt, other_keep.cell_id(), || {
            redirected_ran.set(true);
            unreachable!("a target mismatch cannot reach the dungeon")
        })
        .expect_err("wrong game target is refused");
    assert_eq!(redirected, PrivateClearingConsequenceError::TargetMismatch);
    assert!(!redirected_ran.get());
    assert_eq!(gate.consumed_count(), 0);

    // A caller cannot satisfy the production gate with a made-up non-turn.
    let fake = gate
        .apply_game_turn(&session, &receipt, target, || Ok(TurnReceipt::default()))
        .expect_err("a zero/default receipt is not a committed game transition");
    assert_eq!(
        fake,
        PrivateClearingConsequenceError::InvalidGameTurn("zero turn hash")
    );
    assert_eq!(gate.consumed_count(), 0);
    assert_eq!(keep.read_var("relic_owner"), 0);

    // The valid private result fires exactly one real WriteOnce crown turn.
    let consequence = gate
        .apply_game_turn(&session, &receipt, target, || {
            keep.apply_choice(ROOM_HALL, KP_CLAIM_RED, &claim_red)
                .map_err(|error| error.to_string())
        })
        .expect("proven winner claims the Keep crown");
    assert_eq!(
        keep.read_var("relic_owner"),
        CrownFaction::Red.owner_value()
    );
    assert_eq!(consequence.winner, actor(WINNER));
    assert_eq!(consequence.price, 3);
    assert_eq!(consequence.target_cell, target);
    assert_eq!(consequence.consequence_tag, red_crown_tag());
    assert_eq!(
        consequence.settlement_turn_hash,
        receipt.settlement_turn.turn_hash
    );
    assert_ne!(consequence.game_turn_hash, [0; 32]);
    assert_eq!(
        consequence.disposition,
        PrivateClearingConsequenceDisposition::Committed
    );
    assert_eq!(gate.consumed_count(), 1);

    // Replay is refused by the consequence gate before a second game turn runs.
    let replay_ran = Cell::new(false);
    let replay = gate
        .apply_game_turn(&session, &receipt, target, || {
            replay_ran.set(true);
            unreachable!("consumed result cannot reach the dungeon twice")
        })
        .expect_err("consequence replay is refused");
    assert_eq!(replay, PrivateClearingConsequenceError::AlreadyConsumed);
    assert!(!replay_ran.get());
    assert_eq!(
        keep.read_var("relic_owner"),
        CrownFaction::Red.owner_value()
    );

    // A reconstructed gate restores the committed id and refuses the same
    // private result before dispatch, which is the durable-host restart seam.
    let mut restored = PrivateClearingConsequenceGate::new(target, source.clone(), red_crown_tag());
    restored.restore_consumed([consequence.consequence_id]);
    assert_eq!(
        restored.consumed_ids().copied().collect::<Vec<_>>(),
        vec![consequence.consequence_id]
    );
    let restored_ran = Cell::new(false);
    let restored_replay = restored
        .apply_game_turn(&session, &receipt, target, || {
            restored_ran.set(true);
            unreachable!("restored replay state refuses before game dispatch")
        })
        .expect_err("restored consequence id stays consumed");
    assert_eq!(
        restored_replay,
        PrivateClearingConsequenceError::AlreadyConsumed
    );
    assert!(!restored_ran.get());

    // Separately, if the real game rule refuses (Blue already owns this crown),
    // the result is not consumed and the committed game state does not ghost-change.
    let blocked = deploy_keep(0x54);
    let blocked_scene = keep_scene();
    let claim_blue = choice_at(&blocked_scene, ROOM_HALL, KP_CLAIM_BLUE);
    blocked
        .apply_choice(ROOM_HALL, KP_CLAIM_BLUE, &claim_blue)
        .expect("Blue wins this independent crown first");
    let blocked_target = blocked.cell_id();
    let blocked_claim_red = choice_at(&blocked_scene, ROOM_HALL, KP_CLAIM_RED);
    let mut blocked_gate =
        PrivateClearingConsequenceGate::new(blocked_target, source.clone(), red_crown_tag());
    let refused = blocked_gate
        .apply_game_turn(&session, &receipt, blocked_target, || {
            blocked
                .apply_choice(ROOM_HALL, KP_CLAIM_RED, &blocked_claim_red)
                .map_err(|error| error.to_string())
        })
        .expect_err("the Keep's WriteOnce tooth remains authoritative");
    assert!(matches!(
        refused,
        PrivateClearingConsequenceError::GameRefused(_)
    ));
    assert_eq!(blocked_gate.consumed_count(), 0);
    assert_eq!(
        blocked.read_var("relic_owner"),
        CrownFaction::Blue.owner_value(),
        "executor refusal preserves the prior crown owner"
    );

    // CRASH WINDOW: the target executor commits Red's claim, then the process
    // dies before the consequence replay sidecar advances. The first gate reports
    // the interruption and retains no consumed id.
    let crash_keep = deploy_keep(0x55);
    let crash_target = crash_keep.cell_id();
    let crash_scene = keep_scene();
    let crash_claim_red = choice_at(&crash_scene, ROOM_HALL, KP_CLAIM_RED);
    let observed_commit = RefCell::new(None::<PrivateClearingCommittedObservation>);
    let mut crash_gate =
        PrivateClearingConsequenceGate::new(crash_target, source.clone(), red_crown_tag());
    let crash = crash_gate
        .apply_game_turn_with_commit_hook(
            &session,
            &receipt,
            crash_target,
            || {
                crash_keep
                    .apply_choice(ROOM_HALL, KP_CLAIM_RED, &crash_claim_red)
                    .map_err(|error| error.to_string())
            },
            |consequence_id, game_receipt| {
                observed_commit.replace(Some(PrivateClearingCommittedObservation::new(
                    consequence_id,
                    crash_target,
                    red_crown_tag(),
                    game_receipt.clone(),
                )));
                Err("simulated process death before replay persistence".to_owned())
            },
        )
        .expect_err("fault injection lands between game commit and replay write");
    assert!(matches!(
        crash,
        PrivateClearingConsequenceError::ReplayCommitInterrupted(_)
    ));
    assert_eq!(crash_gate.consumed_count(), 0);
    assert_eq!(
        crash_keep.read_var("relic_owner"),
        CrownFaction::Red.owner_value(),
        "the target turn really committed before the crash"
    );
    drop(crash_gate);

    // RED recovery: absence of a target observation is explicit and cannot
    // silently mark the private result consumed.
    let mut missing_gate =
        PrivateClearingConsequenceGate::new(crash_target, source.clone(), red_crown_tag());
    let missing = missing_gate
        .recover_committed_game_turn(&session, &receipt, crash_target, |_, _, _| Ok(None))
        .expect_err("recovery requires a target-engine observation");
    assert_eq!(missing, PrivateClearingConsequenceError::RecoveryNotFound);
    assert_eq!(missing_gate.consumed_count(), 0);

    // RED recovery: even a real game receipt cannot be spliced under another
    // consequence id. Routing mismatch is refused without consuming replay.
    let committed = observed_commit
        .borrow()
        .clone()
        .expect("crash hook captured committed target observation");
    let mut wrong_id = committed.consequence_id();
    wrong_id[0] ^= 1;
    let mismatched_observation = PrivateClearingCommittedObservation::new(
        wrong_id,
        committed.target_cell(),
        committed.consequence_tag(),
        committed.game_receipt().clone(),
    );
    let mut mismatched_gate =
        PrivateClearingConsequenceGate::new(crash_target, source.clone(), red_crown_tag());
    let mismatched = mismatched_gate
        .recover_committed_game_turn(&session, &receipt, crash_target, |_, _, _| {
            Ok(Some(mismatched_observation))
        })
        .expect_err("another consequence id cannot claim the committed game receipt");
    assert!(matches!(
        mismatched,
        PrivateClearingConsequenceError::RecoveryObservation(_)
    ));
    assert_eq!(mismatched_gate.consumed_count(), 0);

    // RESTART RECOVERY re-observes BOTH the target-specific committed crown
    // state and its executor receipt. It marks the derived id consumed without
    // dispatching a second crown turn.
    let mut recovered_gate =
        PrivateClearingConsequenceGate::new(crash_target, source, red_crown_tag());
    let recovery_dispatches = Cell::new(0usize);
    let recovered = recovered_gate
        .recover_committed_game_turn(
            &session,
            &receipt,
            crash_target,
            |recovery_id, observed_target, observed_tag| {
                let observation = observed_commit.borrow().clone();
                let committed = observation
                    .as_ref()
                    .expect("committed observation survives");
                assert_eq!(
                    recovery_id,
                    committed.consequence_id(),
                    "recovery names the exact id recorded at game commit"
                );
                assert_eq!(observed_target, crash_target);
                assert_eq!(observed_tag, red_crown_tag());
                assert_eq!(
                    crash_keep.read_var("relic_owner"),
                    CrownFaction::Red.owner_value(),
                    "target-specific recovery predicate"
                );
                Ok(observation)
            },
        )
        .expect("re-observed committed game turn closes crash window");
    assert_eq!(
        recovered.disposition,
        PrivateClearingConsequenceDisposition::Recovered
    );
    assert_eq!(recovered_gate.consumed_count(), 1);
    assert_eq!(recovery_dispatches.get(), 0);

    // RED: after recovery, the normal apply path is replay-refused before its
    // closure can fire. Crown ownership and the game receipt remain singletons.
    let recovered_replay = recovered_gate
        .apply_game_turn(&session, &receipt, crash_target, || {
            recovery_dispatches.set(recovery_dispatches.get() + 1);
            unreachable!("recovery consumed the consequence before redispatch")
        })
        .expect_err("recovered consequence cannot execute twice");
    assert_eq!(
        recovered_replay,
        PrivateClearingConsequenceError::AlreadyConsumed
    );
    assert_eq!(recovery_dispatches.get(), 0);
    assert_eq!(
        crash_keep.read_var("relic_owner"),
        CrownFaction::Red.owner_value()
    );
}
