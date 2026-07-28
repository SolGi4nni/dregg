//! A deterministic private-market batch plan reaches one real game turn only
//! when its exact ordered public source image still matches.
//!
//! The three source markets are settled through the production HidingFRI gate.
//! The optimizer sees only their public statements, winners, and committed
//! settlement turns; bid openings and private quantities never enter its API.

#![cfg(feature = "private-clearing")]

/// The verified settlement gate this binary installs before every test — see
/// `tests/support/mod.rs`. Without it `settle_ring_verified` refuses every award as
/// NEVER JUDGED, which is a host-wiring fact about this binary and not a market verdict.
mod support;

use std::cell::Cell;

use dregg_app_framework::TurnReceipt;
use dreggnet_market::private_clearing::batch_optimizer::{
    PrivateBatchConsequenceGate, PrivateBatchConsequenceTag, PrivateBatchOptimizerCertificate,
    PrivateBatchOptimizerError, PrivateBatchSource,
};
use dreggnet_market::private_clearing::{PrivateClearingExpectation, PrivateClearingReceipt};
use dreggnet_market::{DarkBazaarOffering, DarkBazaarSession, TURN_BID, TURN_LIST};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dungeon_on_dregg::{
    KP_CLAIM_BLUE, KP_CLAIM_RED, ROOM_HALL, choice_at, deploy_keep, keep_scene,
};

const SELLER: &str = "descent-player:batch-seller";

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

fn privately_settled_market(
    seed: u64,
    low_bidder: &str,
    winner: &str,
    winning_price: i64,
) -> (DarkBazaarSession, PrivateClearingReceipt) {
    let offering = DarkBazaarOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(seed))
        .expect("Dark Bazaar opens");
    land(&offering, &mut session, TURN_LIST, 1, SELLER);
    land(&offering, &mut session, TURN_BID, 1, low_bidder);
    land(&offering, &mut session, TURN_BID, winning_price, winner);

    let authorization = session
        .prepare_private_clearing_zk()
        .expect("production HidingFRI private clearing proof");
    let statement = authorization.statement();
    assert_eq!(statement.p_star, winning_price as u32);
    assert_eq!(statement.v_star, 1);
    let receipt = offering
        .settle_private_verified(
            &mut session,
            authorization,
            PrivateClearingExpectation::from_statement(statement),
        )
        .expect("private proof authorizes authoritative settlement");
    assert_eq!(receipt.winner, actor(winner));
    (session, receipt)
}

fn allocation_tag() -> PrivateBatchConsequenceTag {
    PrivateBatchConsequenceTag::from_label("wardens-keep/private-batch-allocation/v1")
}

#[test]
fn ordered_private_batch_certificate_is_bound_and_fires_one_real_turn() {
    support::install_verified_settlement_gate();
    let (session0, receipt0) = privately_settled_market(
        0xBA_7C_00,
        "bazaar-bidder:batch-low-0",
        "bazaar-bidder:batch-winner-0",
        2,
    );
    let (session1, receipt1) = privately_settled_market(
        0xBA_7C_01,
        "bazaar-bidder:batch-low-1",
        "bazaar-bidder:batch-winner-1",
        3,
    );
    let (session2, receipt2) = privately_settled_market(
        0xBA_7C_02,
        "bazaar-bidder:batch-low-2",
        "bazaar-bidder:batch-winner-2",
        3,
    );
    let sources = [
        PrivateBatchSource::new(&session0, &receipt0),
        PrivateBatchSource::new(&session1, &receipt1),
        PrivateBatchSource::new(&session2, &receipt2),
    ];

    // Capacity two selects both price-three results. Their tie preserves source
    // order, and the exact objective is checked rather than caller-supplied.
    let certificate = PrivateBatchOptimizerCertificate::issue(&sources, 2)
        .expect("three authoritative private settlements form one batch");
    assert_eq!(certificate.source_count(), 3);
    assert_eq!(certificate.capacity(), 2);
    assert_eq!(certificate.selected_indices(), &[1, 2]);
    assert_eq!(certificate.objective(), 6);
    assert_ne!(certificate.source_root(), [0; 32]);
    assert_ne!(certificate.commitment(), [0; 32]);
    certificate
        .verify(&sources, 2)
        .expect("certificate reproduces from its exact live sources");

    let allocations = certificate
        .allocations(&sources, 2)
        .expect("selected public allocations reproduce");
    assert_eq!(allocations.len(), 2);
    assert_eq!(allocations[0].source_index, 1);
    assert_eq!(allocations[0].private_session, receipt1.statement.session);
    assert_eq!(allocations[0].private_root, receipt1.statement.order_root);
    assert_eq!(allocations[0].winner, receipt1.winner);
    assert_eq!(allocations[0].price, 3);
    assert_eq!(
        allocations[0].settlement_turn_hash,
        receipt1.settlement_turn.turn_hash
    );
    assert_eq!(allocations[1].source_index, 2);
    assert_eq!(allocations[1].private_session, receipt2.statement.session);
    assert_eq!(allocations[1].private_root, receipt2.statement.order_root);
    assert_eq!(allocations[1].winner, receipt2.winner);
    assert_eq!(allocations[1].price, 3);
    assert_eq!(
        allocations[1].settlement_turn_hash,
        receipt2.settlement_turn.turn_hash
    );

    // Neither another ordered batch nor another capacity can inherit this plan.
    let reordered = [sources[2], sources[1], sources[0]];
    assert_eq!(
        certificate.verify(&reordered, 2),
        Err(PrivateBatchOptimizerError::CertificateMismatch)
    );
    assert_eq!(
        certificate.verify(&sources, 1),
        Err(PrivateBatchOptimizerError::CertificateMismatch)
    );
    assert!(matches!(
        PrivateBatchOptimizerCertificate::issue(&[sources[0], sources[0]], 1),
        Err(PrivateBatchOptimizerError::DuplicateSource {
            first: 0,
            second: 1
        })
    ));
    let mut disguised_duplicate_receipt = receipt0.clone();
    disguised_duplicate_receipt.settlement_turn.turn_hash[0] ^= 1;
    assert!(matches!(
        PrivateBatchOptimizerCertificate::issue(
            &[
                sources[0],
                PrivateBatchSource::new(&session0, &disguised_duplicate_receipt),
            ],
            1,
        ),
        Err(PrivateBatchOptimizerError::DuplicateSource {
            first: 0,
            second: 1
        })
    ));

    // Statement/root, source-session, winner, and settlement-turn substitutions
    // all fail before any consequence closure receives the allocations.
    let mut wrong_root_receipt = receipt1.clone();
    wrong_root_receipt.statement.order_root[0] ^= 1;
    let wrong_root_sources = [
        sources[0],
        PrivateBatchSource::new(&session1, &wrong_root_receipt),
        sources[2],
    ];
    assert_eq!(
        certificate.verify(&wrong_root_sources, 2),
        Err(PrivateBatchOptimizerError::CertificateMismatch)
    );

    let mut wrong_rule_receipt = receipt1.clone();
    wrong_rule_receipt.statement.rule ^= 1;
    let wrong_rule_sources = [
        sources[0],
        PrivateBatchSource::new(&session1, &wrong_rule_receipt),
        sources[2],
    ];
    assert!(matches!(
        certificate.verify(&wrong_rule_sources, 2),
        Err(PrivateBatchOptimizerError::SourceMismatch {
            index: 1,
            reason: "private rule differs"
        })
    ));

    let mut wrong_price_receipt = receipt1.clone();
    wrong_price_receipt.statement.p_star = 2;
    let wrong_price_sources = [
        sources[0],
        PrivateBatchSource::new(&session1, &wrong_price_receipt),
        sources[2],
    ];
    assert!(matches!(
        certificate.verify(&wrong_price_sources, 2),
        Err(PrivateBatchOptimizerError::SourceMismatch {
            index: 1,
            reason: "clearing price differs from live settlement"
        })
    ));

    let wrong_session_sources = [
        sources[0],
        PrivateBatchSource::new(&session0, &receipt1),
        sources[2],
    ];
    assert!(matches!(
        certificate.verify(&wrong_session_sources, 2),
        Err(PrivateBatchOptimizerError::SourceMismatch {
            index: 1,
            reason: "private session differs"
        })
    ));

    let mut wrong_winner_receipt = receipt1.clone();
    wrong_winner_receipt.winner = actor("bazaar-bidder:substituted");
    let wrong_winner_sources = [
        sources[0],
        PrivateBatchSource::new(&session1, &wrong_winner_receipt),
        sources[2],
    ];
    assert!(matches!(
        certificate.verify(&wrong_winner_sources, 2),
        Err(PrivateBatchOptimizerError::SourceMismatch {
            index: 1,
            reason: "winner differs from live settlement"
        })
    ));

    let mut wrong_turn_receipt = receipt1.clone();
    wrong_turn_receipt.settlement_turn.turn_hash[0] ^= 1;
    let wrong_turn_sources = [
        sources[0],
        PrivateBatchSource::new(&session1, &wrong_turn_receipt),
        sources[2],
    ];
    assert_eq!(
        certificate.verify(&wrong_turn_sources, 2),
        Err(PrivateBatchOptimizerError::CertificateMismatch)
    );

    let scene = keep_scene();
    let keep = deploy_keep(0xBA);
    let target = keep.cell_id();
    let claim_red = choice_at(&scene, ROOM_HALL, KP_CLAIM_RED);
    let other_keep = deploy_keep(0xBB);
    let mut gate = PrivateBatchConsequenceGate::new(target, allocation_tag(), certificate.clone());

    let redirected_ran = Cell::new(false);
    let redirected = gate
        .apply_game_turn(&sources, other_keep.cell_id(), |_| {
            redirected_ran.set(true);
            unreachable!("a target substitution cannot reach the game")
        })
        .expect_err("certificate is target-bound by its consequence gate");
    assert_eq!(redirected, PrivateBatchOptimizerError::TargetMismatch);
    assert!(!redirected_ran.get());
    assert!(!gate.consumed());

    let tampered_ran = Cell::new(false);
    let tampered = gate
        .apply_game_turn(&wrong_root_sources, target, |_| {
            tampered_ran.set(true);
            unreachable!("a source-root substitution cannot reach the game")
        })
        .expect_err("source root is rechecked at consequence time");
    assert_eq!(tampered, PrivateBatchOptimizerError::CertificateMismatch);
    assert!(!tampered_ran.get());
    assert!(!gate.consumed());

    let turn_tampered_ran = Cell::new(false);
    let turn_tampered = gate
        .apply_game_turn(&wrong_turn_sources, target, |_| {
            turn_tampered_ran.set(true);
            unreachable!("a settlement-turn substitution cannot reach the game")
        })
        .expect_err("every source settlement turn is rechecked at consequence time");
    assert_eq!(
        turn_tampered,
        PrivateBatchOptimizerError::CertificateMismatch
    );
    assert!(!turn_tampered_ran.get());
    assert!(!gate.consumed());

    let invalid_turn = gate
        .apply_game_turn(&sources, target, |_| Ok(TurnReceipt::default()))
        .expect_err("a fabricated no-op is not a target-engine consequence");
    assert_eq!(
        invalid_turn,
        PrivateBatchOptimizerError::InvalidGameTurn("zero turn hash")
    );
    assert!(!gate.consumed());

    // The exact allocation drives a real WriteOnce dungeon turn. Its resulting
    // receipt is joined back to the batch certificate and all source turns.
    let consequence = gate
        .apply_game_turn(&sources, target, |selected| {
            assert_eq!(selected, allocations.as_slice());
            keep.apply_choice(ROOM_HALL, KP_CLAIM_RED, &claim_red)
                .map_err(|error| error.to_string())
        })
        .expect("verified batch allocation commits the real crown turn");
    assert_eq!(keep.read_var("relic_owner"), 1);
    assert_eq!(consequence.certificate_commitment, certificate.commitment());
    assert_eq!(consequence.source_root, certificate.source_root());
    assert_eq!(consequence.objective, 6);
    assert_eq!(consequence.allocations, allocations);
    assert_eq!(consequence.target_cell, target);
    assert_eq!(consequence.consequence_tag, allocation_tag());
    assert_ne!(consequence.consequence_id, [0; 32]);
    assert_ne!(consequence.game_turn_hash, [0; 32]);
    assert!(gate.consumed());

    let replay_ran = Cell::new(false);
    let replay = gate
        .apply_game_turn(&sources, target, |_| {
            replay_ran.set(true);
            unreachable!("a consumed certificate cannot reach the game twice")
        })
        .expect_err("batch consequence replay is refused");
    assert_eq!(replay, PrivateBatchOptimizerError::AlreadyConsumed);
    assert!(!replay_ran.get());

    let mut restored =
        PrivateBatchConsequenceGate::new(target, allocation_tag(), certificate.clone());
    restored.restore_consumed(true);
    let restored_ran = Cell::new(false);
    assert_eq!(
        restored.apply_game_turn(&sources, target, |_| {
            restored_ran.set(true);
            unreachable!("restored replay state refuses before dispatch")
        }),
        Err(PrivateBatchOptimizerError::AlreadyConsumed)
    );
    assert!(!restored_ran.get());

    // A real target-engine WriteOnce refusal also consumes nothing.
    let blocked = deploy_keep(0xBC);
    let blocked_scene = keep_scene();
    let claim_blue = choice_at(&blocked_scene, ROOM_HALL, KP_CLAIM_BLUE);
    blocked
        .apply_choice(ROOM_HALL, KP_CLAIM_BLUE, &claim_blue)
        .expect("Blue owns the independent crown first");
    let claim_blocked_red = choice_at(&blocked_scene, ROOM_HALL, KP_CLAIM_RED);
    let mut blocked_gate =
        PrivateBatchConsequenceGate::new(blocked.cell_id(), allocation_tag(), certificate);
    let refused = blocked_gate
        .apply_game_turn(&sources, blocked.cell_id(), |_| {
            blocked
                .apply_choice(ROOM_HALL, KP_CLAIM_RED, &claim_blocked_red)
                .map_err(|error| error.to_string())
        })
        .expect_err("the target executor remains authoritative");
    assert!(matches!(
        refused,
        PrivateBatchOptimizerError::GameRefused(_)
    ));
    assert!(!blocked_gate.consumed());
    assert_eq!(blocked.read_var("relic_owner"), 2);
}
