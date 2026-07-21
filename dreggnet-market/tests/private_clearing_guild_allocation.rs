//! A proven private Bazaar winner receives a real multiplayer raid allocation.
//!
//! An exact ordered guild roster maps market identities to three independent
//! executor-backed hero cells. The HidingFRI-authorized Bazaar winner alone earns
//! the configured raid XP; reordered/substituted rosters, receipt substitution,
//! wrong targets, dead-character refusals, replay, and the post-turn crash window
//! all fail closed.

#![cfg(feature = "private-clearing")]

use std::cell::{Cell, RefCell};

use dreggnet_market::private_clearing::{PrivateClearingExpectation, PrivateClearingReceipt};
use dreggnet_market::private_clearing_consequence::{
    PrivateClearingCommittedObservation, PrivateClearingConsequenceDisposition,
    PrivateClearingConsequenceError, PrivateClearingConsequenceSource,
    PrivateClearingConsequenceTag,
};
use dreggnet_market::private_clearing_guild_allocation::{
    GuildMember, GuildReward, GuildRoster, PrivateClearingGuildAllocation,
    PrivateClearingGuildAllocationError,
};
use dreggnet_market::{DarkBazaarOffering, DarkBazaarSession, TURN_BID, TURN_LIST};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dungeon_on_dregg::progression::{deploy_hero, gain_xp, perish};

const SELLER: &str = "guild:alice";
const LOW_BIDDER: &str = "guild:bob";
const WINNER: &str = "guild:carol";
const RAID_XP: u64 = 125;

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
        .open(SessionConfig::with_seed(0x6A_11_DA))
        .expect("Dark Bazaar opens");
    land(&offering, &mut session, TURN_LIST, 1, SELLER);
    land(&offering, &mut session, TURN_BID, 2, LOW_BIDDER);
    land(&offering, &mut session, TURN_BID, 3, WINNER);
    let authorization = session
        .prepare_private_clearing_zk()
        .expect("real private clearing proof");
    let statement = authorization.statement();
    let receipt = offering
        .settle_private_verified(
            &mut session,
            authorization,
            PrivateClearingExpectation::from_statement(statement),
        )
        .expect("proof authorizes authoritative Bazaar settlement");
    (session, receipt)
}

fn roster_for(cells: [dregg_app_framework::CellId; 3]) -> GuildRoster {
    GuildRoster::new(vec![
        GuildMember::new(actor(SELLER), cells[0]),
        GuildMember::new(actor(LOW_BIDDER), cells[1]),
        GuildMember::new(actor(WINNER), cells[2]),
    ])
    .expect("three-member exact guild roster")
}

fn raid_reward() -> GuildReward {
    GuildReward::new("raid-xp/frost-vault/v1", RAID_XP).expect("nonzero named raid reward")
}

#[test]
fn private_winner_alone_receives_exact_roster_bound_raid_xp_with_crash_recovery() {
    let (session, receipt) = privately_settled_market();
    let source = PrivateClearingConsequenceSource::from_verified_receipt(&receipt)
        .expect("pin the exact verified private result");

    let alice = deploy_hero(0x21);
    let bob = deploy_hero(0x22);
    let carol = deploy_hero(0x23);
    let roster = roster_for([alice.cell_id(), bob.cell_id(), carol.cell_id()]);
    let expected_roster = roster.digest();
    let allocation = PrivateClearingGuildAllocation::new(
        source.clone(),
        roster.clone(),
        expected_roster,
        raid_reward(),
    )
    .expect("verified winner maps to Carol's exact character cell");
    assert_eq!(allocation.selected_member().actor, actor(WINNER));
    assert_eq!(allocation.selected_member().character_cell, carol.cell_id());
    assert_eq!(allocation.reward().amount, RAID_XP);

    // ROSTER HOSTILITY: order and actor->cell mapping are part of the pinned
    // digest. Neither a reorder nor a substituted winner cell can instantiate
    // the deployment's allocation policy.
    let reordered = GuildRoster::new(vec![
        GuildMember::new(actor(LOW_BIDDER), bob.cell_id()),
        GuildMember::new(actor(SELLER), alice.cell_id()),
        GuildMember::new(actor(WINNER), carol.cell_id()),
    ])
    .expect("internally valid but differently ordered roster");
    assert!(matches!(
        PrivateClearingGuildAllocation::new(
            source.clone(),
            reordered,
            expected_roster,
            raid_reward(),
        ),
        Err(PrivateClearingGuildAllocationError::RosterDigestMismatch)
    ));
    let impostor = deploy_hero(0x24);
    let substituted = roster_for([alice.cell_id(), bob.cell_id(), impostor.cell_id()]);
    assert!(matches!(
        PrivateClearingGuildAllocation::new(
            source.clone(),
            substituted,
            expected_roster,
            raid_reward(),
        ),
        Err(PrivateClearingGuildAllocationError::RosterDigestMismatch)
    ));

    let no_winner = GuildRoster::new(vec![
        GuildMember::new(actor(SELLER), alice.cell_id()),
        GuildMember::new(actor(LOW_BIDDER), bob.cell_id()),
    ])
    .expect("valid two-member roster without Carol");
    let no_winner_digest = no_winner.digest();
    assert!(matches!(
        PrivateClearingGuildAllocation::new(
            source.clone(),
            no_winner,
            no_winner_digest,
            raid_reward(),
        ),
        Err(PrivateClearingGuildAllocationError::WinnerNotInRoster)
    ));
    assert!(matches!(
        GuildRoster::new(vec![
            GuildMember::new(actor(SELLER), alice.cell_id()),
            GuildMember::new(actor(WINNER), alice.cell_id()),
        ]),
        Err(PrivateClearingGuildAllocationError::DuplicateCharacterCell { .. })
    ));

    let mut gate = allocation.consequence_gate();
    let target = allocation.selected_member().character_cell;

    // The exact source receipt remains pinned beneath the roster policy.
    let mut substituted_receipt = receipt.clone();
    substituted_receipt.winner = actor(LOW_BIDDER);
    let substituted_ran = Cell::new(false);
    let source_error = gate
        .apply_game_turn(&session, &substituted_receipt, target, || {
            substituted_ran.set(true);
            unreachable!("substituted source cannot reach the hero executor")
        })
        .expect_err("source receipt substitution is refused");
    assert!(matches!(
        source_error,
        PrivateClearingConsequenceError::ReceiptMismatch(_)
    ));
    assert!(!substituted_ran.get());

    let redirected_ran = Cell::new(false);
    let redirect = gate
        .apply_game_turn(&session, &receipt, bob.cell_id(), || {
            redirected_ran.set(true);
            unreachable!("winner's reward cannot be redirected to Bob")
        })
        .expect_err("nonwinner target is refused");
    assert_eq!(redirect, PrivateClearingConsequenceError::TargetMismatch);
    assert!(!redirected_ran.get());
    assert_eq!(alice.read_var("xp"), 0);
    assert_eq!(bob.read_var("xp"), 0);
    assert_eq!(carol.read_var("xp"), 0);

    // One real StrictMonotonic XP turn awards only the selected guild member.
    let award = gate
        .apply_game_turn(&session, &receipt, target, || {
            gain_xp(&carol, RAID_XP).map_err(|error| error.to_string())
        })
        .expect("private winner earns the roster-bound raid bounty");
    assert_eq!(award.winner, actor(WINNER));
    assert_eq!(award.target_cell, carol.cell_id());
    assert_eq!(award.consequence_tag, allocation.consequence_tag());
    assert_eq!(
        award.disposition,
        PrivateClearingConsequenceDisposition::Committed
    );
    assert_eq!(alice.read_var("xp"), 0);
    assert_eq!(bob.read_var("xp"), 0);
    assert_eq!(carol.read_var("xp"), RAID_XP);

    let replay_ran = Cell::new(false);
    let replay = gate
        .apply_game_turn(&session, &receipt, target, || {
            replay_ran.set(true);
            unreachable!("raid bounty cannot execute twice")
        })
        .expect_err("allocation replay is refused before dispatch");
    assert_eq!(replay, PrivateClearingConsequenceError::AlreadyConsumed);
    assert!(!replay_ran.get());
    assert_eq!(carol.read_var("xp"), RAID_XP);

    // GAME REFUSAL: a dead raid member cannot earn XP. The executor refusal
    // preserves XP and does not consume the allocation id.
    let dead_alice = deploy_hero(0x31);
    let dead_bob = deploy_hero(0x32);
    let dead_carol = deploy_hero(0x33);
    perish(&dead_carol).expect("hardcore death commits before bounty attempt");
    let dead_roster = roster_for([
        dead_alice.cell_id(),
        dead_bob.cell_id(),
        dead_carol.cell_id(),
    ]);
    let dead_digest = dead_roster.digest();
    let dead_allocation = PrivateClearingGuildAllocation::new(
        source.clone(),
        dead_roster,
        dead_digest,
        raid_reward(),
    )
    .expect("same winner maps to the dead character deployment");
    let mut dead_gate = dead_allocation.consequence_gate();
    let dead_error = dead_gate
        .apply_game_turn(&session, &receipt, dead_carol.cell_id(), || {
            gain_xp(&dead_carol, RAID_XP).map_err(|error| error.to_string())
        })
        .expect_err("dead character XP is refused by the game executor");
    assert!(matches!(
        dead_error,
        PrivateClearingConsequenceError::GameRefused(_)
    ));
    assert_eq!(dead_gate.consumed_count(), 0);
    assert_eq!(dead_carol.read_var("xp"), 0);

    // CRASH/RESTART: a separate guild deployment commits Carol's XP, then loses
    // replay state. Recovery requires the exact allocation id/target/tag plus a
    // target-specific observation of XP and the committed executor receipt.
    let crash_alice = deploy_hero(0x41);
    let crash_bob = deploy_hero(0x42);
    let crash_carol = deploy_hero(0x43);
    let crash_roster = roster_for([
        crash_alice.cell_id(),
        crash_bob.cell_id(),
        crash_carol.cell_id(),
    ]);
    let crash_digest = crash_roster.digest();
    let crash_allocation =
        PrivateClearingGuildAllocation::new(source, crash_roster, crash_digest, raid_reward())
            .expect("crash-test allocation");
    let crash_target = crash_allocation.selected_member().character_cell;
    let observed = RefCell::new(None::<PrivateClearingCommittedObservation>);
    let mut crash_gate = crash_allocation.consequence_gate();
    let crash = crash_gate
        .apply_game_turn_with_commit_hook(
            &session,
            &receipt,
            crash_target,
            || gain_xp(&crash_carol, RAID_XP).map_err(|error| error.to_string()),
            |id, game_receipt| {
                observed.replace(Some(PrivateClearingCommittedObservation::new(
                    id,
                    crash_target,
                    crash_allocation.consequence_tag(),
                    game_receipt.clone(),
                )));
                Err("simulated crash before replay persistence".to_owned())
            },
        )
        .expect_err("game committed across injected replay-write crash");
    assert!(matches!(
        crash,
        PrivateClearingConsequenceError::ReplayCommitInterrupted(_)
    ));
    assert_eq!(crash_gate.consumed_count(), 0);
    assert_eq!(crash_carol.read_var("xp"), RAID_XP);
    drop(crash_gate);

    let mut restarted = crash_allocation.consequence_gate();
    let recovered = restarted
        .recover_committed_game_turn(&session, &receipt, crash_target, |id, target, tag| {
            let observation = observed.borrow().clone();
            let committed = observation.as_ref().expect("game receipt is durable");
            assert_eq!(id, committed.consequence_id());
            assert_eq!(target, crash_target);
            assert_eq!(tag, crash_allocation.consequence_tag());
            assert_eq!(crash_carol.read_var("xp"), RAID_XP);
            Ok(observation)
        })
        .expect("restart re-observes committed XP receipt without a second grant");
    assert_eq!(
        recovered.disposition,
        PrivateClearingConsequenceDisposition::Recovered
    );
    let post_recovery_ran = Cell::new(false);
    let second = restarted
        .apply_game_turn(&session, &receipt, crash_target, || {
            post_recovery_ran.set(true);
            unreachable!("recovered raid allocation cannot grant XP twice")
        })
        .expect_err("recovered allocation is one-shot");
    assert_eq!(second, PrivateClearingConsequenceError::AlreadyConsumed);
    assert!(!post_recovery_ran.get());
    assert_eq!(crash_carol.read_var("xp"), RAID_XP);

    // A roster-bound allocation tag cannot be replaced during recovery.
    let committed = observed.borrow().clone().expect("committed observation");
    let wrong_tag = PrivateClearingConsequenceTag::from_label("raid-xp/other-guild/v1");
    let wrong_observation = PrivateClearingCommittedObservation::new(
        committed.consequence_id(),
        committed.target_cell(),
        wrong_tag,
        committed.game_receipt().clone(),
    );
    let mut hostile_restart = crash_allocation.consequence_gate();
    let wrong = hostile_restart
        .recover_committed_game_turn(&session, &receipt, crash_target, |_, _, _| {
            Ok(Some(wrong_observation))
        })
        .expect_err("another guild allocation tag cannot claim this XP receipt");
    assert!(matches!(
        wrong,
        PrivateClearingConsequenceError::RecoveryObservation(_)
    ));
    assert_eq!(hostile_restart.consumed_count(), 0);
}
