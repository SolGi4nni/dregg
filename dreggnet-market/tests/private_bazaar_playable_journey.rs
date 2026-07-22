//! Browser/chat-neutral Dark Bazaar raid journey, through the real engines.
//!
//! The only actions presented to players are payload-free `enter`/`refresh`
//! actions. The market's private HidingFRI proof is produced and verified behind
//! that boundary; its winner is joined to an existing executor-backed hero and
//! causes one real monotonic XP turn. Shared receipt/surface projections retain
//! commitments and turn hashes but no bid, winner, selected cell, witness, or
//! proof bytes.

#![cfg(feature = "private-clearing")]

use std::cell::{Cell, RefCell};

use dreggnet_market::private_bazaar_journey::{
    PrivateBazaarJourneyError, PrivateBazaarPublicAction, PrivateBazaarPublicPhase,
    PrivateBazaarRaidJourney,
};
use dreggnet_market::private_clearing::PrivateClearingExpectation;
use dreggnet_market::private_clearing_consequence::PrivateClearingConsequenceError;
use dreggnet_market::private_clearing_guild_allocation::{GuildMember, GuildReward, GuildRoster};
use dreggnet_market::{DarkBazaarOffering, TURN_BID, TURN_LIST};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dungeon_on_dregg::progression::{deploy_hero, gain_xp};

const SELLER: &str = "journey:guild-alice";
const LOW_BIDDER: &str = "journey:guild-bob";
const WINNER: &str = "journey:guild-carol";
const RAID_XP: u64 = 144;

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_owned())
}

fn land(
    offering: &DarkBazaarOffering,
    session: &mut dreggnet_market::DarkBazaarSession,
    turn: &str,
    value: i64,
    who: &str,
) {
    let outcome = offering.advance(session, Action::new(turn, turn, value, true), actor(who));
    assert!(matches!(outcome, Outcome::Landed { .. }), "{outcome:?}");
}

#[test]
fn payload_free_public_entry_becomes_viewer_blind_settlement_and_real_raid_xp() {
    // These hero cells pre-exist the market. The journey commits their exact
    // actor->cell roster without copying its members into the shared receipt.
    let alice = deploy_hero(0x81);
    let bob = deploy_hero(0x82);
    let carol = deploy_hero(0x83);
    let roster = GuildRoster::new(vec![
        GuildMember::new(actor(SELLER), alice.cell_id()),
        GuildMember::new(actor(LOW_BIDDER), bob.cell_id()),
        GuildMember::new(actor(WINNER), carol.cell_id()),
    ])
    .expect("existing guild roster");
    let reward = GuildReward::new("raid-xp/ashen-vault/v1", RAID_XP).expect("named reward");

    let offering = DarkBazaarOffering::new();
    let mut market = offering
        .open(SessionConfig::with_seed(0xB4_2A_A2))
        .expect("Dark Bazaar opens");
    land(&offering, &mut market, TURN_LIST, 1, SELLER);
    // Bid values enter the owning sealed/private market path, never the public
    // journey actions or its receipt/surface.
    land(&offering, &mut market, TURN_BID, 2, LOW_BIDDER);
    land(&offering, &mut market, TURN_BID, 3, WINNER);

    let recovery_roster = roster.clone();
    let recovery_reward = reward.clone();
    let mut unentered = PrivateBazaarRaidJourney::new(&market, roster.clone(), reward.clone())
        .expect("parallel unentered refusal fixture");
    let mut journey =
        PrivateBazaarRaidJourney::new(&market, roster, reward).expect("bind existing game state");
    assert_eq!(
        unentered
            .advance_public(&PrivateBazaarPublicAction::Refresh.offering_action())
            .expect_err("refresh cannot synthesize a pending receipt"),
        PrivateBazaarJourneyError::RefreshBeforeEnter
    );
    assert_eq!(journey.actions().len(), 1);
    let forged_payload = Action::new(
        "enter with an illicit numeric bid",
        dreggnet_market::private_bazaar_journey::TURN_ENTER_PRIVATE_BAZAAR,
        3,
        true,
    );
    assert_eq!(
        journey
            .advance_public(&forged_payload)
            .expect_err("the public journey has no numeric bid lane"),
        PrivateBazaarJourneyError::PublicActionCarriesPayload
    );
    assert!(journey.receipt().is_none());
    let enter = PrivateBazaarPublicAction::Enter.offering_action();
    assert_eq!(enter.arg, 0);
    assert!(enter.text.is_none());
    let pending = journey
        .advance_public(&enter)
        .expect("payload-free public entry");
    assert_eq!(pending.phase, PrivateBazaarPublicPhase::Pending);
    let pending_debug = format!("{:?}\n{:?}", pending, pending.surface().view());
    for hidden in [SELLER, LOW_BIDDER, WINNER, "proof bytes", "witness"] {
        assert!(
            !pending_debug.contains(hidden),
            "shared pending projection leaked {hidden}: {pending_debug}"
        );
    }
    assert!(pending.public_fields().iter().all(|(name, _)| !matches!(
        name.as_str(),
        "winner" | "price" | "reserve" | "actor" | "proofBytes" | "witness"
    )));
    assert_eq!(
        journey
            .advance_public(&enter)
            .expect_err("enter is write-once at the public boundary"),
        PrivateBazaarJourneyError::EnterAlreadySubmitted
    );

    // The real private proof gates the existing executor settlement behind the
    // public surface. No frontend constructs or interprets this proof.
    let authorization = market
        .prepare_private_clearing_zk()
        .expect("real HidingFRI private clearing proof");
    let statement = authorization.statement();
    let private_receipt = offering
        .settle_private_verified(
            &mut market,
            authorization,
            PrivateClearingExpectation::from_statement(statement),
        )
        .expect("private proof authorizes real market settlement");

    let unentered_ran = Cell::new(false);
    assert_eq!(
        unentered
            .settle_verified(&market, &private_receipt, |_, _| {
                unentered_ran.set(true);
                unreachable!("settlement cannot dispatch before public entry")
            })
            .expect_err("a market result cannot skip public entry"),
        PrivateBazaarJourneyError::SettlementBeforeEnter
    );
    assert!(!unentered_ran.get());
    assert_eq!(alice.read_var("xp"), 0);
    assert_eq!(bob.read_var("xp"), 0);
    assert_eq!(carol.read_var("xp"), 0);

    // The game turn commits, then a durable-receipt write fails. The journey
    // deliberately remains pending while the target engine state really moved.
    let dispatches = Cell::new(0usize);
    let observed = RefCell::new(None);
    let interrupted = journey
        .settle_verified_with_commit_hook(
            &market,
            &private_receipt,
            |member, reward| {
                dispatches.set(dispatches.get() + 1);
                assert_eq!(member.character_cell, carol.cell_id());
                assert_eq!(reward.amount, RAID_XP);
                gain_xp(&carol, reward.amount).map_err(|error| error.to_string())
            },
            |observation| {
                observed.replace(Some(observation));
                Err("simulated crash before public receipt persistence".to_owned())
            },
        )
        .expect_err("fault injection lands after the game commit");
    assert!(matches!(
        interrupted,
        PrivateBazaarJourneyError::Source(
            PrivateClearingConsequenceError::ReplayCommitInterrupted(_)
        )
    ));
    assert_eq!(
        journey.receipt().expect("pending survives").phase,
        PrivateBazaarPublicPhase::Pending
    );
    assert_eq!(dispatches.get(), 1);
    assert_eq!(alice.read_var("xp"), 0);
    assert_eq!(bob.read_var("xp"), 0);
    assert_eq!(carol.read_var("xp"), RAID_XP);

    let interrupted_retry_ran = Cell::new(false);
    assert_eq!(
        journey
            .settle_verified(&market, &private_receipt, |_, _| {
                interrupted_retry_ran.set(true);
                unreachable!("an interrupted consequence is recovery-only")
            })
            .expect_err("post-commit interruption cannot redispatch in-process"),
        PrivateBazaarJourneyError::RecoveryRequired
    );
    assert!(!interrupted_retry_ran.get());

    // Restart reconstructs the same journey configuration, then re-observes
    // the exact committed target turn. No game callback exists on recovery, so
    // XP cannot be dispatched twice.
    drop(journey);
    let mut journey =
        PrivateBazaarRaidJourney::resume_pending(&market, recovery_roster, recovery_reward)
            .expect("restart reconstructs the pending public receipt");
    let restarted_retry_ran = Cell::new(false);
    assert_eq!(
        journey
            .settle_verified(&market, &private_receipt, |_, _| {
                restarted_retry_ran.set(true);
                unreachable!("a resumed pending journey is recovery-only")
            })
            .expect_err("restart cannot mistake recovery for a fresh dispatch"),
        PrivateBazaarJourneyError::RecoveryRequired
    );
    assert!(!restarted_retry_ran.get());
    let settled = journey
        .recover_verified(&market, &private_receipt, |id, target, consequence_tag| {
            let observation = observed.borrow_mut().take();
            let committed = observation.as_ref().expect("durable game observation");
            assert_eq!(id, committed.consequence_id());
            assert_eq!(target, committed.target_cell());
            assert_eq!(consequence_tag, committed.consequence_tag());
            assert_eq!(carol.read_var("xp"), RAID_XP);
            Ok(observation)
        })
        .expect("restart closes the post-game/public-receipt crash window");
    assert_eq!(settled.phase, PrivateBazaarPublicPhase::Settled);
    assert_eq!(dispatches.get(), 1);
    assert_eq!(alice.read_var("xp"), 0);
    assert_eq!(bob.read_var("xp"), 0);
    assert_eq!(carol.read_var("xp"), RAID_XP);
    assert!(settled.input_root.is_some());
    assert!(settled.consequence_id.is_some());
    assert!(settled.settlement_turn_hash.is_some());
    assert!(settled.game_turn_hash.is_some());
    assert!(settled.game_state_root.is_some());

    // What all viewers receive is still identity-free even after the private
    // winner drove a specific existing character cell.
    let settled_debug = format!("{:?}\n{:?}", settled, settled.surface().view());
    for hidden in [
        SELLER,
        LOW_BIDDER,
        WINNER,
        "selected_member",
        "proof bytes",
        "witness",
    ] {
        assert!(
            !settled_debug.contains(hidden),
            "shared settled projection leaked {hidden}: {settled_debug}"
        );
    }
    assert!(settled.public_fields().iter().all(|(name, _)| !matches!(
        name.as_str(),
        "winner" | "price" | "reserve" | "actor" | "proofBytes" | "witness"
    )));

    let replay_ran = Cell::new(false);
    let replay = journey
        .settle_verified(&market, &private_receipt, |_, _| {
            replay_ran.set(true);
            unreachable!("a settled public journey cannot redispatch the game turn")
        })
        .expect_err("one journey applies its consequence once");
    assert_eq!(replay, PrivateBazaarJourneyError::SettlementAlreadyApplied);
    assert!(!replay_ran.get());
    assert_eq!(carol.read_var("xp"), RAID_XP);

    let refreshed = journey
        .advance_public(&PrivateBazaarPublicAction::Refresh.offering_action())
        .expect("refresh is a pure read after settlement");
    assert_eq!(refreshed.phase, PrivateBazaarPublicPhase::Settled);
}
