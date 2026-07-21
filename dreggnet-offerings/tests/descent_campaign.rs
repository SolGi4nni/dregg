//! The real region-cell / Lean-native-Descent campaign composition.

use dreggnet_offerings::campaign::{
    CAMPAIGN_TRAVEL, DescentCampaignMove, DescentCampaignOffering, DescentCampaignSession,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, RecordVerify, SessionConfig};
use dungeon_on_dregg::descent::{DELVE, FLEE, LOOT, SMITE, UNLOCK};

const CROWNED_LINE: [(&str, i64); 18] = [
    (DELVE, 0),
    (SMITE, 0),
    (LOOT, 1),
    (UNLOCK, 2),
    (DELVE, 0),
    (SMITE, 0),
    (LOOT, 2),
    (UNLOCK, 3),
    (DELVE, 0),
    (SMITE, 0),
    (SMITE, 0),
    (LOOT, 3),
    (UNLOCK, 4),
    (DELVE, 0),
    (SMITE, 0),
    (SMITE, 0),
    (LOOT, 0),
    (FLEE, 0),
];

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn offered(
    offering: &DescentCampaignOffering,
    session: &DescentCampaignSession,
    turn: &str,
    arg: i64,
) -> Action {
    offering
        .actions(session)
        .into_iter()
        .find(|action| action.turn == turn && action.arg == arg)
        .unwrap_or_else(|| panic!("missing campaign affordance {turn}({arg})"))
}

fn land(
    offering: &DescentCampaignOffering,
    session: &mut DescentCampaignSession,
    who: &DreggIdentity,
    turn: &str,
    arg: i64,
) -> bool {
    let action = offered(offering, session, turn, arg);
    assert!(action.enabled, "expected {turn}({arg}) to be enabled");
    match offering.advance(session, action, who.clone()) {
        Outcome::Landed { receipt, ended } => {
            assert_ne!(receipt.turn_hash, [0; 32], "a real executor turn landed");
            ended
        }
        Outcome::Refused(reason) => panic!("legal campaign action refused: {reason}"),
    }
}

fn assert_refused(outcome: Outcome) {
    if let Outcome::Landed { .. } = outcome {
        panic!("forged campaign action landed")
    }
}

#[test]
fn crown_is_manually_played_and_is_the_only_region_unlock() {
    let offering = DescentCampaignOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(91))
        .expect("campaign deploys");
    let alice = actor("alice-cipherclerk");

    assert_eq!(session.current_location(), "keep");
    assert_eq!(session.cleared_count(), 0);

    // A forged travel action is sent despite not being advertised. The
    // campaign refuses it before constructing a signed region turn (preserving
    // a landed-only restart image); every admitted travel is still re-checked
    // by the region cell's real FieldGte gate.
    let genesis = session.root();
    assert_refused(offering.advance(
        &mut session,
        Action::new("forge the barred road", CAMPAIGN_TRAVEL, 1, true),
        alice.clone(),
    ));
    assert_eq!(session.root(), genesis);
    assert_eq!(session.revision(), 0);
    assert!(!session.is_cleared("keep"));

    // Seventeen independent player actions are still not a completion.
    for (turn, arg) in CROWNED_LINE[..17].iter().copied() {
        assert!(!land(&offering, &mut session, &alice, turn, arg));
    }
    assert_eq!(session.revision(), 17);
    assert!(!session.is_cleared("keep"));
    let before_forged_travel = session.root();
    assert_refused(offering.advance(
        &mut session,
        Action::new("still barred", CAMPAIGN_TRAVEL, 1, true),
        alice.clone(),
    ));
    assert_eq!(session.root(), before_forged_travel);

    // The eighteenth submitted native action settles the Crown. That exact
    // move carries both a native receipt and the real region clear receipt.
    assert!(!land(&offering, &mut session, &alice, FLEE, 0));
    assert_eq!(session.revision(), 18);
    assert!(session.is_cleared("keep"));
    let crown = session.events().last().expect("crown event");
    assert!(crown.crowned);
    assert!(crown.native_receipt.is_some());
    assert!(crown.region_receipt.is_some());

    // Clearing the Keep opens the executor-gated road; travel starts a fresh
    // native expedition at the destination rather than scripting another win.
    assert!(!land(&offering, &mut session, &alice, CAMPAIGN_TRAVEL, 1));
    assert_eq!(session.current_location(), "vault");
    assert_eq!(session.active_descent().revision(), 0);
    assert!(!session.is_cleared("vault"));
    assert_eq!(session.revision(), 19);

    let report = offering.verify(&session);
    assert!(
        report.verified,
        "fresh dual-executor replay: {}",
        report.detail
    );
    assert_eq!(report.turns, 20, "genesis plus nineteen player commands");
}

#[test]
fn terminal_run_without_crown_cannot_mint_campaign_progress() {
    let offering = DescentCampaignOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(12))
        .expect("campaign deploys");
    let alice = actor("alice-cipherclerk");

    // Native Descent deliberately permits fleeing immediately. It is a real
    // terminal receipt, but not a Crown settlement and therefore carries no
    // region clear receipt or campaign unlock.
    assert!(!land(&offering, &mut session, &alice, FLEE, 0));
    assert_eq!(session.revision(), 1);
    assert!(!session.is_cleared("keep"));
    assert_eq!(session.cleared_count(), 0);
    let event = session.events().last().expect("terminal event recorded");
    assert!(!event.crowned);
    assert!(event.native_receipt.is_some());
    assert!(event.region_receipt.is_none());
    assert!(offering.actions(&session).is_empty());
    assert!(offering.verify(&session).verified);
}

#[test]
fn restart_and_hostile_substitutions_reexecute_exactly() {
    let offering = DescentCampaignOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(33))
        .expect("campaign deploys");
    let alice = actor("alice-cipherclerk");

    for (turn, arg) in CROWNED_LINE[..8].iter().copied() {
        land(&offering, &mut session, &alice, turn, arg);
    }
    let prefix = offering.export_record(&session);
    let mut resumed = offering
        .resume_record(&prefix)
        .expect("a fresh pair of executors reproduces the prefix");
    assert_eq!(resumed.actor(), session.actor());
    assert_eq!(resumed.root(), session.root());
    assert_eq!(resumed.revision(), session.revision());
    assert_eq!(
        resumed.active_descent().game().sim(),
        session.active_descent().game().sim()
    );

    // Continue only from the replayed checkpoint. No helper synthesizes the
    // result; ten more explicit inputs are required.
    for (turn, arg) in CROWNED_LINE[8..].iter().copied() {
        land(&offering, &mut resumed, &alice, turn, arg);
    }
    assert!(resumed.is_cleared("keep"));
    let authentic = offering.export_record(&resumed);
    assert!(offering.verify_record(&resumed, &authentic).verified);

    let mut wrong_actor = authentic.clone();
    wrong_actor.events[0].actor = actor("mallory-cipherclerk");
    assert!(offering.resume_record(&wrong_actor).is_err());
    assert!(!offering.verify_record(&resumed, &wrong_actor).verified);

    let mut wrong_move = authentic.clone();
    wrong_move.events[1].command =
        DescentCampaignMove::Native(dreggnet_offerings::native_descent::NativeDescentMove::Flee);
    assert!(offering.resume_record(&wrong_move).is_err());

    let mut target_wide_relic = authentic.clone();
    target_wide_relic.events[1].command = DescentCampaignMove::Native(
        dreggnet_offerings::native_descent::NativeDescentMove::Loot { relic: u64::MAX },
    );
    assert!(
        offering.resume_record(&target_wide_relic).is_err(),
        "the campaign refuses a stable u64 relic that cannot cross its signed action wire"
    );

    let mut forged_crown = authentic.clone();
    forged_crown
        .events
        .last_mut()
        .expect("terminal event")
        .crowned = false;
    assert!(offering.resume_record(&forged_crown).is_err());

    let mut wrong_native_root = authentic.clone();
    wrong_native_root.events[4].post_native_root[0] ^= 0x80;
    assert!(offering.resume_record(&wrong_native_root).is_err());

    let mut wrong_head = authentic.clone();
    wrong_head.root[31] ^= 1;
    assert!(offering.resume_record(&wrong_head).is_err());

    // A valid native move from another identity remains anti-ghost after the
    // campaign has bound its player.
    let before = session.root();
    let next = offered(&offering, &session, DELVE, 0);
    assert_refused(offering.advance(&mut session, next, actor("mallory-cipherclerk")));
    assert_eq!(session.root(), before);
}
