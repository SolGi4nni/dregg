//! The shared hosted-party path without any frontend-specific implementation:
//! per-viewer controls, real receipted lobby transitions, identity-bound play,
//! anti-ghost refusal, and OfferingHost restart replay.

use dreggnet_offerings::{
    Action, DreggIdentity, InMemoryResumeStore, Offering, OfferingHost, SessionConfig,
};
use dreggnet_party::Role;
use dreggnet_surfaces::PartyOffering;
use dreggnet_surfaces::party::{
    TURN_ACT, TURN_ADVANCE_ENEMY, TURN_CLAIM, TURN_FORK, TURN_LAUNCH, TURN_READY, TURN_RESOLVE_FORK,
};
use dungeon_on_dregg::combat::{WARDEN, is_hero};

const KEY: &str = "party-live";

fn identity(name: &str) -> DreggIdentity {
    DreggIdentity(format!("player:{name}"))
}

fn action(turn: &str, arg: i64) -> Action {
    Action::new(turn, turn, arg, true)
}

fn form_and_launch(
    offering: &PartyOffering,
    session: &mut dreggnet_surfaces::party::PartySession,
) -> [DreggIdentity; 4] {
    let players = [
        identity("alice"),
        identity("bob"),
        identity("carol"),
        identity("dana"),
    ];
    for (idx, player) in players.iter().enumerate() {
        let claim = offering.advance(session, action(TURN_CLAIM, idx as i64), player.clone());
        let receipt = match claim {
            dreggnet_offerings::Outcome::Landed { receipt, .. } => receipt,
            other => panic!("role claim must land: {other:?}"),
        };
        assert_ne!(receipt.turn_hash, [0u8; 32]);
        assert!(
            receipt.action_count > 0,
            "the complete real receipt is kept"
        );
        assert!(
            offering
                .advance(session, action(TURN_READY, 0), player.clone())
                .landed()
        );
    }
    assert!(
        offering
            .advance(session, action(TURN_LAUNCH, 0), players[0].clone())
            .landed()
    );
    players
}

fn choose_warden(
    offering: &PartyOffering,
    session: &mut dreggnet_surfaces::party::PartySession,
    players: &[DreggIdentity; 4],
) {
    for player in players.iter().take(3) {
        assert!(
            offering
                .advance(session, action(TURN_FORK, 0), player.clone())
                .landed(),
            "each seated identity casts its own custody-signed target ballot"
        );
    }
    assert!(
        offering
            .advance(session, action(TURN_RESOLVE_FORK, 0), players[0].clone(),)
            .landed(),
        "the leader enacts the quorum target"
    );
    assert_eq!(session.target(), Some(WARDEN));
}

fn advance_enemies(
    offering: &PartyOffering,
    session: &mut dreggnet_surfaces::party::PartySession,
    leader: &DreggIdentity,
) {
    for _ in 0..4 {
        if session.arena_active().is_some_and(is_hero) {
            return;
        }
        assert!(
            offering
                .advance(session, action(TURN_ADVANCE_ENEMY, 0), leader.clone())
                .landed(),
            "the leader explicitly advances each enemy turn"
        );
    }
    panic!("initiative did not reach a hero within one round");
}

#[test]
fn per_viewer_lobby_launches_and_binds_moves_to_the_claimed_identity() {
    let offering = PartyOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(41))
        .expect("party table opens");
    let alice = identity("alice");
    let bob = identity("bob");

    let alice_actions = offering.actions_for(&session, &alice);
    assert_eq!(
        alice_actions
            .iter()
            .filter(|candidate| candidate.turn == TURN_CLAIM)
            .count(),
        4,
        "a new viewer sees every open role"
    );
    assert!(
        offering
            .advance(
                &mut session,
                action(TURN_CLAIM, Role::Tank.index() as i64),
                alice.clone(),
            )
            .landed()
    );
    let before = session.turns();
    assert!(
        !offering
            .advance(
                &mut session,
                action(TURN_CLAIM, Role::Tank.index() as i64),
                bob.clone(),
            )
            .landed(),
        "Bob cannot steal Alice's occupied role"
    );
    assert_eq!(session.turns(), before, "refusal is anti-ghost");

    // Start afresh for the full four-role flow.
    let mut session = offering
        .open(SessionConfig::with_seed(42))
        .expect("party table opens");
    let players = form_and_launch(&offering, &mut session);
    assert!(session.launched());
    assert_eq!(session.role_of(players[0].as_str()), Some(Role::Tank));
    assert_eq!(session.role_of(players[3].as_str()), Some(Role::Healer));

    choose_warden(&offering, &mut session, &players);
    advance_enemies(&offering, &mut session, &players[0]);

    // A forged Healer arg cannot select Dana's cell: authority comes from
    // Alice's authenticated identity, which maps only to Tank.
    assert!(
        offering
            .advance(
                &mut session,
                action(TURN_ACT, Role::Healer.index() as i64),
                players[0].clone(),
            )
            .landed()
    );
    let before = session.turns();
    assert!(
        !offering
            .advance(&mut session, action(TURN_ACT, 0), players[0].clone())
            .landed(),
        "the hosted once-per-encounter preflight refuses a repeated contribution"
    );
    assert_eq!(session.turns(), before);
    assert!(
        session.encounter_revision() >= 5,
        "three votes, resolution, tactic"
    );
    assert!(offering.verify(&session).verified);

    assert!(
        offering
            .actions_for(&session, &identity("spectator"))
            .is_empty(),
        "a spectator gets no role capability controls"
    );
}

fn host_with_store(store: &InMemoryResumeStore) -> OfferingHost {
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register(KEY, "Live party", PartyOffering::new());
    host
}

#[test]
fn hosted_party_chooses_a_target_fights_and_survives_restart() {
    let store = InMemoryResumeStore::new();
    let players = [
        identity("alice"),
        identity("bob"),
        identity("carol"),
        identity("dana"),
    ];

    let (id, committed, rendered, report) = {
        let mut host = host_with_store(&store);
        let id = host.open(KEY).expect("open hosted party");
        for (idx, player) in players.iter().enumerate() {
            assert!(
                host.advance(KEY, &id, action(TURN_CLAIM, idx as i64), player.clone(),)
                    .expect("live")
                    .landed()
            );
            assert!(
                host.advance(KEY, &id, action(TURN_READY, 0), player.clone())
                    .expect("live")
                    .landed()
            );
        }
        assert!(
            host.advance(KEY, &id, action(TURN_LAUNCH, 0), players[0].clone())
                .expect("live")
                .landed()
        );
        for player in players.iter().take(3) {
            assert!(
                host.advance(KEY, &id, action(TURN_FORK, 0), player.clone())
                    .expect("live")
                    .landed()
            );
        }
        assert!(
            host.advance(KEY, &id, action(TURN_RESOLVE_FORK, 0), players[0].clone(),)
                .expect("live")
                .landed()
        );
        let before_stale = host.move_log(KEY, &id).expect("replay log").moves.len();
        assert!(
            !host
                .advance(KEY, &id, action(TURN_FORK, 1), players[3].clone())
                .expect("live")
                .landed(),
            "a ballot cannot be appended after target resolution"
        );
        assert_eq!(
            host.move_log(KEY, &id).expect("replay log").moves.len(),
            before_stale,
            "the stale ballot refusal is anti-ghost"
        );
        for _ in 0..4 {
            let leader_actions = host
                .actions_for(KEY, &id, &players[0])
                .expect("leader controls");
            if !leader_actions
                .iter()
                .any(|candidate| candidate.turn == TURN_ADVANCE_ENEMY && candidate.enabled)
            {
                break;
            }
            assert!(
                host.advance(KEY, &id, action(TURN_ADVANCE_ENEMY, 0), players[0].clone(),)
                    .expect("live")
                    .landed()
            );
        }
        assert!(
            host.advance(KEY, &id, action(TURN_ACT, 99), players[2].clone())
                .expect("live")
                .landed(),
            "Mage contribution mechanically advances the Arena"
        );
        let before_duplicate = host.move_log(KEY, &id).expect("replay log").moves.len();
        assert!(
            !host
                .advance(KEY, &id, action(TURN_ACT, 0), players[2].clone())
                .expect("live")
                .landed(),
            "the Mage role's WriteOnce tooth refuses a duplicate"
        );
        assert_eq!(
            host.move_log(KEY, &id).expect("replay log").moves.len(),
            before_duplicate,
            "the duplicate role refusal is anti-ghost"
        );

        // If initiative gives the other hero the next slot, spend one more
        // distinct role tactic so the lifecycle includes an enemy turn after
        // player tactics rather than relying on a convenient initiative order.
        if !host
            .actions_for(KEY, &id, &players[0])
            .expect("leader controls")
            .iter()
            .any(|candidate| candidate.turn == TURN_ADVANCE_ENEMY && candidate.enabled)
        {
            assert!(
                host.advance(KEY, &id, action(TURN_ACT, 0), players[0].clone())
                    .expect("live")
                    .landed(),
                "the Tank contributes when two heroes act consecutively"
            );
        }
        let before_wrong_enemy = host.move_log(KEY, &id).expect("replay log").moves.len();
        assert!(
            !host
                .advance(KEY, &id, action(TURN_ADVANCE_ENEMY, 0), players[1].clone(),)
                .expect("live")
                .landed(),
            "a non-leader cannot drive the enemy AI"
        );
        assert_eq!(
            host.move_log(KEY, &id).expect("replay log").moves.len(),
            before_wrong_enemy,
            "wrong-actor refusal is anti-ghost"
        );
        assert!(
            host.advance(KEY, &id, action(TURN_ADVANCE_ENEMY, 0), players[0].clone(),)
                .expect("live")
                .landed(),
            "the leader explicitly advances an enemy after the role tactic"
        );
        assert!(
            host.move_log(KEY, &id).expect("replay log").moves.len() >= 14,
            "formation plus three ballots, resolution, and a tactic are durable hosted moves"
        );
        let report = host.verify(KEY, &id).expect("verify report");
        let committed = host.commitment(KEY, &id).expect("state commitment");
        let rendered = format!("{:?}", host.render(KEY, &id).expect("render").0);
        (id, committed, rendered, report)
    };

    let mut rebooted = host_with_store(&store);
    let resumed = rebooted.resume_all();
    assert_eq!(resumed.len(), 1);
    assert_eq!(resumed[0].1.as_ref().expect("honest log resumes"), &id);
    assert_eq!(
        format!("{:?}", rebooted.render(KEY, &id).expect("render").0),
        rendered,
        "restart must reproduce the exact frontend-neutral tactical state"
    );
    let resumed_report = rebooted.verify(KEY, &id).expect("verify report");
    assert_eq!(
        (
            resumed_report.verified,
            resumed_report.turns,
            resumed_report.detail.as_str(),
        ),
        (report.verified, report.turns, report.detail.as_str()),
        "restart must reproduce the same semantic verification report"
    );
    assert_eq!(
        rebooted.commitment(KEY, &id).expect("resumed commitment"),
        committed,
        "the shared lobby and launched party are reproduced exactly"
    );
    assert!(rebooted.verify(KEY, &id).unwrap().verified);
    assert!(
        rebooted.render(KEY, &id).is_some(),
        "the returning tactical table renders through the frontend-neutral host"
    );
    assert!(
        rebooted
            .move_log(KEY, &id)
            .expect("resumed move log")
            .moves
            .iter()
            .any(|step| step.action.turn == TURN_RESOLVE_FORK),
        "the quorum decision remains an ordinary resumable shared-surface move"
    );
}
