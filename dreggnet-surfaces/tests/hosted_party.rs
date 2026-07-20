//! The shared hosted-party path without any frontend-specific implementation:
//! per-viewer controls, real receipted lobby transitions, identity-bound play,
//! anti-ghost refusal, and OfferingHost restart replay.

use dreggnet_offerings::{
    Action, DreggIdentity, InMemoryResumeStore, Offering, OfferingHost, SessionConfig,
};
use dreggnet_party::Role;
use dreggnet_surfaces::PartyOffering;
use dreggnet_surfaces::party::{TURN_ACT, TURN_CLAIM, TURN_LAUNCH, TURN_READY};

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
fn hosted_party_survives_restart_by_replaying_each_landed_player_action() {
    let store = InMemoryResumeStore::new();
    let players = [
        identity("alice"),
        identity("bob"),
        identity("carol"),
        identity("dana"),
    ];

    let (id, committed) = {
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
        assert!(
            host.advance(KEY, &id, action(TURN_ACT, 99), players[2].clone())
                .expect("live")
                .landed()
        );
        assert_eq!(
            host.move_log(KEY, &id).expect("replay log").moves.len(),
            10,
            "four claims + four ready + launch + one role move"
        );
        let committed = host.commitment(KEY, &id).expect("state commitment");
        (id, committed)
    };

    let mut rebooted = host_with_store(&store);
    let resumed = rebooted.resume_all();
    assert_eq!(resumed.len(), 1);
    assert_eq!(resumed[0].1.as_ref().expect("honest log resumes"), &id);
    assert_eq!(
        rebooted.commitment(KEY, &id).expect("resumed commitment"),
        committed,
        "the shared lobby and launched party are reproduced exactly"
    );
    assert!(rebooted.verify(KEY, &id).unwrap().verified);
    assert!(
        rebooted
            .actions_for(KEY, &id, &players[1])
            .expect("viewer controls")
            .iter()
            .any(|candidate| candidate.turn == TURN_ACT),
        "a returning seated player gets their own role control"
    );
}
