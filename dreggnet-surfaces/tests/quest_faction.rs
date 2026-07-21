//! The faction-to-quest Offering, driven through its real executor cells and generic host.

use dreggnet_offerings::resume::{InMemoryResumeStore, LoggedMove};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingHost, ResumeError, SessionConfig,
};
use dreggnet_quest::{HALL_ACCEPT, LN_LIGHT_1, LN_LIGHT_2, LN_LIGHT_3, LN_TURN_IN};
use dreggnet_surfaces::quest::{
    AshenmoorErrandOffering, KEY, TURN_BETRAY_EMBERS, TURN_PLEDGE_EMBERS, TURN_QUEST_CHOICE,
    TURN_UNDERTAKE_TRIAL,
};

fn alice() -> DreggIdentity {
    DreggIdentity("player:alice".to_string())
}

fn bob() -> DreggIdentity {
    DreggIdentity("player:bob".to_string())
}

fn action(turn: &str, arg: i64) -> Action {
    Action::new(turn, turn, arg, true)
}

#[test]
fn a_single_owner_earns_standing_and_completes_a_replayed_quest() {
    let offering = AshenmoorErrandOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(77))
        .expect("the errand opens");

    // HOSTILE: the disabled trial button is presentation only. Firing it early reaches the
    // faction executor and its FieldGte tooth refuses; no actor is claimed and no ghost turn lands.
    let early_trial = offering.advance(&mut session, action(TURN_UNDERTAKE_TRIAL, 1), alice());
    assert!(!early_trial.landed(), "standing cannot be self-reported");
    assert_eq!(session.turns(), 0);
    assert!(session.owner().is_none());

    // HOSTILE: a quest coordinate cannot be fired before the real faction unlock.
    let early_quest = offering.advance(
        &mut session,
        action(TURN_QUEST_CHOICE, LN_LIGHT_1 as i64),
        alice(),
    );
    assert!(!early_quest.landed());
    assert_eq!(session.quest_steps_done(), 0);

    // The first genuine standing turn claims the whole composition for Alice.
    assert!(
        offering
            .advance(&mut session, action(TURN_PLEDGE_EMBERS, 0), alice(),)
            .landed()
    );
    assert_eq!(session.owner(), Some(&alice()));

    // HOSTILE: another derived identity cannot continue Alice's committed history.
    let before = session.turns();
    let stolen = offering.advance(&mut session, action(TURN_PLEDGE_EMBERS, 0), bob());
    assert!(!stolen.landed(), "a second actor cannot steal the errand");
    assert_eq!(session.turns(), before, "anti-ghost: no stolen turn");

    // HOSTILE: a real executor refusal after a landed move burns the submitting agent's
    // anti-DoS nonce but must neither ghost a faction move nor invalidate later replay.
    let insufficient = offering.advance(&mut session, action(TURN_UNDERTAKE_TRIAL, 1), alice());
    assert!(!insufficient.landed());
    assert_eq!(session.turns(), before);

    assert!(
        offering
            .advance(&mut session, action(TURN_PLEDGE_EMBERS, 0), alice(),)
            .landed()
    );
    assert!(
        offering
            .advance(&mut session, action(TURN_UNDERTAKE_TRIAL, 1), alice(),)
            .landed()
    );
    assert!(session.quest_opened());

    // HOSTILE: step two before step one reaches the quest executor's BoundedBy tooth.
    let before = session.turns();
    let out_of_order = offering.advance(
        &mut session,
        action(TURN_QUEST_CHOICE, LN_LIGHT_2 as i64),
        alice(),
    );
    assert!(!out_of_order.landed());
    assert_eq!(session.turns(), before);
    assert_eq!(session.quest_steps_done(), 0);

    // The canonical ordered line is five genuine quest receipts and ends only at reward == 1.
    for choice in [LN_LIGHT_1, LN_LIGHT_2, LN_LIGHT_3, LN_TURN_IN, HALL_ACCEPT] {
        assert!(
            offering
                .advance(
                    &mut session,
                    action(TURN_QUEST_CHOICE, choice as i64),
                    alice(),
                )
                .landed(),
            "quest choice {choice} lands"
        );
    }
    assert!(session.quest_completed());
    assert!(session.ended());
    assert_eq!(session.turns(), 8, "three faction + five quest turns");

    let report = offering.verify(&session);
    assert!(
        report.verified,
        "both cells replay exactly: {}",
        report.detail
    );
    assert_eq!(report.turns, 10, "both genesis turns are verified too");
    let rendered = format!("{:?}", offering.render(&session).view());
    assert!(rendered.contains("completion replay-verifiable"));
}

#[test]
fn betrayal_is_a_real_terminal_choice_not_a_reversible_ui_flag() {
    let offering = AshenmoorErrandOffering::new();
    let mut session = offering.open(SessionConfig::default()).expect("open");
    let betrayed = offering.advance(&mut session, action(TURN_BETRAY_EMBERS, 2), alice());
    assert!(betrayed.landed());
    assert!(session.standing().betrayed);
    assert!(session.ended());
    assert!(!session.quest_opened());
    assert!(offering.actions(&session).is_empty());

    let reopen = offering.advance(&mut session, action(TURN_UNDERTAKE_TRIAL, 1), alice());
    assert!(!reopen.landed(), "a WriteOnce betrayal cannot be recanted");
    assert_eq!(session.turns(), 1);
    assert!(offering.verify(&session).verified);
}

fn host_with_store(store: &InMemoryResumeStore) -> OfferingHost {
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register(KEY, "Ashenmoor Errand", AshenmoorErrandOffering::new());
    host
}

fn hosted_advance(host: &mut OfferingHost, id: &dreggnet_offerings::SessionId, a: Action) {
    let outcome = host
        .advance(KEY, id, a, alice())
        .expect("the hosted errand is open");
    assert!(outcome.landed(), "hosted move lands: {outcome:?}");
}

#[test]
fn generic_host_restart_replays_both_worlds_and_rejects_an_actor_splice() {
    let store = InMemoryResumeStore::new();
    let (id, commitment, honest) = {
        let mut host = host_with_store(&store);
        let id = host.open(KEY).expect("generic host opens quest");
        hosted_advance(&mut host, &id, action(TURN_PLEDGE_EMBERS, 0));
        hosted_advance(&mut host, &id, action(TURN_PLEDGE_EMBERS, 0));
        hosted_advance(&mut host, &id, action(TURN_UNDERTAKE_TRIAL, 1));
        hosted_advance(&mut host, &id, action(TURN_QUEST_CHOICE, LN_LIGHT_1 as i64));
        let commitment = host.commitment(KEY, &id).expect("session commits");
        assert!(host.verify(KEY, &id).expect("verify report").verified);
        let log = host.move_log(KEY, &id).expect("durable move log");
        assert_eq!(log.moves.len(), 4);
        (id, commitment, log)
    };

    let mut rebooted = host_with_store(&store);
    let resumed = rebooted.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(resumed[0].1.is_ok(), "honest history resumes: {resumed:?}");
    assert_eq!(rebooted.commitment(KEY, &id), Some(commitment));
    assert!(rebooted.verify(KEY, &id).unwrap().verified);

    // Replace the second move's identity. The first move claims Alice; replay refuses Bob at
    // index one and leaves no partially-restored forged session live.
    let mut forged = honest;
    forged.moves[1] = LoggedMove::new(action(TURN_PLEDGE_EMBERS, 0), bob());
    let clean_store = InMemoryResumeStore::new();
    let mut fresh = host_with_store(&clean_store);
    let error = fresh
        .resume(&forged)
        .expect_err("actor splice fails closed");
    assert!(matches!(error, ResumeError::Refused { index: 1, .. }));
    assert!(!fresh.is_open(KEY, &id));
}

#[test]
fn do_once_registrar_mounts_the_new_quest_surface() {
    let mut host = OfferingHost::new();
    dreggnet_surfaces::register_surfaces(&mut host);
    assert!(host.has(KEY));
    let id = host.open(KEY).expect("registered quest opens");
    assert!(host.render(KEY, &id).is_some());
    assert!(host.verify(KEY, &id).unwrap().verified);
}
