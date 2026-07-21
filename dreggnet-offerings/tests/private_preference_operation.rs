#![cfg(feature = "private-preference-operation")]

use dregg_app_framework::field_from_bytes;
use dreggnet_offerings::dungeon::{
    DungeonOffering, PRIVATE_PREFERENCE_OPERATION, TURN_CHOOSE, private_preference_session_for_seed,
};
use dreggnet_offerings::resume::{InMemoryResumeStore, SessionResumeStore};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingHost, RecordVerify, SessionConfig, SessionId,
};
use dungeon_on_dregg::private_preference::{PrivateBallot, prove_private_preference};
use dungeon_on_dregg::{KP_PRESS_ON, KP_PRIVATE_COUNSEL_DESCEND, deploy_keep, keep_scene};
use spween_dregg::{Driver, verify};

const SEED: u64 = 0xC011EC7;

fn ballots() -> [PrivateBallot; 4] {
    [
        PrivateBallot::try_new([3, 2, 0, 1]).unwrap(),
        PrivateBallot::try_new([2, 3, 0, 1]).unwrap(),
        PrivateBallot::try_new([0, 3, 2, 1]).unwrap(),
        PrivateBallot::try_new([1, 2, 3, 0]).unwrap(),
    ]
}

#[test]
fn claimant_free_private_preference_cannot_be_stolen_by_first_uploader() {
    let offering = DungeonOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(SEED)).unwrap();
    assert!(
        offering
            .binary_operations(&session)
            .iter()
            .any(|operation| operation.name == PRIVATE_PREFERENCE_OPERATION)
    );

    let proof_session = private_preference_session_for_seed(SEED);
    let receipt = prove_private_preference(proof_session, &ballots()).unwrap();
    let honest = receipt.to_postcard().unwrap();
    let counsel = DreggIdentity("guild-counsel".to_string());
    let first_uploader = DreggIdentity("mallory-first-uploader".to_string());

    assert!(
        offering
            .advance(
                &mut session,
                Action::new("press on", TURN_CHOOSE, KP_PRESS_ON as i64, true),
                DreggIdentity("pathfinder".to_string()),
            )
            .landed()
    );
    let benefit = Action::new(
        "take the drowned stair",
        TURN_CHOOSE,
        KP_PRIVATE_COUNSEL_DESCEND as i64,
        true,
    );
    assert!(
        !offering
            .actions(&session)
            .into_iter()
            .find(|action| action.arg == KP_PRIVATE_COUNSEL_DESCEND as i64)
            .unwrap()
            .enabled,
        "the private route is visibly unavailable before proof"
    );
    let before_refusal = session.receipts_len();
    assert!(
        !offering
            .advance(&mut session, benefit.clone(), counsel.clone())
            .landed(),
        "an absent private result cannot produce the two-depth benefit"
    );
    assert_eq!(session.receipts_len(), before_refusal);
    assert_eq!(session.read_var("depth"), 0);

    let wrong = prove_private_preference(proof_session + 1, &ballots())
        .unwrap()
        .to_postcard()
        .unwrap();
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_PREFERENCE_OPERATION,
                &wrong,
                DreggIdentity("intruder".to_string()),
            )
            .is_err()
    );
    assert!(session.private_preference_decision().is_none());
    assert!(session.private_preference_actor().is_none());
    assert!(
        !offering
            .advance(&mut session, benefit.clone(), counsel.clone())
            .landed(),
        "a receipt substituted from another proof session cannot authorize the route"
    );
    assert_eq!(session.read_var("depth"), 0);

    let mut corrupt = honest.clone();
    let at = corrupt.len() - 1;
    corrupt[at] ^= 1;
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_PREFERENCE_OPERATION,
                &corrupt,
                DreggIdentity("intruder".to_string()),
            )
            .is_err()
    );
    assert!(session.private_preference_decision().is_none());

    let landed = offering
        .invoke_binary_operation(
            &mut session,
            PRIVATE_PREFERENCE_OPERATION,
            &honest,
            first_uploader.clone(),
        )
        .unwrap();
    assert_eq!(landed.operation, PRIVATE_PREFERENCE_OPERATION);
    assert_eq!(session.private_preference_decision().unwrap().winner(), 1);
    assert_eq!(
        session.private_preference_actor(),
        Some(&first_uploader),
        "uploader attribution is retained only as provenance"
    );
    assert!(
        offering
            .actions(&session)
            .into_iter()
            .find(|action| action.arg == KP_PRIVATE_COUNSEL_DESCEND as i64)
            .unwrap()
            .enabled,
        "the verified drowned-stair result unlocks the route"
    );
    assert!(
        offering
            .advance(&mut session, benefit, counsel.clone())
            .landed(),
        "Mallory uploading claimant-free proof bytes first must not steal the party consequence"
    );
    assert_eq!(
        session.read_var("depth"),
        2,
        "ordinary descent advances only one"
    );
    let authentic = session.playthrough();
    assert!(
        authentic
            .steps
            .last()
            .unwrap()
            .decision_commitment
            .is_some()
    );
    assert!(offering.verify(&session).verified);

    // This is a fully valid scene receipt chain carrying a DIFFERENT certified
    // commitment. The generic spween verifier accepts it; the dungeon verifier
    // must reject it because it is not the accepted HidingFri result + actual
    // enacting actor.
    let world_seed = ((SEED % 251) + 1) as u8;
    let scene = keep_scene();
    let mut unbound = Driver::start(deploy_keep(world_seed), &scene).unwrap();
    unbound.advance(KP_PRESS_ON).unwrap();
    assert!(
        unbound.advance(KP_PRIVATE_COUNSEL_DESCEND).is_err(),
        "the executor itself refuses the benefit without a same-turn certified commitment"
    );

    let mut substituted = Driver::start(deploy_keep(world_seed), &scene).unwrap();
    substituted.advance(KP_PRESS_ON).unwrap();
    substituted
        .advance_certified(
            KP_PRIVATE_COUNSEL_DESCEND,
            field_from_bytes(b"substituted-private-result"),
        )
        .unwrap();
    let substituted_record = substituted.playthrough();
    assert!(verify(deploy_keep(world_seed), &scene, &substituted_record).is_ok());
    let rejected = offering.verify_record(&session, &substituted_record);
    assert!(
        !rejected.verified,
        "an unrelated certified value must not pass"
    );
    assert!(rejected.detail.contains("substituted result commitment"));

    let before = session.private_preference_decision();
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_PREFERENCE_OPERATION,
                &honest,
                DreggIdentity("replayer".to_string()),
            )
            .is_err()
    );
    assert_eq!(session.private_preference_decision(), before);
}

#[test]
fn private_party_choice_reverifies_from_the_operation_journal_after_restart() {
    let id = SessionId::new("durable-private-party-counsel");
    let proof_session = private_preference_session_for_seed(SEED);
    let honest = prove_private_preference(proof_session, &ballots())
        .unwrap()
        .to_postcard()
        .unwrap();
    let store = InMemoryResumeStore::new();
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(SEED))
        .unwrap();
    host.advance(
        "dungeon",
        &id,
        Action::new("press on", TURN_CHOOSE, KP_PRESS_ON as i64, true),
        DreggIdentity("pathfinder".to_string()),
    )
    .unwrap();
    host.invoke_binary_operation(
        "dungeon",
        &id,
        PRIVATE_PREFERENCE_OPERATION,
        &honest,
        DreggIdentity("guild-counsel".to_string()),
    )
    .unwrap();
    let enacted = host
        .advance(
            "dungeon",
            &id,
            Action::new(
                "take the drowned stair",
                TURN_CHOOSE,
                KP_PRIVATE_COUNSEL_DESCEND as i64,
                true,
            ),
            DreggIdentity("guild-counsel".to_string()),
        )
        .unwrap();
    assert!(enacted.landed());
    assert!(host.verify("dungeon", &id).unwrap().verified);

    let log = store.load("dungeon", &id).unwrap();
    assert_eq!(log.operations.len(), 1);
    assert_eq!(log.operations[0].after_moves, 1);
    assert_eq!(log.moves.len(), 2);
    assert!(log.operations[0].replay_is_canonical_request);
    assert!(log.operations[0].replay_disclosure.contains("no ballot"));
    drop(host);

    let mut reopened = OfferingHost::new().with_resume_store(Box::new(store));
    reopened.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let resumed = reopened.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(resumed[0].1.is_ok(), "{resumed:?}");
    let rendered = format!("{:?}", reopened.render("dungeon", &id).unwrap().0);
    assert!(rendered.contains("the party privately chose #1"));
    assert!(rendered.contains("descend the drowned stair"));
    assert!(rendered.contains("depth 2"));
    assert!(reopened.verify("dungeon", &id).unwrap().verified);

    assert!(
        reopened
            .invoke_binary_operation(
                "dungeon",
                &id,
                PRIVATE_PREFERENCE_OPERATION,
                &honest,
                DreggIdentity("restart-replayer".to_string()),
            )
            .is_err()
    );
}
