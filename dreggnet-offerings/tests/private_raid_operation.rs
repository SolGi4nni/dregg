#![cfg(feature = "private-raid-operation")]

use dregg_app_framework::field_from_bytes;
use dreggnet_offerings::dungeon::{DungeonOffering, PRIVATE_RAID_OPERATION, TURN_CHOOSE};
use dreggnet_offerings::resume::{InMemoryResumeStore, SessionResumeStore};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingHost, RecordVerify, SessionConfig, SessionId,
};
use dungeon_on_dregg::private_raid::{RaidPartyAssignment, RaidRole, prove_private_assignment};
use dungeon_on_dregg::{
    KP_DESCEND, KP_PRESS_ON, KP_PRIVATE_RAID_MENDER_CHOICES, KP_TRADE_BLOWS, deploy_keep,
    keep_scene,
};
use spween_dregg::{Driver, verify};

fn scores() -> [[u8; 4]; 4] {
    [[0, 3, 0, 0], [3, 0, 0, 0], [0, 0, 3, 0], [0, 0, 0, 3]]
}

fn mender_choice(assignment: RaidPartyAssignment) -> usize {
    let seat = assignment
        .roles()
        .iter()
        .position(|role| *role == RaidRole::Mender)
        .expect("assignment is a role permutation");
    KP_PRIVATE_RAID_MENDER_CHOICES[seat]
}

fn choose(label: &str, index: usize) -> Action {
    Action::new(label, TURN_CHOOSE, index as i64, true)
}

#[test]
fn hosted_dungeon_accepts_one_real_private_raid_proof_atomically() {
    let offering = DungeonOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(31_337))
        .expect("dungeon opens");
    let proof_session = session.private_raid_session_id();
    let pathfinder = DreggIdentity("pathfinder".to_string());
    assert!(
        offering
            .advance(
                &mut session,
                choose("trade one survivable blow", KP_TRADE_BLOWS),
                DreggIdentity("vanguard".to_string()),
            )
            .landed()
    );
    assert!(
        offering
            .advance(
                &mut session,
                choose("press on", KP_PRESS_ON),
                pathfinder.clone(),
            )
            .landed()
    );
    assert!(
        offering
            .advance(&mut session, choose("descend", KP_DESCEND), pathfinder,)
            .landed()
    );
    assert_eq!(session.read_var("hp"), 30);
    let before_absent = session.receipts_len();
    assert!(
        !offering
            .advance(
                &mut session,
                choose(
                    "invent a Mender assignment",
                    KP_PRIVATE_RAID_MENDER_CHOICES[2],
                ),
                DreggIdentity("party-captain".to_string()),
            )
            .landed()
    );
    assert_eq!(session.receipts_len(), before_absent);
    assert_eq!(session.read_var("hp"), 30);
    // Other independently feature-gated private mechanics may share this
    // offering.  The raid test asserts discovery by stable identity instead of
    // assuming it is the only binary operation installed.
    assert!(
        offering
            .binary_operations(&session)
            .iter()
            .any(|operation| operation.name == PRIVATE_RAID_OPERATION)
    );

    let receipt = prove_private_assignment(proof_session, scores(), [[true; 4]; 4])
        .expect("private assignment proves");
    let honest = receipt.to_postcard().expect("canonical receipt");

    let mut corrupt = honest.clone();
    let at = corrupt.len() - 1;
    corrupt[at] ^= 1;
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_RAID_OPERATION,
                &corrupt,
                DreggIdentity("mallory".to_string()),
            )
            .is_err()
    );
    assert!(session.private_raid_assignment().is_none());
    assert!(session.private_raid_actor().is_none());

    let wrong_session = prove_private_assignment(proof_session + 1, scores(), [[true; 4]; 4])
        .unwrap()
        .to_postcard()
        .unwrap();
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_RAID_OPERATION,
                &wrong_session,
                DreggIdentity("mallory".to_string()),
            )
            .is_err()
    );
    assert!(session.private_raid_assignment().is_none());

    let applied = offering
        .invoke_binary_operation(
            &mut session,
            PRIVATE_RAID_OPERATION,
            &honest,
            DreggIdentity("party-captain".to_string()),
        )
        .expect("verified assignment lands");
    assert_eq!(applied.operation, PRIVATE_RAID_OPERATION);
    let assignment = session
        .private_raid_assignment()
        .expect("assignment stored");
    assert_eq!(
        assignment.roles(),
        [
            RaidRole::Striker,
            RaidRole::Bulwark,
            RaidRole::Mender,
            RaidRole::Pathfinder,
        ]
    );
    assert_eq!(
        session.private_raid_actor(),
        Some(&DreggIdentity("party-captain".to_string()))
    );

    let landed = assignment;
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_RAID_OPERATION,
                &honest,
                DreggIdentity("replayer".to_string()),
            )
            .is_err()
    );
    assert_eq!(session.private_raid_assignment(), Some(landed));
    assert_eq!(
        session.private_raid_actor(),
        Some(&DreggIdentity("party-captain".to_string()))
    );

    let exact_choice = mender_choice(assignment);
    let wrong_choice = KP_PRIVATE_RAID_MENDER_CHOICES
        .iter()
        .copied()
        .find(|choice| *choice != exact_choice)
        .unwrap();
    assert!(
        !offering
            .advance(
                &mut session,
                choose("claim the wrong role", wrong_choice),
                DreggIdentity("party-captain".to_string()),
            )
            .landed(),
        "the assignment's public role permutation selects one exact Mender seat"
    );
    assert!(
        !offering
            .advance(
                &mut session,
                choose("steal the Mender recovery", exact_choice),
                DreggIdentity("mallory".to_string()),
            )
            .landed(),
        "a different actor cannot carry the assignment submitter's benefit"
    );
    assert_eq!(session.read_var("hp"), 30);

    assert!(
        offering
            .advance(
                &mut session,
                choose("apply the assigned Mender recovery", exact_choice),
                DreggIdentity("party-captain".to_string()),
            )
            .landed()
    );
    assert_eq!(session.read_var("hp"), 50);
    assert_eq!(session.read_var("raid_mending_used"), 1);
    assert!(
        session
            .playthrough()
            .steps
            .last()
            .unwrap()
            .decision_commitment
            .is_some()
    );
    assert!(offering.verify(&session).verified);
    let before_reuse = session.receipts_len();
    assert!(
        !offering
            .advance(
                &mut session,
                choose("reuse the assigned Mender", exact_choice),
                DreggIdentity("party-captain".to_string()),
            )
            .landed()
    );
    assert_eq!(session.receipts_len(), before_reuse);
    assert_eq!(session.read_var("hp"), 50);

    let world_seed = ((31_337u64 % 251) + 1) as u8;
    let scene = keep_scene();
    let drive_to_sanctum = |driver: &mut Driver<'_>| {
        driver.advance(KP_TRADE_BLOWS).unwrap();
        driver.advance(KP_PRESS_ON).unwrap();
        driver.advance(KP_DESCEND).unwrap();
    };
    let mut unbound = Driver::start(deploy_keep(world_seed), &scene).unwrap();
    drive_to_sanctum(&mut unbound);
    assert!(
        unbound.advance(exact_choice).is_err(),
        "the executor refuses the role benefit without a certified carrier"
    );
    let mut substituted = Driver::start(deploy_keep(world_seed), &scene).unwrap();
    drive_to_sanctum(&mut substituted);
    substituted
        .advance_certified(
            exact_choice,
            field_from_bytes(b"substituted-private-raid-assignment"),
        )
        .unwrap();
    let substituted_record = substituted.playthrough();
    assert!(verify(deploy_keep(world_seed), &scene, &substituted_record).is_ok());
    let rejected = offering.verify_record(&session, &substituted_record);
    assert!(!rejected.verified);
    assert!(rejected.detail.contains("substituted result commitment"));
}

#[test]
fn private_raid_role_benefit_restarts_from_its_exact_operation_timeline() {
    const SEED: u64 = 31_338;
    let id = SessionId::new("durable-private-raid-mender");
    let store = InMemoryResumeStore::new();
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(SEED))
        .unwrap();
    for (label, choice, actor) in [
        ("trade one blow", KP_TRADE_BLOWS, "vanguard"),
        ("press on", KP_PRESS_ON, "pathfinder"),
        ("descend", KP_DESCEND, "pathfinder"),
    ] {
        assert!(
            host.advance(
                "dungeon",
                &id,
                choose(label, choice),
                DreggIdentity(actor.to_string()),
            )
            .expect("dungeon session exists")
            .landed()
        );
    }

    let receipt = prove_private_assignment(
        ((SEED % 2_013_265_920) + 1) as u32,
        scores(),
        [[true; 4]; 4],
    )
    .unwrap();
    let mender_seat = receipt
        .statement()
        .roles
        .iter()
        .position(|role| *role == RaidRole::Mender as u8)
        .expect("public assignment is a role permutation");
    let exact_choice = KP_PRIVATE_RAID_MENDER_CHOICES[mender_seat];
    host.invoke_binary_operation(
        "dungeon",
        &id,
        PRIVATE_RAID_OPERATION,
        &receipt.to_postcard().unwrap(),
        DreggIdentity("party-captain".to_string()),
    )
    .unwrap();
    assert!(
        host.advance(
            "dungeon",
            &id,
            choose("apply durable Mender recovery", exact_choice),
            DreggIdentity("party-captain".to_string()),
        )
        .unwrap()
        .landed()
    );
    assert!(host.verify("dungeon", &id).unwrap().verified);

    let log = store.load("dungeon", &id).expect("durable raid journal");
    assert_eq!(log.moves.len(), 4);
    assert_eq!(log.operations.len(), 1);
    assert_eq!(log.operations[0].after_moves, 3);
    assert!(log.operations[0].replay_is_canonical_request);
    drop(host);

    let mut reopened = OfferingHost::new().with_resume_store(Box::new(store));
    reopened.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let resumed = reopened.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(resumed[0].1.is_ok(), "{resumed:?}");
    let render = format!("{:?}", reopened.render("dungeon", &id).unwrap().0);
    assert!(render.contains("HP 50"), "{render}");
    assert!(render.contains("Mender"), "{render}");
    assert!(reopened.verify("dungeon", &id).unwrap().verified);
}
