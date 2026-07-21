#![cfg(feature = "private-fair-shuffle-operation")]

use dregg_app_framework::field_from_bytes;
use dreggnet_offerings::dungeon::{
    DungeonOffering, PRIVATE_SHUFFLE_COMMIT_OPERATION, PRIVATE_SHUFFLE_PROVE_OPERATION,
    PRIVATE_SHUFFLE_REVEAL_OPERATION, TURN_CHOOSE, encode_private_shuffle_commitment,
    private_fair_shuffle_session_for_seed,
};
use dreggnet_offerings::resume::{InMemoryResumeStore, SessionResumeStore};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingHost, RecordVerify, SessionConfig, SessionId,
};
use dungeon_on_dregg::private_fair_shuffle::{PARTICIPANTS, PreparedFairShuffle};
use dungeon_on_dregg::{
    KP_PRESS_ON, KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE, KP_PRIVATE_SHUFFLE_ODD_INITIATIVE,
    deploy_keep, keep_scene,
};
use spween_dregg::{Driver, verify};

fn actor(participant: usize) -> DreggIdentity {
    DreggIdentity(format!("shuffle-player-{participant}"))
}

fn initiative_for(card: u8) -> usize {
    if card % 2 == 0 {
        KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE
    } else {
        KP_PRIVATE_SHUFFLE_ODD_INITIATIVE
    }
}

#[test]
fn hosted_dungeon_keeps_claimant_free_shuffle_consequences_party_shared() {
    let offering = DungeonOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(0xFA17))
        .expect("dungeon opens");
    assert!(
        offering
            .advance(
                &mut session,
                Action::new("press on", TURN_CHOOSE, KP_PRESS_ON as i64, true),
                DreggIdentity("pathfinder".to_string()),
            )
            .landed()
    );
    let unavailable = Action::new(
        "play fair initiative",
        TURN_CHOOSE,
        KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE as i64,
        true,
    );
    let before_absent = session.receipts_len();
    assert!(
        !offering
            .advance(&mut session, unavailable, actor(6))
            .landed(),
        "no revealed private result means no initiative benefit"
    );
    assert_eq!(session.receipts_len(), before_absent);
    assert_eq!(session.read_var("relic_owner"), 0);
    assert_eq!(session.read_var("depth"), 0);
    let prepared = PreparedFairShuffle::fresh(
        session.private_fair_shuffle_session_id(),
        0,
        [12_345, 1, 2, 3, 4, 5, 6, 7],
    )
    .expect("private deal witness");

    let first = encode_private_shuffle_commitment(0, prepared.participant_commitment(0).unwrap());
    offering
        .invoke_binary_operation(
            &mut session,
            PRIVATE_SHUFFLE_COMMIT_OPERATION,
            &first,
            actor(0),
        )
        .expect("first commitment lands");
    let stolen_seat =
        encode_private_shuffle_commitment(1, prepared.participant_commitment(1).unwrap());
    offering
        .invoke_binary_operation(
            &mut session,
            PRIVATE_SHUFFLE_COMMIT_OPERATION,
            &stolen_seat,
            actor(0),
        )
        .expect("uploader attribution cannot masquerade as a proved seat owner");
    assert!(session.private_fair_shuffle_table().commitments()[1].is_some());

    for participant in 2..PARTICIPANTS {
        let payload = encode_private_shuffle_commitment(
            participant as u8,
            prepared.participant_commitment(participant).unwrap(),
        );
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_SHUFFLE_COMMIT_OPERATION,
                &payload,
                actor(participant),
            )
            .unwrap();
    }

    let receipt = prepared
        .prove_receipt(session.private_fair_shuffle_table())
        .expect("real hiding proof");
    let proof = receipt.to_postcard().unwrap();
    let applied = offering
        .invoke_binary_operation(
            &mut session,
            PRIVATE_SHUFFLE_PROVE_OPERATION,
            &proof,
            DreggIdentity("shuffle-prover".to_string()),
        )
        .expect("accepted proof lands");
    assert!(
        applied
            .public_fields
            .iter()
            .any(|(key, value)| key == "outcome" && value == "accepted")
    );
    assert!(
        session
            .private_fair_shuffle_table()
            .accepted_receipt()
            .is_some()
    );
    assert!(
        !offering
            .advance(
                &mut session,
                Action::new(
                    "play unrevealed initiative",
                    TURN_CHOOSE,
                    KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE as i64,
                    true,
                ),
                actor(6),
            )
            .landed(),
        "an accepted hidden deal without a selective opening grants no public mechanic"
    );

    let opening = prepared.card_opening(6).unwrap().to_postcard().unwrap();
    let revealed = offering
        .invoke_binary_operation(
            &mut session,
            PRIVATE_SHUFFLE_REVEAL_OPERATION,
            &opening,
            actor(5),
        )
        .expect("a valid claimant-free opening lands regardless of who transports it");
    assert!(revealed.public_fields.iter().any(|(key, _)| key == "card"));
    let card = session.private_fair_shuffle_table().revealed_cards()[6].unwrap();
    let initiative = initiative_for(card);
    let wrong_initiative = if initiative == KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE {
        KP_PRIVATE_SHUFFLE_ODD_INITIATIVE
    } else {
        KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE
    };
    let party_enactor = DreggIdentity("party-enactor-with-no-seat-claim".to_string());
    assert!(
        !offering
            .advance(
                &mut session,
                Action::new(
                    "forge the other parity",
                    TURN_CHOOSE,
                    wrong_initiative as i64,
                    true,
                ),
                party_enactor.clone(),
            )
            .landed(),
        "the selectively opened card fixes which banner initiative may claim"
    );
    assert!(
        offering
            .advance(
                &mut session,
                Action::new("play fair initiative", TURN_CHOOSE, initiative as i64, true),
                party_enactor,
            )
            .landed(),
        "commit uploader, opening uploader, and enactor may differ without first-uploader theft"
    );
    assert_eq!(session.read_var("relic_owner"), 1 + (card % 2) as u64);
    assert_eq!(session.read_var("depth"), 1);
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

    let world_seed = ((0xFA17u64 % 251) + 1) as u8;
    let scene = keep_scene();
    let mut unbound = Driver::start(deploy_keep(world_seed), &scene).unwrap();
    unbound.advance(KP_PRESS_ON).unwrap();
    assert!(
        unbound.advance(initiative).is_err(),
        "the executor refuses initiative without a certified carrier"
    );
    let mut substituted = Driver::start(deploy_keep(world_seed), &scene).unwrap();
    substituted.advance(KP_PRESS_ON).unwrap();
    substituted
        .advance_certified(
            initiative,
            field_from_bytes(b"substituted-fair-shuffle-result"),
        )
        .unwrap();
    let substituted_record = substituted.playthrough();
    assert!(verify(deploy_keep(world_seed), &scene, &substituted_record).is_ok());
    let rejected = offering.verify_record(&session, &substituted_record);
    assert!(!rejected.verified);
    assert!(rejected.detail.contains("substituted result commitment"));

    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_SHUFFLE_REVEAL_OPERATION,
                &opening,
                actor(6),
            )
            .is_err(),
        "opening replay is refused"
    );
}

#[test]
fn fair_deal_operation_journal_restores_the_exact_public_protocol_state() {
    const SEED: u64 = 0xFA18;
    let store = InMemoryResumeStore::new();
    let id = SessionId::new("durable-fair-deal");
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(SEED))
        .unwrap();
    assert!(
        host.advance(
            "dungeon",
            &id,
            Action::new("press on", TURN_CHOOSE, KP_PRESS_ON as i64, true),
            DreggIdentity("pathfinder".to_string()),
        )
        .expect("dungeon session exists")
        .landed()
    );

    let prepared = PreparedFairShuffle::fresh(
        private_fair_shuffle_session_for_seed(SEED),
        0,
        [9_999, 1, 2, 3, 4, 5, 6, 7],
    )
    .unwrap();
    let mut mirror = dungeon_on_dregg::private_fair_shuffle::FairShuffleTable::new(
        private_fair_shuffle_session_for_seed(SEED),
    )
    .unwrap();
    for participant in 0..PARTICIPANTS {
        let commitment = prepared.participant_commitment(participant).unwrap();
        mirror.commit(participant, commitment).unwrap();
        host.invoke_binary_operation(
            "dungeon",
            &id,
            PRIVATE_SHUFFLE_COMMIT_OPERATION,
            &encode_private_shuffle_commitment(participant as u8, commitment),
            actor(participant),
        )
        .unwrap();
    }
    let proof = prepared
        .prove_receipt(&mirror)
        .unwrap()
        .to_postcard()
        .unwrap();
    host.invoke_binary_operation(
        "dungeon",
        &id,
        PRIVATE_SHUFFLE_PROVE_OPERATION,
        &proof,
        DreggIdentity("proof-relay".to_string()),
    )
    .unwrap();
    let prepared_opening = prepared.card_opening(3).unwrap();
    let card = prepared_opening.card;
    let opening = prepared_opening.to_postcard().unwrap();
    host.invoke_binary_operation(
        "dungeon",
        &id,
        PRIVATE_SHUFFLE_REVEAL_OPERATION,
        &opening,
        actor(3),
    )
    .unwrap();
    let initiative = initiative_for(card);
    assert!(
        host.advance(
            "dungeon",
            &id,
            Action::new(
                "play durable fair initiative",
                TURN_CHOOSE,
                initiative as i64,
                true,
            ),
            actor(3),
        )
        .expect("dungeon session exists")
        .landed()
    );
    assert!(host.verify("dungeon", &id).unwrap().verified);

    let log = store.load("dungeon", &id).expect("durable operation log");
    assert_eq!(log.operations.len(), PARTICIPANTS + 2);
    assert_eq!(log.moves.len(), 2);
    assert!(
        log.operations
            .iter()
            .all(|operation| operation.after_moves == 1),
        "commit/prove/reveal all landed after entering the hall and before initiative"
    );
    assert!(
        log.operations
            .iter()
            .all(|operation| operation.replay_is_canonical_request)
    );
    drop(host);

    let mut reopened = OfferingHost::new().with_resume_store(Box::new(store));
    reopened.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let resumed = reopened.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(resumed[0].1.is_ok(), "{resumed:?}");
    let render = format!("{:?}", reopened.render("dungeon", &id).unwrap().0);
    assert!(render.contains("accepted attempt 0"));
    assert!(render.contains("1 private card opening(s) landed"));
    assert!(render.contains("depth 1"));
    let expected_banner = if card % 2 == 0 {
        "crown Red Hand"
    } else {
        "crown Blue Hand"
    };
    assert!(render.contains(expected_banner), "{render}");
    assert!(reopened.verify("dungeon", &id).unwrap().verified);
}
