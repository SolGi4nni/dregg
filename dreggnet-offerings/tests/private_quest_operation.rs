//! An external prover reduces a hidden semantic quest while the hosted game
//! retains and restart-replays only the pinned public proof history.

#![cfg(feature = "private-quest-operation")]

use dreggnet_offerings::dungeon::{
    DungeonOffering, PRIVATE_QUEST_OPERATION, private_quest_session_for_seed,
};
use dreggnet_offerings::resume::{InMemoryResumeStore, SessionResumeStore};
use dreggnet_offerings::{DreggIdentity, OfferingHost, SessionConfig, SessionId};
use dungeon_on_dregg::private_quest::{
    PrivateQuestMove, PrivateQuestRaid, encode_private_quest_receipt,
};

#[test]
fn opaque_quest_reductions_land_atomically_and_survive_restart() {
    const SEED: u64 = 0x5155_4553;
    let id = SessionId::new("durable-private-quest");
    let session = private_quest_session_for_seed(SEED);

    // The producer owns every graph edge, match, selected rule, and blinding.
    // The host receives only these two public statements + opaque proofs.
    let mut producer = PrivateQuestRaid::new(session).expect("private quest producer");
    let first = producer
        .advance(producer.command(PrivateQuestMove::ScoutVeiledRoute))
        .expect("first hidden reduction proves");
    let first_bytes = encode_private_quest_receipt(&first).unwrap();
    let second = producer
        .advance(producer.command(PrivateQuestMove::BreakWardenSeal))
        .expect("second hidden reduction proves");
    let second_bytes = encode_private_quest_receipt(&second).unwrap();
    assert!(producer.is_complete());

    let store = InMemoryResumeStore::new();
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(SEED))
        .unwrap();
    assert!(
        host.binary_operations("dungeon", &id)
            .unwrap()
            .iter()
            .any(|operation| operation.name == PRIVATE_QUEST_OPERATION)
    );

    let mut corrupt = first_bytes.clone();
    let last = corrupt.len() - 1;
    corrupt[last] ^= 1;
    assert!(
        host.invoke_binary_operation(
            "dungeon",
            &id,
            PRIVATE_QUEST_OPERATION,
            &corrupt,
            DreggIdentity("forger".to_string()),
        )
        .is_err()
    );
    assert_eq!(store.load("dungeon", &id).unwrap().operations.len(), 0);

    let first_result = host
        .invoke_binary_operation(
            "dungeon",
            &id,
            PRIVATE_QUEST_OPERATION,
            &first_bytes,
            DreggIdentity("scout".to_string()),
        )
        .expect("first receipt lands");
    assert!(
        first_result
            .public_fields
            .iter()
            .any(|(key, value)| key == "index" && value == "0")
    );

    // A linked history, not a set: replay and reordering refuse without adding
    // an operation-journal entry.
    assert!(
        host.invoke_binary_operation(
            "dungeon",
            &id,
            PRIVATE_QUEST_OPERATION,
            &first_bytes,
            DreggIdentity("replayer".to_string()),
        )
        .is_err()
    );
    assert_eq!(store.load("dungeon", &id).unwrap().operations.len(), 1);

    host.invoke_binary_operation(
        "dungeon",
        &id,
        PRIVATE_QUEST_OPERATION,
        &second_bytes,
        DreggIdentity("warden-breaker".to_string()),
    )
    .expect("second linked receipt lands");
    assert!(
        host.invoke_binary_operation(
            "dungeon",
            &id,
            PRIVATE_QUEST_OPERATION,
            &second_bytes,
            DreggIdentity("third-step-forger".to_string()),
        )
        .is_err()
    );
    let rendered = format!("{:?}", host.render("dungeon", &id).unwrap().0);
    assert!(rendered.contains("Private semantic quest"));
    assert!(rendered.contains("2/2 opaque reductions verified"));
    assert!(rendered.contains("2 attributed uploader(s)"));

    let log = store.load("dungeon", &id).expect("durable quest journal");
    assert_eq!(log.operations.len(), 2);
    assert!(
        log.operations
            .iter()
            .all(|operation| operation.replay_is_canonical_request)
    );
    drop(host);

    // Boot creates a fresh dungeon, re-verifies both opaque proofs in timeline
    // order, and reconstructs the exact public continuation. No hidden graph is
    // serialized into the resume store.
    let mut reopened = OfferingHost::new().with_resume_store(Box::new(store));
    reopened.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let resumed = reopened.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(resumed[0].1.is_ok(), "{resumed:?}");
    let rendered = format!("{:?}", reopened.render("dungeon", &id).unwrap().0);
    assert!(rendered.contains("2/2 opaque reductions verified"));
    assert!(rendered.contains("2 attributed uploader(s)"));
}
