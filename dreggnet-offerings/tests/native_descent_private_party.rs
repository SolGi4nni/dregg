#![cfg(all(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]

//! Private-party mechanics attached to one exact Lean-native Descent head.
//! The tests drive the generic binary-operation seam, including its durable
//! replay timeline, rather than calling the proof verifiers as a substitute
//! for the offering boundary.

use dreggnet_offerings::native_descent::{
    NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION, NATIVE_DESCENT_PRIVATE_RAID_OPERATION,
    NativeDescentOffering, NativeDescentSession, encode_native_descent_private_preference,
    encode_native_descent_private_raid, native_descent_private_preference_proof_session,
    native_descent_private_raid_proof_session,
};
use dreggnet_offerings::resume::{InMemoryResumeStore, SessionResumeStore};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingHost, RecordVerify, ResumeError, SessionConfig,
    SessionId,
};
use dungeon_on_dregg::descent::{DELVE, SMITE};
use dungeon_on_dregg::private_preference::{PrivateBallot, prove_private_preference};
use dungeon_on_dregg::private_raid::{RaidRole, prove_private_assignment};

const SEED: u64 = 0xD35CE17;
const ROOT_OFFSET: usize = 8 + 1 + 1 + 8;

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn ballots() -> [PrivateBallot; 4] {
    [
        PrivateBallot::try_new([3, 2, 0, 1]).unwrap(),
        PrivateBallot::try_new([2, 3, 0, 1]).unwrap(),
        PrivateBallot::try_new([0, 3, 2, 1]).unwrap(),
        PrivateBallot::try_new([1, 2, 3, 0]).unwrap(),
    ]
}

fn raid_scores() -> [[u8; 4]; 4] {
    [[0, 3, 0, 0], [3, 0, 0, 0], [0, 0, 3, 0], [0, 0, 0, 3]]
}

fn action(actions: Vec<Action>, turn: &str) -> Action {
    actions
        .into_iter()
        .find(|candidate| candidate.turn == turn && candidate.arg == 0)
        .unwrap_or_else(|| panic!("missing enabled native Descent action {turn}"))
}

fn land_direct(
    offering: &NativeDescentOffering,
    session: &mut NativeDescentSession,
    who: &DreggIdentity,
    turn: &str,
) {
    let move_ = action(offering.actions(session), turn);
    assert!(move_.enabled, "{turn} must be enabled on the driven line");
    assert!(
        offering.advance(session, move_, who.clone()).landed(),
        "{turn} lands through the native executor"
    );
}

#[test]
fn private_party_proofs_are_exact_head_bound_and_restart_replayed() {
    let offering = NativeDescentOffering::new();
    let alice = actor("alice-cipherclerk");
    let bob = actor("bob-cipherclerk");
    let id = SessionId::new("native-descent-private-party");
    let store = InMemoryResumeStore::new();
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register("descent", "The Lean-native Descent", offering);
    host.open_session("descent", id.clone(), SessionConfig::with_seed(SEED))
        .expect("native session opens");

    assert!(
        host.binary_operations("descent", &id)
            .expect("session exists")
            .is_empty(),
        "an unclaimed run has no authenticated private-operation context"
    );

    let mut mirror = offering
        .open(SessionConfig::with_seed(SEED))
        .expect("deterministic mirror opens");
    let delve = action(host.actions("descent", &id).unwrap(), DELVE);
    assert!(
        host.advance("descent", &id, delve, alice.clone())
            .expect("session exists")
            .landed()
    );
    land_direct(&offering, &mut mirror, &alice, DELVE);
    let context = mirror
        .private_operation_context()
        .expect("the first landed move binds the exact head");
    assert_eq!(context.revision, 1);

    let descriptors = host
        .binary_operations("descent", &id)
        .expect("private operations are discoverable");
    assert_eq!(descriptors.len(), 2);
    for descriptor in &descriptors {
        assert!(descriptor.title.contains("revision 1"));
        assert!(descriptor.title.contains("alice-cipherclerk"));
        assert!(descriptor.disclosure.contains("exact revision"));
        assert!(descriptor.disclosure.contains("exact journal root"));
    }

    let preference = prove_private_preference(
        native_descent_private_preference_proof_session(&context),
        &ballots(),
    )
    .expect("private preference proves");
    let preference_payload = encode_native_descent_private_preference(&context, &preference)
        .expect("preference context envelope");
    let raid = prove_private_assignment(
        native_descent_private_raid_proof_session(&context),
        raid_scores(),
        [[true; 4]; 4],
    )
    .expect("private raid assignment proves");
    let raid_payload =
        encode_native_descent_private_raid(&context, &raid).expect("raid context envelope");

    let truncated = &preference_payload[..preference_payload.len() - 1];
    let malformed = host
        .invoke_binary_operation(
            "descent",
            &id,
            NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION,
            truncated,
            alice.clone(),
        )
        .expect_err("truncated envelope refuses");
    assert!(malformed.to_string().contains("malformed"), "{malformed}");

    let mut wrong_root = preference_payload.clone();
    wrong_root[ROOT_OFFSET] ^= 1;
    let wrong_root_error = host
        .invoke_binary_operation(
            "descent",
            &id,
            NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION,
            &wrong_root,
            alice.clone(),
        )
        .expect_err("a different exact root refuses before proof acceptance");
    assert!(
        wrong_root_error
            .to_string()
            .contains("wrong native Descent"),
        "{wrong_root_error}"
    );

    let wrong_actor = host
        .invoke_binary_operation(
            "descent",
            &id,
            NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION,
            &preference_payload,
            bob,
        )
        .expect_err("a different authenticated actor cannot submit Alice's receipt");
    assert!(
        wrong_actor.to_string().contains("bound to actor"),
        "{wrong_actor}"
    );
    assert!(store.load("descent", &id).unwrap().operations.is_empty());

    let preference_result = host
        .invoke_binary_operation(
            "descent",
            &id,
            NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION,
            &preference_payload,
            alice.clone(),
        )
        .expect("the exact preference head lands");
    assert_eq!(
        preference_result.operation,
        NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION
    );
    assert!(
        preference_result
            .public_fields
            .iter()
            .any(|(name, value)| name == "revision" && value == "1")
    );
    assert!(
        offering
            .invoke_binary_operation(
                &mut mirror,
                NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION,
                &preference_payload,
                alice.clone(),
            )
            .is_ok()
    );

    let raid_result = host
        .invoke_binary_operation(
            "descent",
            &id,
            NATIVE_DESCENT_PRIVATE_RAID_OPERATION,
            &raid_payload,
            alice.clone(),
        )
        .expect("the exact raid assignment lands");
    assert_eq!(raid_result.operation, NATIVE_DESCENT_PRIVATE_RAID_OPERATION);
    assert!(
        offering
            .invoke_binary_operation(
                &mut mirror,
                NATIVE_DESCENT_PRIVATE_RAID_OPERATION,
                &raid_payload,
                alice.clone(),
            )
            .is_ok()
    );
    assert_eq!(mirror.private_preference().unwrap().decision().winner(), 1);
    assert_eq!(
        mirror.private_raid().unwrap().assignment().roles(),
        [
            RaidRole::Striker,
            RaidRole::Bulwark,
            RaidRole::Mender,
            RaidRole::Pathfinder,
        ]
    );
    assert!(
        host.binary_operations("descent", &id).unwrap().is_empty(),
        "both one-shot private slots are filled"
    );

    let smite = action(host.actions("descent", &id).unwrap(), SMITE);
    assert!(
        host.advance("descent", &id, smite, alice.clone())
            .unwrap()
            .landed()
    );
    land_direct(&offering, &mut mirror, &alice, SMITE);
    let stale = host
        .invoke_binary_operation(
            "descent",
            &id,
            NATIVE_DESCENT_PRIVATE_RAID_OPERATION,
            &raid_payload,
            alice.clone(),
        )
        .expect_err("the revision-one envelope is stale at revision two");
    assert!(stale.to_string().contains("stale"), "{stale}");

    let report = host.verify("descent", &id).expect("session verifies");
    assert!(report.verified, "{}", report.detail);
    let rendered = format!("{:?}", host.render("descent", &id).unwrap().0);
    assert!(rendered.contains("Shielded party preference"), "{rendered}");
    assert!(rendered.contains("Shielded raid assignment"), "{rendered}");

    let record = offering.export_record(&mirror);
    let replayed = offering
        .resume_record(&record)
        .expect("the native public record reverifies both opaque receipts");
    assert_eq!(
        replayed.private_preference().unwrap().receipt_id(),
        mirror.private_preference().unwrap().receipt_id()
    );
    assert_eq!(
        replayed.private_raid().unwrap().receipt_id(),
        mirror.private_raid().unwrap().receipt_id()
    );

    let before_restart = host.commitment("descent", &id).unwrap();
    let log = store
        .load("descent", &id)
        .expect("durable operation timeline");
    assert_eq!(log.moves.len(), 2);
    assert_eq!(log.operations.len(), 2);
    assert!(
        log.operations
            .iter()
            .all(|operation| operation.after_moves == 1)
    );
    assert!(
        log.operations
            .iter()
            .all(|operation| operation.replay_is_canonical_request)
    );
    drop(host);

    let mut restarted = OfferingHost::new().with_resume_store(Box::new(store));
    restarted.register("descent", "The Lean-native Descent", offering);
    let resumed = restarted.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(resumed[0].1.is_ok(), "{resumed:?}");
    assert_eq!(
        restarted.commitment("descent", &id).unwrap(),
        before_restart
    );
    assert!(restarted.verify("descent", &id).unwrap().verified);

    let mut tampered = log;
    tampered.operations[0].replay_material[ROOT_OFFSET] ^= 1;
    let digest = *blake3::hash(&tampered.operations[0].replay_material).as_bytes();
    tampered.operations[0].payload_digest = digest;
    tampered.operations[0].replay_digest = digest;
    let mut rejecting = OfferingHost::new();
    rejecting.register("descent", "The Lean-native Descent", offering);
    match rejecting.resume(&tampered) {
        Err(ResumeError::OperationRefused { index: 0, reason }) => {
            assert!(reason.contains("wrong native Descent"), "{reason}")
        }
        other => panic!("wrong-root restart must fail closed, got {other:?}"),
    }
}
