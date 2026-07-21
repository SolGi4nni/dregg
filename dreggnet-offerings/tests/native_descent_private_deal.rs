#![cfg(feature = "private-fair-shuffle-operation")]

//! A bias-free private initiative deal attached to one exact Lean-native
//! Descent head. The producer is intentionally Tier 1: it sees all eight
//! contributions. The offering receives only commitments, a HidingFri receipt,
//! and the fixed seat-zero opening; it never receives the other seven cards.

use dreggnet_offerings::native_descent::{
    NATIVE_DESCENT_PRIVATE_DEAL_OPERATION, NativeDescentOffering, NativeDescentSession,
    encode_native_descent_private_deal, native_descent_private_deal_proof_session,
};
use dreggnet_offerings::resume::{InMemoryResumeStore, SessionResumeStore};
use dreggnet_offerings::{Action, DreggIdentity, Offering, OfferingHost, SessionConfig, SessionId};
use dungeon_on_dregg::descent::{DELVE, SMITE};
use dungeon_on_dregg::private_fair_shuffle::{FairShuffleTable, PARTICIPANTS, PreparedFairShuffle};

const SEED: u64 = 0xFA17_D35C;
const ROOT_OFFSET: usize = 8 + 1 + 1 + 8;

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn action(actions: Vec<Action>, turn: &str) -> Action {
    actions
        .into_iter()
        .find(|candidate| candidate.turn == turn && candidate.arg == 0)
        .unwrap_or_else(|| panic!("missing native Descent action {turn}"))
}

fn land(
    offering: &NativeDescentOffering,
    session: &mut NativeDescentSession,
    who: &DreggIdentity,
    turn: &str,
) {
    let move_ = action(offering.actions(session), turn);
    assert!(move_.enabled, "{turn} must be enabled on the driven line");
    assert!(offering.advance(session, move_, who.clone()).landed());
}

fn prove_deal(session: &NativeDescentSession) -> (Vec<u8>, u8) {
    let context = session
        .private_operation_context()
        .expect("a landed native move binds the player and exact head");
    let prepared = PreparedFairShuffle::fresh(
        native_descent_private_deal_proof_session(&context),
        0,
        [12_345, 1, 2, 3, 4, 5, 6, 7],
    )
    .expect("accepted private-deal witness");
    let commitments = std::array::from_fn(|participant| {
        prepared
            .participant_commitment(participant)
            .expect("fixed participant is in range")
    });
    let mut table = FairShuffleTable::new(native_descent_private_deal_proof_session(&context))
        .expect("proof session is canonical");
    for (participant, commitment) in commitments.iter().copied().enumerate() {
        table.commit(participant, commitment).unwrap();
    }
    let receipt = prepared
        .prove_receipt(&table)
        .expect("real HidingFri fair-deal proof");
    let opening = prepared.card_opening(0).expect("fixed seat zero opens");
    let card = opening.card;
    (
        encode_native_descent_private_deal(&context, commitments, &receipt, opening)
            .expect("canonical exact-head envelope"),
        card,
    )
}

#[test]
fn native_private_deal_is_exact_head_bound_minimally_disclosed_and_restart_replayed() {
    let offering = NativeDescentOffering::new();
    let alice = actor("alice-initiative");
    let bob = actor("bob-initiative");
    let id = SessionId::new("native-private-deal");
    let store = InMemoryResumeStore::new();
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register("descent", "The Lean-native Descent", offering);
    host.open_session("descent", id.clone(), SessionConfig::with_seed(SEED))
        .unwrap();

    assert!(host.binary_operations("descent", &id).unwrap().is_empty());
    let delve = action(host.actions("descent", &id).unwrap(), DELVE);
    assert!(
        host.advance("descent", &id, delve, alice.clone())
            .unwrap()
            .landed()
    );

    let mut mirror = offering.open(SessionConfig::with_seed(SEED)).unwrap();
    land(&offering, &mut mirror, &alice, DELVE);
    let (payload, expected_card) = prove_deal(&mirror);
    let descriptor = host
        .binary_operations("descent", &id)
        .unwrap()
        .into_iter()
        .find(|descriptor| descriptor.name == NATIVE_DESCENT_PRIVATE_DEAL_OPERATION)
        .expect("private initiative is discoverable after actor binding");
    assert!(descriptor.disclosure.contains("fixed seat-zero"));
    assert!(descriptor.disclosure.contains("Tier-1 local producer"));
    assert!(
        descriptor
            .disclosure
            .contains("not distributed private-input")
    );

    let truncated = &payload[..payload.len() - 1];
    assert!(
        host.invoke_binary_operation(
            "descent",
            &id,
            NATIVE_DESCENT_PRIVATE_DEAL_OPERATION,
            truncated,
            alice.clone(),
        )
        .is_err()
    );
    let mut wrong_root = payload.clone();
    wrong_root[ROOT_OFFSET] ^= 1;
    let cross_root = host
        .invoke_binary_operation(
            "descent",
            &id,
            NATIVE_DESCENT_PRIVATE_DEAL_OPERATION,
            &wrong_root,
            alice.clone(),
        )
        .expect_err("different native journal root refuses");
    assert!(cross_root.to_string().contains("wrong native Descent"));
    let cross_actor = host
        .invoke_binary_operation(
            "descent",
            &id,
            NATIVE_DESCENT_PRIVATE_DEAL_OPERATION,
            &payload,
            bob,
        )
        .expect_err("different authenticated submitter refuses");
    assert!(cross_actor.to_string().contains("bound to actor"));
    assert!(
        store.load("descent", &id).unwrap().operations.is_empty(),
        "every hostile refusal is mutation-free"
    );

    let applied = host
        .invoke_binary_operation(
            "descent",
            &id,
            NATIVE_DESCENT_PRIVATE_DEAL_OPERATION,
            &payload,
            alice.clone(),
        )
        .expect("the exact actor/head deal lands");
    let public_names: Vec<&str> = applied
        .public_fields
        .iter()
        .map(|(name, _)| name.as_str())
        .collect();
    assert_eq!(
        public_names,
        [
            "actor",
            "revision",
            "root",
            "proofSession",
            "dealRoot",
            "initiativeSeat",
            "initiativeCard",
        ],
        "the public outcome does not disclose contributions, rank, or seven other cards"
    );
    assert!(
        applied.public_fields.iter().any(|(name, value)| {
            name == "initiativeCard" && value == &expected_card.to_string()
        })
    );

    assert!(
        host.invoke_binary_operation(
            "descent",
            &id,
            NATIVE_DESCENT_PRIVATE_DEAL_OPERATION,
            &payload,
            alice.clone(),
        )
        .is_err(),
        "the one-shot deal cannot replay"
    );
    assert_eq!(store.load("descent", &id).unwrap().operations.len(), 1);

    let smite = action(host.actions("descent", &id).unwrap(), SMITE);
    assert!(
        host.advance("descent", &id, smite, alice.clone())
            .unwrap()
            .landed()
    );
    let stale_id = SessionId::new("native-private-deal-stale");
    host.open_session("descent", stale_id.clone(), SessionConfig::with_seed(SEED))
        .unwrap();
    let delve = action(host.actions("descent", &stale_id).unwrap(), DELVE);
    assert!(
        host.advance("descent", &stale_id, delve, alice.clone())
            .unwrap()
            .landed()
    );
    let smite = action(host.actions("descent", &stale_id).unwrap(), SMITE);
    assert!(
        host.advance("descent", &stale_id, smite, alice.clone())
            .unwrap()
            .landed()
    );
    let stale = host
        .invoke_binary_operation(
            "descent",
            &stale_id,
            NATIVE_DESCENT_PRIVATE_DEAL_OPERATION,
            &payload,
            alice.clone(),
        )
        .expect_err("revision-one envelope is stale at revision two");
    assert!(stale.to_string().contains("stale"), "{stale}");

    assert!(host.verify("descent", &id).unwrap().verified);
    let log = store.load("descent", &id).unwrap();
    assert_eq!(log.operations.len(), 1);
    assert!(log.operations[0].replay_is_canonical_request);
    assert_eq!(log.operations[0].after_moves, 1);
    drop(host);

    let mut reopened = OfferingHost::new().with_resume_store(Box::new(store));
    reopened.register("descent", "The Lean-native Descent", offering);
    let resumed = reopened.resume_all();
    assert!(
        resumed
            .iter()
            .any(|(_, result)| result.as_ref().is_ok_and(|resumed_id| resumed_id == &id)),
        "the durable operation timeline fresh-reverifies the proof: {resumed:?}"
    );
    let rendered = format!("{:?}", reopened.render("descent", &id).unwrap().0);
    assert!(rendered.contains("Shielded initiative deal"), "{rendered}");
    assert!(rendered.contains(&format!("initiative card {expected_card}")));
    assert!(reopened.verify("descent", &id).unwrap().verified);
}

#[test]
fn native_private_deal_from_another_root_refuses_record_restart() {
    let offering = NativeDescentOffering::new();
    let alice = actor("alice-cross-root");
    let mut first = offering.open(SessionConfig::with_seed(SEED)).unwrap();
    land(&offering, &mut first, &alice, DELVE);
    let (payload, _) = prove_deal(&first);
    offering
        .invoke_binary_operation(
            &mut first,
            NATIVE_DESCENT_PRIVATE_DEAL_OPERATION,
            &payload,
            alice.clone(),
        )
        .unwrap();

    let mut other = offering.open(SessionConfig::with_seed(SEED + 1)).unwrap();
    land(&offering, &mut other, &alice, DELVE);
    let mut tampered = other.export_record();
    tampered.private_deal = first.export_record().private_deal;
    let error = match offering.resume_record(&tampered) {
        Ok(_) => panic!("deal from another native root must refuse restart"),
        Err(error) => error,
    };
    assert!(
        error.to_string().contains("exact recorded native root"),
        "{error}"
    );
}

#[test]
fn native_private_deal_rejects_nonfixed_selective_opening_without_mutation() {
    let offering = NativeDescentOffering::new();
    let alice = actor("alice-fixed-seat");
    let mut session = offering.open(SessionConfig::with_seed(SEED)).unwrap();
    land(&offering, &mut session, &alice, DELVE);
    let context = session.private_operation_context().unwrap();
    let proof_session = native_descent_private_deal_proof_session(&context);
    let prepared =
        PreparedFairShuffle::fresh(proof_session, 0, [12_345, 1, 2, 3, 4, 5, 6, 7]).unwrap();
    let commitments =
        std::array::from_fn(|participant| prepared.participant_commitment(participant).unwrap());
    let mut table = FairShuffleTable::new(proof_session).unwrap();
    for participant in 0..PARTICIPANTS {
        table.commit(participant, commitments[participant]).unwrap();
    }
    let receipt = prepared.prove_receipt(&table).unwrap();
    let seat_one = prepared.card_opening(1).unwrap();
    let payload = encode_native_descent_private_deal(&context, commitments, &receipt, seat_one)
        .expect("encoding alone preserves the claimed opening");
    let error = offering
        .invoke_binary_operation(
            &mut session,
            NATIVE_DESCENT_PRIVATE_DEAL_OPERATION,
            &payload,
            alice,
        )
        .expect_err("after-the-fact choice of a favorable seat refuses");
    assert!(error.to_string().contains("fixed seat 0"), "{error}");
    assert!(session.private_deal().is_none());
}
