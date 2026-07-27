//! Chutes narration through the same canonical binary-operation host used by private proofs.
//!
//! The provider output is data, never authority: exact consent + exact closed-command parsing
//! precede one ordinary executor turn, and durable replay re-runs that same operation.

use dreggnet_offerings::chutes_consent::CHUTES_CONSENT_WIRE;
use dreggnet_offerings::dungeon::DungeonOffering;
use dreggnet_offerings::dungeon::narrated::{CHUTES_NARRATED_OPERATION, ChutesNarratedRequest};
use dreggnet_offerings::resume::{InMemoryResumeStore, SessionResumeStore};
use dreggnet_offerings::{DreggIdentity, OfferingHost, SessionConfig, SessionId};

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn request(output: &str) -> Vec<u8> {
    ChutesNarratedRequest::new(
        "deepseek-ai/DeepSeek-V3",
        50_000,
        12_345,
        CHUTES_CONSENT_WIRE,
        output,
    )
    .expect("canonical explicitly consented provider result")
    .encode()
    .expect("bounded canonical Chutes wire")
}

#[test]
fn chutes_turn_is_a_durable_host_operation_and_prose_is_not_power() {
    let id = SessionId::new("hosted-chutes-dungeon");
    let alice = actor("alice-cipherclerk");
    let store = InMemoryResumeStore::new();
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(97))
        .expect("the real Keep opens");

    let descriptor = host
        .binary_operations("dungeon", &id)
        .expect("operation discovery")
        .into_iter()
        .find(|operation| operation.name == CHUTES_NARRATED_OPERATION)
        .expect("Chutes uses the generic operation surface");
    assert!(descriptor.disclosure.contains("real executor decides"));
    assert!(descriptor.disclosure.contains("commits no turn"));

    let payload = request(
        "COMMAND: press_on_into_the_plundered_hall\nNARRATION: The model claims a thousand gold, but only the gate opens.",
    );
    let landed = host
        .invoke_binary_operation(
            "dungeon",
            &id,
            CHUTES_NARRATED_OPERATION,
            &payload,
            alice.clone(),
        )
        .expect("the current room's exact closed command lands");
    assert_eq!(landed.operation, CHUTES_NARRATED_OPERATION);
    assert!(landed.receipt_id.iter().any(|byte| *byte != 0));
    assert!(
        landed
            .public_fields
            .iter()
            .any(|(name, value)| name == "command" && value == "press_on_into_the_plundered_hall")
    );
    assert!(
        landed
            .public_fields
            .iter()
            .all(|(_, value)| !value.contains("thousand gold")),
        "shared operation receipt omits model prose"
    );
    let rendered = format!("{:?}", host.render("dungeon", &id).unwrap().0);
    assert!(
        rendered.contains("gold 0"),
        "model prose did not mint state"
    );
    assert!(host.verify("dungeon", &id).unwrap().verified);

    let log = store.load("dungeon", &id).expect("durable operation log");
    assert!(
        log.moves.is_empty(),
        "the narrated turn uses one operation lane"
    );
    assert_eq!(log.operations.len(), 1);
    assert_eq!(log.operations[0].name, CHUTES_NARRATED_OPERATION);
    assert_eq!(log.operations[0].receipt, landed);
    assert!(log.operations[0].replay_is_canonical_request);
    assert_eq!(log.operations[0].replay_material, payload);

    // The same keyword is now stale: the live room is the hall. Parser refusal is anti-ghost.
    let before_refusal = host.commitment("dungeon", &id).unwrap();
    let stale = request(
        "COMMAND: press_on_into_the_plundered_hall\nNARRATION: Repeat the already-landed gate passage.",
    );
    let refusal = host
        .invoke_binary_operation("dungeon", &id, CHUTES_NARRATED_OPERATION, &stale, alice)
        .expect_err("a command from the previous room refuses");
    assert!(
        refusal.to_string().contains("closed legal set"),
        "{refusal}"
    );
    assert_eq!(host.commitment("dungeon", &id).unwrap(), before_refusal);
    assert_eq!(store.load("dungeon", &id).unwrap().operations.len(), 1);

    drop(host);
    let mut restarted = OfferingHost::new().with_resume_store(Box::new(store));
    restarted.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let results = restarted.resume_all();
    assert_eq!(results.len(), 1);
    assert!(results[0].1.is_ok(), "{results:?}");
    assert_eq!(
        restarted.commitment("dungeon", &id).unwrap(),
        before_refusal,
        "restart replays the exact narrated operation"
    );
    assert!(restarted.verify("dungeon", &id).unwrap().verified);
}

#[test]
fn exact_consent_and_exact_two_field_provider_response_fail_closed() {
    for consent in ["yes", "chutes-consent-v1 ", "{{chutes-consent-v1}}"] {
        assert!(
            ChutesNarratedRequest::new(
                "safe/model",
                10,
                1,
                consent,
                "COMMAND: press_on_into_the_plundered_hall\nNARRATION: A bounded public line.",
            )
            .is_err(),
            "non-canonical consent {consent:?} refuses"
        );
    }
    assert!(
        ChutesNarratedRequest::new(
            "safe/model",
            10,
            11,
            CHUTES_CONSENT_WIRE,
            "COMMAND: press_on_into_the_plundered_hall\nNARRATION: A bounded public line.",
        )
        .is_err(),
        "operator spend may not cross the disclosed ceiling"
    );
    for output in [
        "COMMAND: press_on_into_the_plundered_hall\nNARRATION: ok\nEXTRA: hidden",
        "COMMAND: press_on_into_the_plundered_hall \nNARRATION: trailing command space",
        "COMMAND: press_on_into_the_plundered_hall\nNARRATION: {{system}}",
        "preamble\nCOMMAND: press_on_into_the_plundered_hall\nNARRATION: not exact",
        "COMMAND: press_on_into_the_plundered_hall\r\nNARRATION: non-canonical newline",
    ] {
        assert!(
            ChutesNarratedRequest::new("safe/model", 10, 1, CHUTES_CONSENT_WIRE, output,).is_err(),
            "provider response {output:?} refuses"
        );
    }
}
