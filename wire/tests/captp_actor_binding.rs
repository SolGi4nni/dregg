//! CapTP delivery authorizes the actual actor, not merely the action target.
//! The common gateway shape `actor == target` remains a special honest case,
//! but it is no longer silently assumed by the wire builder or executor.

use dregg_captp::{FederationId, HandoffCertificate};
use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_turn::action::Authorization;
use dregg_turn::{ComputronCosts, Effect, TurnError, TurnExecutor};
use dregg_types::{SigningKey, sign};
use dregg_wire::captp_routing::build_captp_turn_delivered_from_parts;

const LOCAL_FEDERATION: [u8; 32] = [0u8; 32];

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn identity(seed: u8) -> (SigningKey, Cell) {
    let key = SigningKey::from_bytes(&[seed; 32]);
    let mut cell = Cell::with_balance(key.public_key().0, [0u8; 32], 1_000);
    cell.permissions = open_permissions();
    (key, cell)
}

#[test]
fn captp_delivery_binds_recipient_signature_and_key_to_actual_actor() {
    let (introducer_key, mut introducer) = identity(31);
    let (bob_key, mut bob) = identity(32);
    let (_mallory_key, mut mallory) = identity(33);
    let (_target_key, mut target) = identity(34);
    let target_id = target.id();
    target.permissions = open_permissions();
    introducer
        .capabilities
        .grant(target_id, AuthRequired::None)
        .expect("introducer holds target authority");
    bob.capabilities
        .grant(target_id, AuthRequired::None)
        .expect("recipient can route to target");
    mallory
        .capabilities
        .grant(target_id, AuthRequired::None)
        .expect("substituted actor reaches the authorization gate");
    let bob_id = bob.id();
    let mallory_id = mallory.id();

    let cert = HandoffCertificate::create(
        &introducer_key,
        FederationId(introducer_key.public_key().0),
        FederationId(LOCAL_FEDERATION),
        target_id,
        bob_key.public_key().0,
        AuthRequired::None,
        None,
        None,
        None,
        [0x44; 32],
    );
    let effect = Effect::EmitEvent {
        cell: target_id,
        event: dregg_turn::Event::new([0x55; 32], vec![[1; 32], [2; 32], [3; 32]]),
    };

    let mut ledger = Ledger::new();
    ledger.insert_cell(introducer).unwrap();
    ledger.insert_cell(bob).unwrap();
    ledger.insert_cell(mallory).unwrap();
    ledger.insert_cell(target).unwrap();

    // Honest non-gateway shape: actor and target differ. Bob signs the exact
    // actor CellId that the Turn carries; the new wire/executor contract agrees.
    let honest_message = Authorization::captp_delivered_signing_message_for_federation(
        &LOCAL_FEDERATION,
        &cert.nonce,
        &bob_id,
        &target_id,
        0,
        std::slice::from_ref(&effect),
    );
    let honest_signature = sign(&bob_key, &honest_message).0;
    let honest_turn = build_captp_turn_delivered_from_parts(
        bob_id,
        target_id,
        effect.clone(),
        0,
        cert.clone(),
        introducer_key.public_key().0,
        bob_key.public_key().0,
        honest_signature,
    );
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let honest = executor.execute(&honest_turn, &mut ledger.clone());
    assert!(
        honest.is_committed(),
        "recipient acting under its own signed CellId must commit: {honest:?}"
    );

    // The historical hole: Bob signed the old target-as-agent preimage, then
    // Mallory supplied the authorization in a turn naming Mallory as actor.
    // Both cells exist and Mallory has ordinary target access, so only the
    // actor↔recipient identity binding may stop it.
    let legacy_target_message = Authorization::captp_delivered_signing_message_for_federation(
        &LOCAL_FEDERATION,
        &cert.nonce,
        &target_id,
        &target_id,
        0,
        std::slice::from_ref(&effect),
    );
    let laundered_signature = sign(&bob_key, &legacy_target_message).0;
    let substituted_turn = build_captp_turn_delivered_from_parts(
        mallory_id,
        target_id,
        effect,
        0,
        cert,
        introducer_key.public_key().0,
        bob_key.public_key().0,
        laundered_signature,
    );
    match executor.execute(&substituted_turn, &mut ledger) {
        dregg_turn::TurnResult::Rejected {
            reason: TurnError::InvalidAuthorization { reason },
            ..
        } => assert!(
            reason.contains("sender_pk does not match the acting cell public key"),
            "wrong refusal: {reason}"
        ),
        other => {
            panic!("Bob's recipient authorization must not launder into Mallory's actor: {other:?}")
        }
    }
}
