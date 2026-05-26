//! Integration tests exercising cross-module scenarios in dregg-captp.
//!
//! These tests verify that the components (Swiss table, URI, sessions, GC,
//! handoff, pipeline, store-and-forward) compose correctly for end-to-end
//! capability lifecycle operations.

use dregg_captp::FederationId;
use dregg_captp::session::CapSession;
use dregg_captp::{
    CrossFedPipelineBridge, DropResult, ExportGcManager, HandoffCertificate, HandoffPresentation,
    ImportGcManager, MessagePriority, MessageRelay, PipelinePromiseState, PipelineRegistry,
    PipelineResultValue, PipelinedAction, PipelinedMessage, StoreForwardClient, SwissTable,
    generate_x25519_keypair,
};

use dregg_cell::AuthRequired;
use dregg_types::{CellId, generate_keypair};

// =============================================================================
// Helpers
// =============================================================================

fn fed(byte: u8) -> FederationId {
    FederationId([byte; 32])
}

fn cell(byte: u8) -> CellId {
    CellId([byte; 32])
}

fn make_action(method: &str) -> PipelinedAction {
    PipelinedAction {
        method: method.to_string(),
        args: vec![],
        authorization: vec![],
    }
}

// =============================================================================
// Test 3: Pipeline lifecycle
//   register promise -> pipeline multiple messages -> resolve -> all delivered
// =============================================================================

#[test]
fn pipeline_register_pipeline_resolve_deliver() {
    let mut registry = PipelineRegistry::new();
    let sender = fed(0xAA);

    // Phase 1: Create a promise
    let promise_id = registry.create_promise();
    assert!(matches!(
        registry.promise_state(promise_id),
        Some(PipelinePromiseState::Pending)
    ));

    // Phase 2: Pipeline multiple messages to the promise
    let methods = ["transfer", "query_balance", "emit_event", "update_state"];
    for (i, method) in methods.iter().enumerate() {
        let msg = PipelinedMessage {
            target_promise_id: promise_id,
            action: make_action(method),
            result_promise_id: Some(100 + i as u64),
            sender,
        };
        registry.pipeline_message(msg).unwrap();
    }

    assert_eq!(registry.queued_count(promise_id), 4);

    // Phase 3: Resolve the promise
    let resolved_cell = cell(0x77);
    let delivered = registry.resolve_promise(promise_id, resolved_cell);

    // Phase 4: Verify all messages delivered in order
    assert_eq!(delivered.len(), 4);
    for (i, msg) in delivered.iter().enumerate() {
        assert_eq!(msg.action.method, methods[i]);
        assert_eq!(msg.result_promise_id, Some(100 + i as u64));
        assert_eq!(msg.sender, sender);
    }

    assert_eq!(registry.queued_count(promise_id), 0);
    assert!(matches!(
        registry.promise_state(promise_id),
        Some(PipelinePromiseState::Fulfilled { resolved_cell: c }) if *c == resolved_cell
    ));
}

#[test]
fn pipeline_chain_and_cascading_break() {
    let mut registry = PipelineRegistry::new();
    let sender = fed(0xBB);

    let initial = registry.create_promise();

    let steps = vec![
        make_action("authenticate"),
        make_action("authorize"),
        make_action("execute"),
    ];
    let final_promise = registry.pipeline_chain(initial, steps, sender).unwrap();

    // Resolve initial -> delivers "authenticate"
    let step1_msgs = registry.resolve_promise(initial, cell(0x01));
    assert_eq!(step1_msgs.len(), 1);
    assert_eq!(step1_msgs[0].action.method, "authenticate");
    let step1_result = step1_msgs[0].result_promise_id.unwrap();

    // Break step1's result -> cascades to "authorize" and "execute"
    let notifications = registry.break_promise(step1_result, "auth failed".into());
    assert!(!notifications.is_empty());

    // Final promise should be broken
    assert!(matches!(
        registry.promise_state(final_promise),
        Some(PipelinePromiseState::Broken { reason }) if reason.contains("auth failed")
    ));
}

#[test]
fn store_forward_ttl_expiry_and_priority() {
    let (bob_secret, bob_public) = generate_x25519_keypair();
    let (alice_secret, _) = generate_x25519_keypair();
    let bob_fed = fed(0xBB);
    let alice_fed = fed(0xAA);

    let mut client = StoreForwardClient::new(alice_fed, vec![]);
    let mut relay = MessageRelay::new(100, 1000);

    // Queue messages with different TTLs and priorities
    let msg_short_ttl = client.prepare_message(
        bob_fed,
        b"ephemeral notification",
        &bob_public,
        &alice_secret,
        MessagePriority::Low,
        10, // short TTL
        100,
    );
    let msg_long_ttl = client.prepare_message(
        bob_fed,
        b"important payment",
        &bob_public,
        &alice_secret,
        MessagePriority::High,
        1000, // long TTL
        100,
    );

    relay.enqueue(msg_short_ttl).unwrap();
    relay.enqueue(msg_long_ttl).unwrap();
    assert_eq!(relay.total_stored(), 2);

    // Advance time past short TTL
    let expired = relay.expire(110); // 110 - 100 = 10 >= ttl of 10
    assert_eq!(expired, 1);
    assert_eq!(relay.total_stored(), 1);

    // Long TTL message still present
    let remaining = relay.drain(&bob_fed);
    assert_eq!(remaining.len(), 1);

    let processed = StoreForwardClient::process_incoming(remaining, &bob_secret).unwrap();
    assert_eq!(processed.len(), 1);
    assert_eq!(processed[0].1, b"important payment");
}

#[test]
fn session_gc_integration() {
    // Demonstrates how sessions and GC managers work together
    let peer_b_id = [0xBB; 32];

    let mut session_a = CapSession::new(peer_b_id);
    let mut export_gc = ExportGcManager::new();
    let mut import_gc = ImportGcManager::new();

    let exported_cell = cell(0x55);

    // A exports to B
    session_a.export(exported_cell, AuthRequired::Signature);
    export_gc.record_export(exported_cell, fed(0xBB), 100);

    // B holds a reference (tracked by import GC on B's side)
    import_gc.record_import(fed(0xAA), exported_cell);

    // B drops its reference
    let drop_msg = import_gc.local_ref_dropped(fed(0xAA), exported_cell);
    assert!(drop_msg.is_some());

    // A processes the drop
    let result = export_gc.process_drop(exported_cell, fed(0xBB));
    assert_eq!(result, DropResult::CanRevoke);

    // A releases the session export
    assert!(session_a.release_export(&exported_cell));
    assert!(session_a.exports.is_empty());

    // GC sweep cleans up
    let swept = export_gc.gc_sweep();
    assert!(swept.contains(&exported_cell));
}

// =============================================================================
// Test 6: Cross-federation pipeline bridge end-to-end
// =============================================================================

#[test]
fn cross_federation_bridge_full_flow() {
    let mut bridge = CrossFedPipelineBridge::new();
    let remote_fed = fed(0xBB);

    // Phase 1: Pipeline a chain of actions to a remote promise
    let steps = vec![
        make_action("lookup_account"),
        make_action("check_balance"),
        make_action("debit"),
    ];

    let final_promise = bridge
        .pipeline_chain_to_remote(remote_fed, 42, steps)
        .unwrap();

    // Should have 3 outbound messages
    let outbox = bridge.drain_outbox();
    assert_eq!(outbox.len(), 3);
    for (dest, _msg) in &outbox {
        assert_eq!(*dest, remote_fed);
    }

    // Phase 2: Remote resolves the first result
    let first_local_promise = match &outbox[0].1 {
        dregg_captp::PipelineWireMessage::PipelineToPromise {
            result_promise_id, ..
        } => result_promise_id.unwrap(),
        _ => panic!("expected PipelineToPromise"),
    };

    let delivered = bridge.on_remote_resolution(remote_fed, first_local_promise, cell(0x01));
    assert!(delivered.is_empty());

    assert!(matches!(
        bridge.local_registry().promise_state(first_local_promise),
        Some(PipelinePromiseState::Fulfilled { .. })
    ));

    // Phase 3: Remote sends back a failure for the final step
    let failure_result = PipelineResultValue::Failure {
        error: "insufficient funds".into(),
    };
    bridge.on_pipeline_result(remote_fed, final_promise, failure_result);

    assert!(matches!(
        bridge.local_registry().promise_state(final_promise),
        Some(PipelinePromiseState::Broken { reason }) if reason == "insufficient funds"
    ));
}

#[test]
fn cross_federation_bridge_incoming_and_local_resolve() {
    let mut bridge = CrossFedPipelineBridge::new();
    let peer_a = fed(0xAA);
    let peer_b = fed(0xBB);

    // Create a local promise
    let local_promise = bridge.local_registry_mut().create_promise();

    // Peer A and peer B both pipeline to our local promise
    bridge
        .on_pipeline_message(
            peer_a,
            local_promise,
            make_action("a_wants_result"),
            Some(10),
        )
        .unwrap();
    bridge
        .on_pipeline_message(
            peer_b,
            local_promise,
            make_action("b_wants_result"),
            Some(20),
        )
        .unwrap();

    // Resolve the local promise
    let delivered = bridge.resolve_local_promise(local_promise, cell(0x99));

    // Both peers' messages should be delivered
    assert_eq!(delivered.len(), 2);
    let methods: Vec<&str> = delivered.iter().map(|m| m.action.method.as_str()).collect();
    assert!(methods.contains(&"a_wants_result"));
    assert!(methods.contains(&"b_wants_result"));
}

// =============================================================================
// Test 7: Error paths and edge cases
// =============================================================================

#[test]
fn pipeline_to_nonexistent_promise_from_bridge() {
    let mut bridge = CrossFedPipelineBridge::new();
    let peer = fed(0xAA);

    // Pipeline to a promise that doesn't exist in local registry.
    // The bridge should create it implicitly in the peer's registry.
    let result = bridge.on_pipeline_message(peer, 999, make_action("speculative"), None);
    assert!(result.is_ok());
}

// =============================================================================
// Test 8: Multi-federation GC independence
// =============================================================================

#[test]
fn multi_federation_gc_independence() {
    let mut export_gc = ExportGcManager::new();
    let shared_cell = cell(0x42);

    // Three federations all hold references to the same cell
    export_gc.record_export(shared_cell, fed(0xAA), 100);
    export_gc.record_export(shared_cell, fed(0xBB), 101);
    export_gc.record_export(shared_cell, fed(0xCC), 102);

    assert_eq!(export_gc.get(&shared_cell).unwrap().total_refs, 3);

    // Drop from AA
    let r = export_gc.process_drop(shared_cell, fed(0xAA));
    assert_eq!(r, DropResult::StillHeld);

    // Drop from BB
    let r = export_gc.process_drop(shared_cell, fed(0xBB));
    assert_eq!(r, DropResult::StillHeld);

    // Drop from CC (last holder)
    let r = export_gc.process_drop(shared_cell, fed(0xCC));
    assert_eq!(r, DropResult::CanRevoke);

    // Invalid drop (already dropped)
    let r = export_gc.process_drop(shared_cell, fed(0xAA));
    assert_eq!(r, DropResult::Invalid);
}

// =============================================================================
// Test: three-party handoff (Alice → Bob → Carol)
//
// Closes audit GAP-1: the introducer's federation differs from the target's.
// The cert is signed by Alice, names Bob as recipient and Carol as target,
// and Carol's swiss table has the swiss pre-registered out-of-band.
// =============================================================================

#[test]
fn three_party_handoff_alice_introduces_bob_to_carol() {
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);

    let (bob_sk, bob_pk) = generate_keypair();

    let carol_fed = fed(0xCA);
    let carol_cell = cell(0x42);

    // Carol pre-registers a swiss entry for the target cell.
    let mut carol_swiss = SwissTable::new();
    let swiss = carol_swiss.export(carol_cell, AuthRequired::Signature, 100, None);

    // Alice mints a cert directing Bob at Carol's cell.
    let cert = HandoffCertificate::create(
        &alice_sk,
        alice_fed,
        carol_fed,
        carol_cell,
        bob_pk.0,
        AuthRequired::Signature,
        None,
        Some(500),
        Some(1),
        swiss,
    );
    assert_ne!(cert.introducer, cert.target_federation);

    // Bob signs a presentation binding himself to the cert.
    let presentation = HandoffPresentation::create(cert, &bob_sk);

    // Carol validates the cert end-to-end.
    let known = vec![alice_fed];
    let acceptance = dregg_captp::handoff::validate_handoff(
        &presentation,
        &alice_pk,
        &mut carol_swiss,
        &known,
        150,
    )
    .expect("three-party cert must validate");
    assert_eq!(acceptance.cell_id, carol_cell);
}
