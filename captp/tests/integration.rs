//! Integration tests exercising cross-module scenarios in pyana-captp.
//!
//! These tests verify that the components (Swiss table, URI, sessions, GC,
//! handoff, pipeline, store-and-forward) compose correctly for end-to-end
//! capability lifecycle operations.

use pyana_captp::FederationId;
use pyana_captp::handoff::validate_handoff;
use pyana_captp::session::CapSession;
use pyana_captp::store_forward::{RelayInfo, queue_via_blocklace, scan_and_decrypt_blocklace};
use pyana_captp::{
    CrossFedPipelineBridge, DropResult, ExportGcManager, HandoffCertificate, HandoffPresentation,
    ImportGcManager, MessagePriority, MessageRelay, PipelineError, PipelinePromiseState,
    PipelineRegistry, PipelineResultValue, PipelinedAction, PipelinedMessage, PyanaUri,
    QueuedMessage, StoreForwardClient, SwissTable, generate_x25519_keypair,
};

use pyana_cell::AuthRequired;
use pyana_types::{CellId, generate_keypair};

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
// Test 1: Full lifecycle
//   export swiss -> create URI -> parse URI -> enliven -> use -> drop -> GC
// =============================================================================

#[test]
fn full_lifecycle_export_to_gc() {
    let federation_id = [0xAB; 32];
    let target_cell = cell(0x42);
    let holder_federation = fed(0xCC);

    // Phase 1: Export
    let mut swiss_table = SwissTable::new();
    let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, Some(500));

    // Phase 2: Create URI
    let uri = swiss_table.make_uri(federation_id, &swiss).unwrap();
    assert_eq!(uri.federation_id, federation_id);
    assert_eq!(uri.cell_id, target_cell.0);
    assert_eq!(uri.swiss, swiss);

    // Phase 3: Serialize and parse URI
    let uri_string = uri.to_uri_string();
    assert!(uri_string.starts_with("pyana://"));
    let parsed_uri = PyanaUri::parse(&uri_string).unwrap();
    assert_eq!(parsed_uri, uri);

    // Phase 4: Enliven
    let entry = swiss_table.enliven(&parsed_uri.swiss, 200).unwrap();
    assert_eq!(entry.cell_id, target_cell);
    assert_eq!(entry.permissions, AuthRequired::Signature);
    assert_eq!(entry.use_count, 1);

    // Phase 5: Register in GC
    let mut export_gc = ExportGcManager::new();
    export_gc.record_export(target_cell, holder_federation, 200);
    assert_eq!(export_gc.get(&target_cell).unwrap().total_refs, 1);

    let mut import_gc = ImportGcManager::new();
    import_gc.record_import(fed(0xAB), target_cell);
    assert_eq!(
        import_gc.get(&fed(0xAB), &target_cell).unwrap().local_refs,
        1
    );

    // Phase 6: Use (enliven again)
    let entry2 = swiss_table.enliven(&parsed_uri.swiss, 300).unwrap();
    assert_eq!(entry2.use_count, 2);

    // Phase 7: Drop
    let drop_msg = import_gc.local_ref_dropped(fed(0xAB), target_cell);
    assert!(drop_msg.is_some());
    let drop_msg = drop_msg.unwrap();
    assert_eq!(drop_msg.cell_id, target_cell);

    let result = export_gc.process_drop(target_cell, holder_federation);
    assert_eq!(result, DropResult::CanRevoke);

    // Phase 8: GC sweep
    let swept = export_gc.gc_sweep();
    assert_eq!(swept.len(), 1);
    assert!(swept.contains(&target_cell));
    assert!(export_gc.is_empty());

    // Phase 9: Revoke from swiss table
    assert!(swiss_table.revoke(&swiss));
    assert!(!swiss_table.contains(&swiss));

    let err = swiss_table.enliven(&swiss, 400).unwrap_err();
    assert_eq!(err, pyana_captp::EnlivenError::NotFound);
}

// =============================================================================
// Test 2: Handoff lifecycle
//   register swiss -> create cert -> serialize -> deserialize -> present -> validate
// =============================================================================

#[test]
fn handoff_full_lifecycle() {
    let (intro_sk, intro_pk) = generate_keypair();
    let intro_fed = FederationId(intro_pk.0);
    let (recip_sk, recip_pk) = generate_keypair();
    let target_fed = fed(0xDD);
    let target_cell = cell(0xEE);

    // Phase 1: Introducer registers swiss at target
    let mut swiss_table = SwissTable::new();
    let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, None);
    assert!(swiss_table.contains(&swiss));

    // Phase 2: Create handoff certificate
    let cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0,
        AuthRequired::Signature,
        None,
        None,
        None,
        swiss,
    );

    assert!(cert.verify_signature(&intro_pk));
    assert!(cert.is_valid(1000));

    // Phase 3: Serialize to compact string (out-of-band transport)
    let compact = cert.to_compact_string();
    assert!(compact.starts_with("pyana-handoff:"));

    // Phase 4: Recipient deserializes
    let decoded_cert = HandoffCertificate::from_compact_string(&compact).unwrap();
    assert_eq!(decoded_cert.introducer, intro_fed);
    assert_eq!(decoded_cert.target_cell, target_cell);
    assert_eq!(decoded_cert.recipient_pk, recip_pk.0);
    assert_eq!(decoded_cert.swiss, swiss);

    // Also verify bytes roundtrip
    let bytes = decoded_cert.to_bytes();
    let from_bytes = HandoffCertificate::from_bytes(&bytes).unwrap();
    assert_eq!(from_bytes.nonce, decoded_cert.nonce);

    // Phase 5: Recipient creates presentation
    let presentation = HandoffPresentation::create(decoded_cert, &recip_sk);
    assert!(presentation.verify_recipient_signature());

    // Phase 6: Target validates
    let known_feds = vec![intro_fed];
    let acceptance =
        validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known_feds, 200).unwrap();

    assert_eq!(acceptance.cell_id, target_cell);
    assert_eq!(acceptance.permissions, AuthRequired::Signature);
    assert!(acceptance.routing_token != [0u8; 32]);

    // Phase 7: Verify swiss was consumed
    let entry = swiss_table.peek(&swiss).unwrap();
    assert_eq!(entry.use_count, 1);
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

// =============================================================================
// Test 4: Store-and-forward lifecycle
//   queue messages -> simulate reconnect -> deliver in order
// =============================================================================

#[test]
fn store_forward_queue_reconnect_deliver() {
    let (bob_secret, bob_public) = generate_x25519_keypair();
    let (alice_secret, _alice_public) = generate_x25519_keypair();
    let alice_fed = fed(0xAA);
    let bob_fed = fed(0xBB);

    // Phase 1: Alice creates a store-forward client
    let mut alice_client = StoreForwardClient::new(
        alice_fed,
        vec![RelayInfo {
            federation_id: fed(0xCC),
            endpoint: "relay.pyana.net".into(),
            capacity: 10000,
        }],
    );

    let mut relay = MessageRelay::new(100, 10000);

    // Phase 2: Bob is offline. Alice queues multiple messages
    let messages = vec![
        b"capability grant: read access".to_vec(),
        b"state update: balance=100".to_vec(),
        b"event: transfer initiated".to_vec(),
        b"capability grant: write access".to_vec(),
    ];

    for payload in &messages {
        let msg = alice_client.prepare_message(
            bob_fed,
            payload,
            &bob_public,
            &alice_secret,
            MessagePriority::Normal,
            100,
            500,
        );
        let result = alice_client.queue_on_relay(msg, &mut relay);
        assert!(matches!(result, pyana_captp::SendResult::Queued { .. }));
    }

    assert_eq!(relay.pending_count(&bob_fed), 4);
    assert_eq!(alice_client.unacknowledged_count(), 4);

    // Phase 3: Bob comes online and drains
    let queued = relay.drain(&bob_fed);
    assert_eq!(queued.len(), 4);
    assert_eq!(relay.pending_count(&bob_fed), 0);

    // Phase 4: Bob decrypts and processes in causal order
    let processed = StoreForwardClient::process_incoming(queued, &bob_secret).unwrap();
    assert_eq!(processed.len(), 4);

    for (i, (seq, plaintext)) in processed.iter().enumerate() {
        assert_eq!(*seq, i as u64);
        assert_eq!(*plaintext, messages[i]);
    }

    // Phase 5: Bob acknowledges
    for i in 0..4u64 {
        assert!(alice_client.acknowledge(&bob_fed, i));
    }
    assert_eq!(alice_client.unacknowledged_count(), 0);
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
fn store_forward_blocklace_integration() {
    let (bob_secret, bob_public) = generate_x25519_keypair();
    let (alice_secret, _) = generate_x25519_keypair();
    let bob_fed = fed(0xBB);
    let alice_fed = fed(0xAA);

    // Phase 1: Alice queues messages via blocklace
    let payloads_for_bob: Vec<(&[u8], u64)> = vec![
        (b"blocklace msg 0", 0),
        (b"blocklace msg 1", 1),
        (b"blocklace msg 2", 2),
    ];

    let mut blocklace_blocks: Vec<Vec<u8>> = Vec::new();

    // Add unrelated blocks (noise)
    blocklace_blocks.push(b"unrelated consensus data".to_vec());
    blocklace_blocks.push(vec![0xDE, 0xAD, 0xBE, 0xEF]);

    // Add store-forward envelopes (intentionally out of causal order)
    for (msg, seq) in payloads_for_bob.iter().rev() {
        let block = queue_via_blocklace(bob_fed, msg, &bob_public, &alice_secret, *seq);
        blocklace_blocks.push(block);
    }

    // Add a message for Alice (should be skipped by Bob)
    let (_alice_secret2, alice_public2) = generate_x25519_keypair();
    blocklace_blocks.push(queue_via_blocklace(
        alice_fed,
        b"not for bob",
        &alice_public2,
        &alice_secret,
        99,
    ));

    // Phase 2: Bob syncs the blocklace and scans
    let results = scan_and_decrypt_blocklace(&blocklace_blocks, &bob_fed, &bob_secret).unwrap();

    // Phase 3: Verify correct messages in causal order
    assert_eq!(results.len(), 3);
    assert_eq!(results[0], (0, b"blocklace msg 0".to_vec()));
    assert_eq!(results[1], (1, b"blocklace msg 1".to_vec()));
    assert_eq!(results[2], (2, b"blocklace msg 2".to_vec()));
}

// =============================================================================
// Test 5: Session exchange
//   two sessions exchanging import/export entries
// =============================================================================

#[test]
fn session_bidirectional_exchange() {
    let peer_b_id = [0xBB; 32];
    let peer_a_id = [0xAA; 32];

    // Create sessions (each tracks the OTHER peer)
    let mut session_a = CapSession::new(peer_b_id); // A's view of B
    let mut session_b = CapSession::new(peer_a_id); // B's view of A

    // Phase 1: A exports a capability to B
    let cell_from_a = cell(0x11);
    let exported_cell = session_a.export(cell_from_a, AuthRequired::Signature);
    assert_eq!(exported_cell, cell_from_a);
    assert_eq!(session_a.exports[&cell_from_a].ref_count, 1);

    // B records the import
    session_b.import(cell_from_a, AuthRequired::Signature);
    assert!(session_b.imports[&cell_from_a].live);

    // Phase 2: B exports a capability to A
    let cell_from_b = cell(0x22);
    session_b.export(cell_from_b, AuthRequired::None);
    session_a.import(cell_from_b, AuthRequired::None);

    // Both sessions should be active
    assert!(session_a.is_active());
    assert!(session_b.is_active());

    // Phase 3: Promise lifecycle across sessions
    let promise_id = session_a.create_promise();
    assert!(matches!(
        session_a.promise_state(promise_id),
        Some(pyana_captp::session::PromiseState::Pending)
    ));

    let result_cell = cell(0x33);
    assert!(session_a.fulfill_promise(promise_id, result_cell));
    assert!(matches!(
        session_a.promise_state(promise_id),
        Some(pyana_captp::session::PromiseState::Fulfilled { cell_id }) if *cell_id == result_cell
    ));

    // Phase 4: A exports same cell multiple times (ref counting)
    session_a.export(cell_from_a, AuthRequired::Signature);
    assert_eq!(session_a.exports[&cell_from_a].ref_count, 2);

    // Release one ref
    assert!(!session_a.release_export(&cell_from_a));
    assert_eq!(session_a.exports[&cell_from_a].ref_count, 1);

    // Release last ref
    assert!(session_a.release_export(&cell_from_a));
    assert!(!session_a.exports.contains_key(&cell_from_a));

    // Phase 5: Disconnect and deactivation
    session_a.disconnect_import(&cell_from_b);
    assert!(!session_a.imports[&cell_from_b].live);
    assert!(!session_a.is_active()); // no exports, no live imports

    // B still active (has exports)
    assert!(session_b.is_active());

    // Phase 6: Break a promise
    let promise_b = session_b.create_promise();
    assert!(session_b.break_promise(promise_b, "connection lost".into()));
    assert!(matches!(
        session_b.promise_state(promise_b),
        Some(pyana_captp::session::PromiseState::Broken { reason }) if reason == "connection lost"
    ));

    // Cannot fulfill or break an already-broken promise
    assert!(!session_b.fulfill_promise(promise_b, cell(0x44)));
    assert!(!session_b.break_promise(promise_b, "another reason".into()));
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
        pyana_captp::PipelineWireMessage::PipelineToPromise {
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

#[test]
fn empty_pipeline_chain_rejected() {
    let mut registry = PipelineRegistry::new();
    let p = registry.create_promise();

    let result = registry.pipeline_chain(p, vec![], fed(0xAA));
    assert_eq!(result, Err(PipelineError::EmptyChain));
}

#[test]
fn handoff_wrong_recipient_rejects_presentation() {
    let (intro_sk, intro_pk) = generate_keypair();
    let intro_fed = FederationId(intro_pk.0);
    let (_recip_sk, recip_pk) = generate_keypair();
    let (impostor_sk, _impostor_pk) = generate_keypair();
    let target_fed = fed(0xDD);
    let target_cell = cell(0xEE);

    let mut swiss_table = SwissTable::new();
    let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, None);

    let cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0, // Certificate names the real recipient
        AuthRequired::Signature,
        None,
        None,
        None,
        swiss,
    );

    // Impostor tries to present
    let presentation = HandoffPresentation::create(cert, &impostor_sk);

    let known = vec![intro_fed];
    let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);
    assert_eq!(
        result.unwrap_err(),
        pyana_captp::HandoffError::InvalidRecipientSignature
    );
}

#[test]
fn uri_invalid_inputs() {
    // Wrong scheme
    assert!(PyanaUri::parse("http://foo/bar/baz").is_err());

    // Wrong segment count
    assert!(PyanaUri::parse("pyana://one/two").is_err());
    assert!(PyanaUri::parse("pyana://one/two/three/four").is_err());

    // Invalid base58 characters
    assert!(PyanaUri::parse("pyana://0OIl/valid/valid").is_err());

    // Wrong length (valid base58 but not 32 bytes)
    let short = bs58::encode(&[0xAA; 16]).into_string();
    let valid = bs58::encode(&[0xBB; 32]).into_string();
    assert!(PyanaUri::parse(&format!("pyana://{short}/{valid}/{valid}")).is_err());
}

#[test]
fn store_forward_relay_limits() {
    let mut relay = MessageRelay::new(2, 3);
    let dest_a = fed(0xAA);
    let dest_b = fed(0xBB);

    let make_msg = |dest: FederationId, seq: u64| QueuedMessage {
        destination: dest,
        encrypted_payload: vec![seq as u8],
        sender_ephemeral_pk: [0x11; 32],
        causal_sequence: seq,
        queued_at: 100,
        ttl_blocks: 50,
        priority: MessagePriority::Normal,
    };

    // Fill dest_a's queue (max 2)
    relay.enqueue(make_msg(dest_a, 0)).unwrap();
    relay.enqueue(make_msg(dest_a, 1)).unwrap();
    assert!(relay.enqueue(make_msg(dest_a, 2)).is_err()); // queue full

    // dest_b still has room (total: 2 of 3)
    relay.enqueue(make_msg(dest_b, 0)).unwrap();

    // Now total is 3, no more room anywhere
    assert!(relay.enqueue(make_msg(dest_b, 1)).is_err()); // storage full
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
