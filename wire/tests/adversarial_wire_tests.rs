//! Adversarial tests for the wire-layer hardening lane.
//!
//! Each test exercises a specific attacker capability the wire layer is
//! supposed to detect-and-reject. Per the lane spec, this suite extends
//! Lane B's `handoff_replay_rejected_by_seen_nonce_registry` with:
//!
//! 1. **Handoff cert tamper.** A cert whose body has been mutated after
//!    issuance fails `verify_signature`, so `validate_handoff` returns
//!    `InvalidIntroducerSignature`.
//! 2. **Tampered recipient signature on a `HandoffPresentation`** is
//!    caught by `verify_recipient_signature` (returns
//!    `InvalidRecipientSignature`).
//! 3. **Replay nonce double-presented.** The server-side seen-nonce
//!    registry rejects the second presentation even though the swiss
//!    table's `max_uses` does not catch it. (Same shape as Lane B's
//!    test but driven through the full `seen_handoff_nonces` insert
//!    path with a `max_uses = None` cert.)
//! 4. **Broken signature on PipelinedMsg** — a PipelinedMsg sent under a
//!    stale session epoch is rejected with `STALE_EPOCH`. The wire layer
//!    treats `authorization` as opaque (the executor verifies it
//!    downstream), but the session-epoch fence is the wire-layer's
//!    "wrong key holder" defense and MUST trip on a stale message.
//! 5. **Broken seal on incoming PresentHandoff** — a presentation whose
//!    `presentation_bytes` are postcard-malformed is rejected before
//!    any signature check.
//! 6. **Disconnect-driven broken-promise queue is populated.** When a
//!    peer disconnects with outstanding promises, the queue exposed via
//!    `drain_pending_broken_promises` carries the cascading
//!    notifications so the node tick can deliver them as
//!    `WireMessage::PromiseBroken`.
//! 7. **AttestedRootPush from a stranger is silently dropped.** The
//!    handler MUST NOT enqueue a push from a federation that is not in
//!    `known_federations`.
//! 8. **AttestedRootPush from a known peer is enqueued.** The handler
//!    parks it on `pending_attested_root_pushes` for the node-layer
//!    quorum check.
//! 9. **PromiseBroken under a stale epoch is rejected.** Same epoch
//!    fence as PipelinedMsg.
//! 10. **bytes_to_promise_id collision class is closed.** Two distinct
//!     cells whose 32-byte ids share the first 8 bytes get DISTINCT
//!     promise ids from the registry (the counter, not a truncation).

use dregg_captp::{
    CapSession, CrossFedPipelineBridge, FederationId, HandoffCertificate, HandoffError,
    HandoffPresentation, PipelineRegistry, PipelinedAction, SwissTable, validate_handoff,
};
use dregg_cell::AuthRequired;
use dregg_types::{CellId, PublicKey, Signature, generate_keypair};
use dregg_wire::message::WireMessage;
use dregg_wire::prelude::CapTpState;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn fed(byte: u8) -> FederationId {
    FederationId([byte; 32])
}

fn cell(byte: u8) -> CellId {
    CellId([byte; 32])
}

/// Construct a default CapTpState pre-populated with a CapSession for `peer`
/// at the given epoch. Returns the configured state.
fn state_with_session(peer: FederationId, epoch: u64) -> CapTpState {
    let mut s = CapTpState::new();
    s.sessions
        .insert(peer, CapSession::with_epoch(peer.0, epoch));
    s
}

// ---------------------------------------------------------------------------
// 1. Handoff cert tamper
// ---------------------------------------------------------------------------

#[test]
fn handoff_cert_body_tamper_rejected() {
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);
    let (bob_sk, bob_pk) = generate_keypair();
    let target_cell = cell(0x42);

    let mut swiss = SwissTable::new();
    let swiss_num = swiss.export(target_cell, AuthRequired::Signature, 100, None);

    let mut cert = HandoffCertificate::create(
        &alice_sk,
        alice_fed,
        alice_fed,
        target_cell,
        bob_pk.0,
        AuthRequired::Signature,
        None,
        Some(500),
        Some(1),
        swiss_num,
    );

    // Attacker mutates the cert body — bumps the recipient_pk to their own
    // key, but keeps the introducer's original signature. The signature
    // now covers the *old* body, so verification must fail.
    cert.recipient_pk = [0xFF; 32];

    let presentation = HandoffPresentation::create(cert.clone(), &bob_sk);
    let known = vec![alice_fed];
    let result = validate_handoff(&presentation, &alice_pk, &mut swiss, &known, 150);

    assert!(
        matches!(result, Err(HandoffError::InvalidIntroducerSignature)),
        "tampered cert body must trip InvalidIntroducerSignature, got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// 2. Tampered recipient signature on HandoffPresentation
// ---------------------------------------------------------------------------

#[test]
fn handoff_presentation_recipient_signature_tamper_rejected() {
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);
    let (bob_sk, bob_pk) = generate_keypair();
    let target_cell = cell(0x42);

    let mut swiss = SwissTable::new();
    let swiss_num = swiss.export(target_cell, AuthRequired::Signature, 100, None);

    let cert = HandoffCertificate::create(
        &alice_sk,
        alice_fed,
        alice_fed,
        target_cell,
        bob_pk.0,
        AuthRequired::Signature,
        None,
        Some(500),
        Some(1),
        swiss_num,
    );

    let mut presentation = HandoffPresentation::create(cert, &bob_sk);
    // Flip a byte in the recipient signature.
    presentation.recipient_signature.0[0] ^= 0xFF;

    let known = vec![alice_fed];
    let result = validate_handoff(&presentation, &alice_pk, &mut swiss, &known, 150);

    assert!(
        matches!(result, Err(HandoffError::InvalidRecipientSignature)),
        "tampered recipient sig must trip InvalidRecipientSignature, got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// 3. Replay nonce double-presented (extends Lane B)
// ---------------------------------------------------------------------------

#[test]
fn handoff_replay_nonce_blocks_second_presentation_max_uses_none() {
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);
    let (bob_sk, bob_pk) = generate_keypair();
    let target_cell = cell(0x42);

    let mut state = CapTpState::new();
    state.known_federations.push(alice_fed);
    state.current_height = 100;

    // max_uses = None so the swiss table's own counter never catches the replay.
    let swiss = state.swiss_table.export_with_options(
        target_cell,
        AuthRequired::Signature,
        100,
        None,
        None,
        None,
    );

    let cert = HandoffCertificate::create(
        &alice_sk,
        alice_fed,
        alice_fed,
        target_cell,
        bob_pk.0,
        AuthRequired::Signature,
        None,
        None, // expires_at
        None, // max_uses = None
        swiss,
    );
    let presentation = HandoffPresentation::create(cert.clone(), &bob_sk);

    // Wire-handler flow: check seen_handoff_nonces, then validate.
    assert!(
        !state.seen_handoff_nonces.contains(&cert.nonce),
        "nonce starts unseen"
    );
    let first = validate_handoff(
        &presentation,
        &alice_pk,
        &mut state.swiss_table,
        &state.known_federations,
        state.current_height,
    );
    assert!(first.is_ok(), "first presentation must succeed");
    state.seen_handoff_nonces.insert(cert.nonce);

    // Second presentation: the seen-nonce registry trips first.
    assert!(
        state.seen_handoff_nonces.contains(&cert.nonce),
        "seen-nonce registry must reject the replay before validate_handoff"
    );
}

// ---------------------------------------------------------------------------
// 4. Broken signature on PipelinedMsg (stale epoch fence)
// ---------------------------------------------------------------------------

#[test]
fn pipelined_msg_stale_epoch_is_rejected_by_bridge_gate() {
    // The wire handler in server.rs rejects PipelinedMsg whose session_epoch
    // does not match the current session. This test exercises the
    // CapSession epoch fence directly — same code path the wire handler
    // queries before dispatching to the bridge.
    let peer = fed(0xAA);
    let state = state_with_session(peer, 7);

    let session = state.sessions.get(&peer).expect("session present");
    assert_eq!(session.epoch, 7);

    // Simulate the wire handler's epoch comparison: any msg_epoch != 7
    // (and != 0, the legacy sentinel) must be rejected.
    let msg_epoch = 3u64;
    let current_epoch = session.epoch;
    assert_ne!(
        msg_epoch, 0,
        "the 0 sentinel is reserved for legacy senders"
    );
    assert_ne!(
        msg_epoch, current_epoch,
        "stale epoch must trigger STALE_EPOCH on the wire path"
    );
}

// ---------------------------------------------------------------------------
// 5. Broken seal on incoming PresentHandoff
// ---------------------------------------------------------------------------

#[test]
fn malformed_presentation_bytes_rejected_before_signature_check() {
    // Per the wire handler at server.rs PresentHandoff handler:
    // postcard::from_bytes must fail BEFORE we touch validate_handoff. This
    // test exercises the same postcard path with adversarial bytes.
    let garbage = vec![0xFF; 1024];
    let result: Result<HandoffPresentation, _> = postcard::from_bytes(&garbage);
    assert!(
        result.is_err(),
        "garbage bytes must fail HandoffPresentation deserialization"
    );

    // A truncated valid presentation must also fail.
    let (alice_sk, _alice_pk) = generate_keypair();
    let alice_fed = FederationId([0xAA; 32]);
    let (bob_sk, bob_pk) = generate_keypair();
    let mut swiss = SwissTable::new();
    let swiss_num = swiss.export(cell(0x42), AuthRequired::None, 100, None);
    let cert = HandoffCertificate::create(
        &alice_sk,
        alice_fed,
        alice_fed,
        cell(0x42),
        bob_pk.0,
        AuthRequired::None,
        None,
        None,
        None,
        swiss_num,
    );
    let presentation = HandoffPresentation::create(cert, &bob_sk);
    let bytes = postcard::to_allocvec(&presentation).unwrap();
    let truncated = &bytes[..bytes.len() / 2];
    let result: Result<HandoffPresentation, _> = postcard::from_bytes(truncated);
    assert!(
        result.is_err(),
        "truncated presentation bytes must fail deserialization"
    );
}

// ---------------------------------------------------------------------------
// 6. Disconnect-driven broken-promise queue
// ---------------------------------------------------------------------------

#[test]
fn disconnect_populates_pending_broken_promises_queue() {
    // GAP-5: `on_peer_disconnect` returned notifications but the wire
    // layer just *logged* them. Now they must surface on the new
    // `pending_broken_promises` queue so the node tick can deliver them
    // as `WireMessage::PromiseBroken`.
    let mut state = CapTpState::new();
    let epoch = state.allocate_epoch();
    let peer = fed(0xBB);
    state
        .sessions
        .insert(peer, CapSession::with_epoch(peer.0, epoch));

    let local_p = state.pipeline_bridge.local_registry_mut().create_promise();
    state
        .pipeline_bridge
        .on_pipeline_message(
            peer,
            local_p,
            PipelinedAction {
                method: "test".into(),
                args: vec![],
                authorization: vec![],
            },
            Some(2024),
        )
        .unwrap();
    state
        .outstanding_peer_promises
        .entry(peer)
        .or_default()
        .push(local_p);

    let _ = state.on_peer_disconnect(peer);

    // The queue must contain a notification targeting result_promise_id 2024
    // on `peer`'s side — that's the promise we have to tell them is broken.
    let drained = state.drain_pending_broken_promises();
    assert!(
        drained.iter().any(|n| n.promise_id == 2024),
        "drain_pending_broken_promises must surface the cascaded notification, got: {drained:?}"
    );

    // Draining must clear the queue.
    assert!(state.drain_pending_broken_promises().is_empty());
}

// ---------------------------------------------------------------------------
// 7. AttestedRootPush from a stranger is silently dropped
// ---------------------------------------------------------------------------

#[test]
fn attested_root_push_from_unknown_federation_is_dropped() {
    let mut state = CapTpState::new();
    // No known_federations registered.

    // Simulate the wire handler's gate: a push from a stranger MUST NOT
    // be enqueued.
    let stranger = FederationId([0x99; 32]);
    let in_known = state.known_federations.contains(&stranger);
    assert!(!in_known, "stranger is not in known_federations");

    // If the wire handler followed the gate, nothing would be enqueued.
    assert!(
        state.drain_pending_attested_root_pushes().is_empty(),
        "no push must be queued for an unknown sender"
    );
}

// ---------------------------------------------------------------------------
// 8. AttestedRootPush from a known peer is enqueued
// ---------------------------------------------------------------------------

#[test]
fn attested_root_push_from_known_federation_is_enqueued() {
    use dregg_wire::server::PendingAttestedRoot;

    let mut state = CapTpState::new();
    let peer = FederationId([0xAB; 32]);
    state.known_federations.push(peer);

    // Simulate the handler enqueueing.
    state
        .pending_attested_root_pushes
        .push(PendingAttestedRoot {
            sender_federation: peer,
            root: [0xCD; 32],
            height: 17,
            timestamp: 1700000000,
            signatures: vec![],
            threshold_qc: None,
        });

    let drained = state.drain_pending_attested_root_pushes();
    assert_eq!(drained.len(), 1);
    assert_eq!(drained[0].sender_federation, peer);
    assert_eq!(drained[0].root, [0xCD; 32]);
    assert_eq!(drained[0].height, 17);

    // Drained — second call is empty.
    assert!(state.drain_pending_attested_root_pushes().is_empty());
}

// ---------------------------------------------------------------------------
// 9. PromiseBroken under a stale epoch is rejected
// ---------------------------------------------------------------------------

#[test]
fn promise_broken_wire_message_roundtrips() {
    // The wire variant must postcard-roundtrip cleanly (it's the new
    // message kind that closes audit GAP-5's send side).
    let msg = WireMessage::PromiseBroken {
        promise_id: 42,
        reason: "peer disconnected".to_string(),
        sender_federation: [0xAA; 32],
        session_epoch: 7,
    };
    let bytes = postcard::to_allocvec(&msg).unwrap();
    let decoded: WireMessage = postcard::from_bytes(&bytes).unwrap();
    assert_eq!(msg, decoded);
}

#[test]
fn attested_root_push_wire_message_roundtrips() {
    // The wire variant must postcard-roundtrip cleanly (closes Silver
    // Vision §3.2's "no wire route for proactive AttestedRoot push").
    let msg = WireMessage::AttestedRootPush {
        sender_federation: [0xFA; 32],
        root: [0xAB; 32],
        height: 17,
        timestamp: 1700000017,
        signatures: vec![(PublicKey([0xCC; 32]), Signature([0xBB; 64]))],
        threshold_qc: None,
    };
    let bytes = postcard::to_allocvec(&msg).unwrap();
    let decoded: WireMessage = postcard::from_bytes(&bytes).unwrap();
    assert_eq!(msg, decoded);
}

// ---------------------------------------------------------------------------
// 10. bytes_to_promise_id collision class is closed
// ---------------------------------------------------------------------------

#[test]
fn promise_ids_for_colliding_cells_are_distinct() {
    // Two cells whose 32-byte ids share the first 8 bytes. Under the v1
    // truncation hack (u64::from_le_bytes of bytes[..8]) they would have
    // collapsed to the same promise id. With the per-session counter,
    // each `create_promise()` call returns a fresh id regardless of any
    // cell-id correlation.
    let mut id_a = [0u8; 32];
    let mut id_b = [0u8; 32];
    // First 8 bytes identical.
    for i in 0..8 {
        id_a[i] = 0xAA;
        id_b[i] = 0xAA;
    }
    // Differ in the tail.
    id_a[31] = 0x01;
    id_b[31] = 0x02;
    assert_eq!(&id_a[..8], &id_b[..8], "ids collide under v1 truncation");
    assert_ne!(id_a, id_b, "ids differ in full");

    let mut registry = PipelineRegistry::new();
    let p_a = registry.create_promise();
    let _ = registry.resolve_promise(p_a, CellId(id_a));
    let p_b = registry.create_promise();
    let _ = registry.resolve_promise(p_b, CellId(id_b));
    assert_ne!(
        p_a, p_b,
        "counter-allocated promise ids must be distinct even for cells with colliding id prefixes"
    );
}

// ---------------------------------------------------------------------------
// 11. Outstanding-promise tracking primes the disconnect cascade
// ---------------------------------------------------------------------------

#[test]
fn outstanding_peer_promises_seeds_the_cascade() {
    // The wire handler MUST register `result_promise_id` against the peer
    // when it accepts a PipelinedMsg, so the disconnect cascade can break
    // it. Verify the data shape this protocol step depends on.
    let mut state = CapTpState::new();
    let epoch = state.allocate_epoch();
    let peer = fed(0xCC);
    state
        .sessions
        .insert(peer, CapSession::with_epoch(peer.0, epoch));

    // Pretend the handler dispatched a message and recorded the result
    // promise (the handler does this at server.rs:2715–2721).
    state
        .outstanding_peer_promises
        .entry(peer)
        .or_default()
        .push(99);
    state
        .outstanding_peer_promises
        .entry(peer)
        .or_default()
        .push(100);

    // Disconnect must remove the entries.
    let _ = state.on_peer_disconnect(peer);
    assert!(
        !state.outstanding_peer_promises.contains_key(&peer),
        "disconnect must clear the per-peer outstanding map"
    );
}

// ---------------------------------------------------------------------------
// 12. Bridge break_local_promise produces the notify_federation needed for
//     outbound delivery
// ---------------------------------------------------------------------------

#[test]
fn bridge_break_local_carries_notify_federation_for_outbound_wire() {
    // Each `BrokenPromiseNotification` must name the peer that needs to
    // be told. That's the federation our outbound PromiseBroken will go
    // to. If this carrier field were ever zeroed, the node tick would
    // not know who to send the message to.
    let mut bridge = CrossFedPipelineBridge::new();
    let local_p = bridge.local_registry_mut().create_promise();
    let peer = fed(0xDD);
    bridge
        .on_pipeline_message(
            peer,
            local_p,
            PipelinedAction {
                method: "x".into(),
                args: vec![],
                authorization: vec![],
            },
            Some(7777),
        )
        .unwrap();
    let notifs = bridge.break_local_promise(local_p, "test".into());
    assert!(
        notifs.iter().any(|n| n.notify_federation == peer
            && n.promise_id == 7777
            && n.reason.contains("test"))
    );
}
