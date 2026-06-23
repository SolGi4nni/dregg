//! E2E: a CROSS-NODE CapTP capability HANDOFF over the REAL relay HTTP routes.
//!
//! The robigalia vision made concrete: a capability relocates across machines.
//! Node A holds a cap to a cell (recorded as a swiss entry at B — B's
//! authoritative `held` record). A introduces a recipient to that cap by minting
//! an introducer-signed [`HandoffCertificate`]; the recipient signs a
//! [`HandoffPresentation`]. A seals the presentation into the store-and-forward
//! envelope and POSTs it to B's hosted inbox over the ACTUAL
//! `POST /relay/send/:dest` route (the same node relay that carries every other
//! federation message — `relay_service::relay_router`). B drains it over the
//! real `GET /relay/drain` route, unseals it, and runs the PROVEN
//! [`dregg_captp::validate_handoff`] against ITS OWN swiss table + trusted
//! introducer set. On success B resolves the acceptance into a live
//! [`dregg_captp::SendCap`] and EXERCISES it on a real data-plane
//! [`dregg_captp::data_plane::Bus`] — a committed custody receipt: the
//! handed-off authority genuinely works on B.
//!
//! Two assertions carry the security claim:
//!   * (positive) an ATTENUATING handoff (held = Either, granted = Signature)
//!     is accepted, resolved, and the cap works on B — bounded by what A held.
//!   * (negative) an OVER-BROAD handoff (held = Signature, granted = None — an
//!     amplification attempt) is REFUSED by B's validator as
//!     [`dregg_captp::HandoffError::Amplification`]; B installs no cap.
//!
//! This is the missing rung-7 leg of the federation census: `PresentHandoff`
//! ROUTED over the node↔node transport, verified + installed on the receiver.
#![cfg(test)]

use std::sync::Arc;

use dregg_captp::data_plane::{Bus, ChannelName, DataPlaneError, SendCap};
use dregg_captp::handoff::{
    HandoffCertificate, HandoffError, HandoffPresentation, validate_handoff,
};
use dregg_captp::handoff_session::PresentHandoffFrame;
use dregg_captp::store_forward::{
    BlocklaceEnvelope, generate_x25519_keypair, queue_via_blocklace,
};
use dregg_captp::sturdy::SwissTable;
use dregg_captp::FederationId;
use dregg_cell::{AuthRequired, CellId};
use dregg_sdk::AgentCipherclerk;
use dregg_sdk_net::mailbox::{MailboxTransport, RelayHttpTransport};
use dregg_storage::operator::RelayOperator;
use dregg_types::{generate_keypair, PublicKey, SigningKey};
use tokio::sync::RwLock;

use crate::relay_service::{
    relay_router, RelayConfig, RelayState, RelayTemplateState,
};

/// Spawn the REAL relay HTTP router on an ephemeral port; return its base URL.
/// (Same shape as `mailbox_crank_e2e::spawn_relay`.)
fn spawn_relay() -> String {
    let config = RelayConfig {
        operator_key: [0xAA; 32],
        bond_amount: 10_000,
        max_total_capacity: 100_000,
        default_inbox_capacity: 8,
        default_min_deposit: 1,
        ..RelayConfig::default()
    };
    let state = Arc::new(RwLock::new(RelayState {
        operator: RelayOperator::new(
            config.operator_key,
            config.bond_amount,
            config.max_delivery_latency_blocks,
        ),
        template: RelayTemplateState::new(&config),
        config,
        current_height: 0,
        delivery_proofs: std::collections::HashMap::new(),
        messages_delivered: 0,
        messages_received: 0,
    }));
    let router = relay_router(state);

    let listener = std::net::TcpListener::bind("127.0.0.1:0").expect("bind relay port");
    let addr = listener.local_addr().expect("local addr");
    listener.set_nonblocking(true).expect("nonblocking");

    std::thread::spawn(move || {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .expect("relay test runtime");
        rt.block_on(async move {
            let listener = tokio::net::TcpListener::from_std(listener).expect("tokio listener");
            axum::serve(listener, router).await.expect("relay serve");
        });
    });

    format!("http://{addr}")
}

/// Build a handoff scenario: an introducer/holder (node A) registers a swiss
/// entry at the target (node B) recording `held` authority, then mints a cert
/// granting `granted` authority to a fresh recipient. Returns the presentation,
/// the introducer pk, the introducer federation id, B's swiss table, and the
/// target cell.
fn scenario(
    held: AuthRequired,
    granted: AuthRequired,
) -> (HandoffPresentation, [u8; 32], FederationId, SwissTable, CellId) {
    let (intro_sk, intro_pk): (SigningKey, PublicKey) = generate_keypair();
    let intro_fed = FederationId(intro_pk.0);
    let (recip_sk, recip_pk) = generate_keypair();
    let target_fed = FederationId([0xDD; 32]);
    let target_cell = CellId([0xEE; 32]);

    let mut swiss_table = SwissTable::new();
    let swiss = swiss_table.export(target_cell, held, 100, None);

    let cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0,
        granted,
        None,
        None,
        None,
        swiss,
    );
    let presentation = HandoffPresentation::create(cert, &recip_sk);
    (presentation, intro_pk.0, intro_fed, swiss_table, target_cell)
}

/// THE CROSS-NODE HANDOFF, BY RUNNING over the real relay HTTP routes.
///
/// A seals a `PresentHandoffFrame` and POSTs it to B's inbox over actual HTTP;
/// B drains it over the real drain route, validates, resolves a cap, and uses
/// it. An over-broad handoff is refused.
#[test]
fn cross_node_cap_handoff_over_the_relay_routes() {
    let base_url = spawn_relay();

    // B's identity: a cipherclerk for relay drain-auth + an X25519 keypair the
    // store-and-forward envelope seals to. A only needs an X25519 secret.
    let b_clerk = Arc::new(std::sync::RwLock::new(AgentCipherclerk::new()));
    let b_pk = b_clerk.read().unwrap().public_key().0;
    let (b_x_secret, b_x_public) = generate_x25519_keypair();
    let (a_x_secret, _a_x_public) = generate_x25519_keypair();

    // B subscribes: create its hosted inbox on the relay.
    let mut b_transport =
        RelayHttpTransport::new(&base_url, b_clerk.clone()).expect("b transport");
    b_transport
        .subscribe(Some(64), Some(1))
        .expect("B subscribes a hosted inbox");

    // A's transport (a fresh cipherclerk identity; A authenticates only its own
    // sends, which the relay does not gate — recipient gating is at B).
    let a_clerk = Arc::new(std::sync::RwLock::new(AgentCipherclerk::new()));
    let a_transport = RelayHttpTransport::new(&base_url, a_clerk).expect("a transport");

    // ── (1) POSITIVE: an attenuating handoff (held Either ⊇ granted Signature).
    let (presentation, intro_pk, intro_fed, mut swiss_table, target_cell) =
        scenario(AuthRequired::Either, AuthRequired::Signature);
    let known = vec![intro_fed]; // B trusts A's introducer federation.

    // A frames the presentation and seals it to B over the store-and-forward
    // envelope (the same primitive `seal_intent` uses), then SENDS over HTTP.
    let frame = PresentHandoffFrame {
        presentation_bytes: postcard::to_stdvec(&presentation).unwrap(),
        introducer_pk: intro_pk,
    };
    let frame_bytes = postcard::to_stdvec(&frame).unwrap();
    let sealed = queue_via_blocklace(FederationId(b_pk), &frame_bytes, &b_x_public, &a_x_secret, 0);
    a_transport
        .send(&b_pk, &a_transport.owner_pk(), &sealed, 100)
        .expect("A sends the handoff over the real relay route");

    // ── B drains over the REAL drain route, unseals, validates, resolves.
    let drained = b_transport.drain(8).expect("B drains its inbox");
    assert_eq!(drained.len(), 1, "B drained exactly the handoff frame");
    let envelope =
        BlocklaceEnvelope::from_payload(&drained[0].payload).expect("parse sealed envelope");
    let plaintext = envelope.decrypt(&b_x_secret).expect("B unseals the frame");
    let recv_frame: PresentHandoffFrame =
        postcard::from_bytes(&plaintext).expect("decode handoff frame");
    let recv_presentation: HandoffPresentation =
        postcard::from_bytes(&recv_frame.presentation_bytes).expect("decode presentation");

    let acceptance = validate_handoff(
        &recv_presentation,
        &PublicKey(recv_frame.introducer_pk),
        &mut swiss_table,
        &known,
        150,
    )
    .expect("B validates the attenuating handoff");

    // (a) Authority bound: resolved grant ⊆ what A held (Either).
    assert_eq!(acceptance.cell_id, target_cell);
    assert_eq!(acceptance.permissions, AuthRequired::Signature);
    assert!(
        acceptance
            .permissions
            .is_narrower_or_equal(&AuthRequired::Either),
        "resolved grant must be bounded by the introducer's held authority"
    );

    // (b) THE CAP WORKS ON B: resolve into a SendCap, exercise on a real Bus.
    let (relay_sk, relay_pk) = generate_keypair();
    let mut bus = Bus::new(FederationId(relay_pk.0), relay_sk, 64, 256);
    let recipient = FederationId(acceptance.cell_id.0);
    let channel = ChannelName::new(b"cross-node-handoff".to_vec());
    let cap = SendCap::grant(recipient, channel.clone(), acceptance.permissions.clone());
    let delivery = bus
        .enqueue(
            &cap,
            recipient,
            &channel,
            AuthRequired::Signature, // offered ⊆ granted
            b"a real turn through the cross-node handed-off cap".to_vec(),
            1,
        )
        .expect("the handed-off cap must work on B");
    assert_ne!(delivery.content_hash, [0u8; 32], "a committed custody receipt");

    // And using the cap BEYOND its grant is refused at the Bus seam.
    let over = bus.enqueue(
        &cap,
        recipient,
        &channel,
        AuthRequired::None,
        b"over-broad use".to_vec(),
        2,
    );
    assert!(
        matches!(over, Err(DataPlaneError::Unauthorized { .. })),
        "using the handed-off cap beyond its grant must be refused"
    );

    // ── (2) NEGATIVE: an over-broad handoff (held Signature, granted None) is
    //     REFUSED by B's validator as amplification — no cap is installed.
    let (amp_presentation, amp_intro_pk, amp_intro_fed, mut amp_swiss, _amp_cell) =
        scenario(AuthRequired::Signature, AuthRequired::None);
    let amp_known = vec![amp_intro_fed];

    let amp_frame = PresentHandoffFrame {
        presentation_bytes: postcard::to_stdvec(&amp_presentation).unwrap(),
        introducer_pk: amp_intro_pk,
    };
    let amp_bytes = postcard::to_stdvec(&amp_frame).unwrap();
    let amp_sealed =
        queue_via_blocklace(FederationId(b_pk), &amp_bytes, &b_x_public, &a_x_secret, 1);
    a_transport
        .send(&b_pk, &a_transport.owner_pk(), &amp_sealed, 100)
        .expect("A sends the amplifying handoff over the relay");

    let amp_drained = b_transport.drain(8).expect("B drains the second message");
    assert_eq!(amp_drained.len(), 1);
    let amp_env =
        BlocklaceEnvelope::from_payload(&amp_drained[0].payload).expect("parse amp envelope");
    let amp_plain = amp_env.decrypt(&b_x_secret).expect("unseal amp frame");
    let amp_recv: PresentHandoffFrame = postcard::from_bytes(&amp_plain).unwrap();
    let amp_recv_pres: HandoffPresentation =
        postcard::from_bytes(&amp_recv.presentation_bytes).unwrap();

    let amp_result = validate_handoff(
        &amp_recv_pres,
        &PublicKey(amp_recv.introducer_pk),
        &mut amp_swiss,
        &amp_known,
        150,
    );
    assert_eq!(
        amp_result.unwrap_err(),
        HandoffError::Amplification,
        "B must REFUSE an over-broad handoff (granted ⊄ held) as amplification"
    );
}
