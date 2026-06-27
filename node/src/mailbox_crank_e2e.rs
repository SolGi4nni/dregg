//! E2E: the mailbox crank over the REAL relay routes (ORGANS §2).
//!
//! Agent A sends a SEALED turn-intent to agent B's hosted relay inbox while
//! B is offline (B's crank is simply not running). B's crank later drains
//! the relay over the actual HTTP drain route, the fail-closed
//! executor-anchored sender gate admits A, the intent executes as a turn on
//! B's cell through the SDK's normal `.turn()` path, and the custody
//! receipt (the relay's dequeue proof + the proof-covered content hash,
//! re-derived from the delivered body) is checkable against the relay's
//! `/relay/proof/:msg_id` route.
//!
//! The inbox CELL rides the storage-template CapInbox factory — the same
//! descriptor `starbridge_seed` now registers at node boot — born on B's
//! runtime via `CreateCellFromFactory`, adopted, and its slot-5 sender-set
//! root mutated only by executor-admitted `grant_sender` turns.
//!
//! Negative: a sender that was never granted drains through the same crank
//! and is REFUSED (`UnauthorizedSender`) with no state change — the custody
//! receipt still records the relay's proof.
#![cfg(test)]

use std::sync::Arc;

use dregg_captp::FederationId;
use dregg_captp::store_forward::generate_x25519_keypair;
use dregg_cell::{AuthRequired, CapabilityRef, Cell, CellId, CellMode, FactoryCreationParams};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, Effect};
use dregg_sdk_net::mailbox::{
    CrankDisposition, MailboxCrank, MailboxTurnIntent, RefusalReason, RelayHttpTransport,
    seal_intent,
};
// E2E fixture still constructs the legacy RelayOperator directly (factory migration is separate).
#[allow(deprecated)]
use dregg_storage::operator::RelayOperator;
use dregg_storage_templates::cap_inbox;
use tokio::sync::RwLock;

use crate::relay_service::{RelayConfig, RelayState, RelayTemplateState, relay_router};

/// Spawn the REAL relay router on an ephemeral port inside a background
/// runtime thread; return its base URL.
#[allow(deprecated)] // constructs the legacy RelayOperator directly for the E2E fixture
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

/// Birth B's inbox cell from the CapInbox factory on B's runtime (the same
/// descriptor the node seeds at boot), fund + adopt it, and return its id.
fn birth_inbox(runtime: &mut AgentRuntime, owner_pk: [u8; 32]) -> CellId {
    let descriptor = cap_inbox::cap_inbox_factory_descriptor();
    let factory_vk = descriptor.factory_vk;
    let program_vk = descriptor.child_program_vk;
    runtime.deploy_factory(descriptor);

    let token_id = *blake3::hash(b"mailbox-e2e-inbox").as_bytes();
    let inbox = CellId::derive_raw(&owner_pk, &token_id);

    // Creation-time field constraints: cursors/deposits zero, capacity and
    // min_deposit in range, owner non-zero.
    let params = FactoryCreationParams {
        mode: CellMode::Hosted,
        program_vk,
        initial_fields: vec![
            (cap_inbox::HEAD_SEQ_SLOT as u32, 0),
            (cap_inbox::TAIL_SEQ_SLOT as u32, 0),
            (cap_inbox::CAPACITY_SLOT as u32, 64),
            (cap_inbox::MIN_DEPOSIT_SLOT as u32, 1),
            (cap_inbox::OWNER_PK_HASH_SLOT as u32, 1),
            (cap_inbox::TOTAL_DEPOSITS_SLOT as u32, 0),
        ],
        initial_caps: vec![],
        owner_pubkey: owner_pk,
    };

    runtime
        .turn()
        .effect(Effect::CreateCellFromFactory {
            factory_vk,
            owner_pubkey: owner_pk,
            token_id,
            params,
        })
        .sign()
        .expect("sign create")
        .submit()
        .expect("inbox cell birth commits");

    // Fund the inbox for the adopt turn's fee, then the one-time adopt
    // self-grant (the c-list capability the `.on(inbox)` parent gate needs).
    runtime
        .turn()
        .transfer(inbox, 5_000)
        .sign()
        .expect("sign fund")
        .submit()
        .expect("inbox funding commits");
    runtime
        .turn()
        .as_cell(inbox, 2_000)
        .grant(
            runtime.cell_id(),
            CapabilityRef {
                target: inbox,
                slot: 0,
                permissions: AuthRequired::Signature,
                breadstuff: None,
                expires_at: None,
                allowed_effects: None,
                stored_epoch: None,
            },
        )
        .sign()
        .expect("sign adopt")
        .submit()
        .expect("adopt self-grant commits");

    inbox
}

#[test]
fn offline_sealed_send_drains_executes_and_custody_receipt_checks() {
    let base_url = spawn_relay();

    // ── B: runtime, inbox cell (CapInbox factory), relay subscription ──
    let mut b_runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), "mailbox-e2e");
    let b_pk = b_runtime.cipherclerk().read().unwrap().public_key().0;
    let inbox_cell = birth_inbox(&mut b_runtime, b_pk);
    let (b_x_secret, b_x_public) = generate_x25519_keypair();

    // A destination cell on B's runtime for the deferred transfer.
    let dest = {
        let cell = Cell::with_balance([0xC1; 32], [0u8; 32], 0);
        let id = cell.id();
        b_runtime
            .ledger()
            .lock()
            .unwrap()
            .insert_cell(cell)
            .expect("dest cell");
        id
    };

    let b_transport =
        RelayHttpTransport::new(&base_url, b_runtime.cipherclerk().clone()).expect("b transport");
    b_transport
        .subscribe(Some(8), Some(1))
        .expect("relay subscribe");

    let mut crank = MailboxCrank::new(&b_runtime, inbox_cell, b_x_secret, b_transport);

    // ── A: identity + authorization (an executor-admitted grant_sender) ──
    let a_cclerk = AgentCipherclerk::new();
    let a_pk = a_cclerk.public_key().0;
    let (a_x_secret, _) = generate_x25519_keypair();
    crank
        .grant_sender(a_pk)
        .expect("grant_sender turn commits through the executor");
    {
        // The executor-committed slot-5 root anchors the crank's opening.
        let ledger = b_runtime.ledger().lock().unwrap();
        let root = ledger.get(&inbox_cell).unwrap().state.fields
            [dregg_sdk_net::mailbox::SENDER_SET_ROOT_SLOT];
        assert_ne!(root, [0u8; 32], "grant must commit a non-zero sender root");
    }

    // ── A sends a SEALED turn-intent while B is offline (crank idle) ──
    let intent = MailboxTurnIntent {
        target: b_runtime.cell_id(),
        method: "execute".into(),
        effects: vec![Effect::Transfer {
            from: b_runtime.cell_id(),
            to: dest,
            amount: 7,
        }],
    };
    let sealed = seal_intent(&intent, FederationId(b_pk), &b_x_public, &a_x_secret, 0);
    let a_transport = RelayHttpTransport::new(
        &base_url,
        std::sync::Arc::new(std::sync::RwLock::new(a_cclerk)),
    )
    .expect("a transport");
    a_transport
        .send(&b_pk, &a_pk, &sealed, 100)
        .expect("relay accepts the sealed send");

    // ── B comes online: the crank drains, gates, and executes ──
    let report = crank.crank_once(10).expect("crank pass");
    assert_eq!(report.executed(), 1, "report: {report:?}");
    assert_eq!(report.refused(), 0);

    // The deferred turn executed on B's cell.
    {
        let ledger = b_runtime.ledger().lock().unwrap();
        assert_eq!(
            ledger.get(&dest).unwrap().state.balance(),
            7,
            "the sealed intent's transfer must have committed on B's cell"
        );
    }

    // ── Custody receipt is checkable ──
    let receipt = &crank.receipts()[0];
    assert!(
        receipt.proof_ok,
        "the relay's dequeue proof must verify (head-binding + exact post-root)"
    );
    assert!(receipt.payload_binding_ok, "body re-hashed to content_hash");
    assert!(receipt.executed_turn_receipt.is_some());
    assert_eq!(receipt.sender, a_pk);
    // The relay's proof route returns the SAME dequeue proof the drain
    // delivered — old/new roots match the receipt.
    let b_check = RelayHttpTransport::new(&base_url, b_runtime.cipherclerk().clone())
        .expect("check transport");
    let proof = b_check
        .proof(&receipt.content_hash)
        .expect("proof route answers");
    assert!(proof.found, "relay must hold the dequeue proof");
    let hex = |b: &[u8; 32]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
    assert_eq!(proof.old_root, hex(&receipt.proof_old_root));
    assert_eq!(proof.new_root, hex(&receipt.proof_new_root));

    // ── Negative: an ungranted sender is refused, fail-closed ──
    let e_cclerk = AgentCipherclerk::new();
    let e_pk = e_cclerk.public_key().0;
    let (e_x_secret, _) = generate_x25519_keypair();
    let evil = MailboxTurnIntent {
        target: b_runtime.cell_id(),
        method: "execute".into(),
        effects: vec![Effect::Transfer {
            from: b_runtime.cell_id(),
            to: dest,
            amount: 1_000,
        }],
    };
    let sealed_evil = seal_intent(&evil, FederationId(b_pk), &b_x_public, &e_x_secret, 0);
    a_transport
        .send(&b_pk, &e_pk, &sealed_evil, 100)
        .expect("relay accepts the bytes (auth is the recipient's gate)");

    let report2 = crank.crank_once(10).expect("crank pass 2");
    assert_eq!(report2.executed(), 0);
    assert_eq!(report2.refused(), 1);
    assert!(matches!(
        report2.outcomes[0].disposition,
        CrankDisposition::Refused(RefusalReason::UnauthorizedSender)
    ));
    {
        let ledger = b_runtime.ledger().lock().unwrap();
        assert_eq!(
            ledger.get(&dest).unwrap().state.balance(),
            7,
            "the refused intent must not have executed"
        );
    }
    // Custody of the refused message is still recorded (proof + binding
    // verified, no execution receipt).
    let refused = &crank.receipts()[1];
    assert!(refused.proof_ok);
    assert!(refused.payload_binding_ok);
    assert!(refused.executed_turn_receipt.is_none());
}
