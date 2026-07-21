//! Hostile receipt-log tests for the node/SDK boundary.
//!
//! A node observes one immutable append-only log, while every agent owns an
//! independent causal receipt chain. These tests pin the distinction: global
//! append order must never become an excuse to rewrite an executor-signed
//! receipt's predecessor.

mod common;

use dregg_sdk::ChainAppendError;
use dregg_turn::{
    TurnReceipt, sign_receipt, verify_receipt_chain, verify_receipt_signature_with_keys,
};

fn signed(mut receipt: TurnReceipt, seed: &[u8; 32]) -> TurnReceipt {
    receipt.executor_signature = Some(sign_receipt(&receipt, seed));
    receipt
}

#[test]
fn two_agents_interleave_without_cross_linking_their_causal_chains() {
    let mut clerk = common::cclerk_from_label("interleaved-node-log");
    let alice = clerk.cell_id("alice");
    let bob = clerk.cell_id("bob");

    let alice_1 = common::mock_receipt(alice, [0x10; 32], [0x11; 32]);
    clerk.append_receipt(alice_1.clone()).unwrap();
    let alice_1_hash = alice_1.receipt_hash();

    let bob_1 = common::mock_receipt(bob, [0x20; 32], [0x21; 32]);
    clerk.append_receipt(bob_1.clone()).unwrap();
    let bob_1_hash = bob_1.receipt_hash();

    let alice_2 = common::mock_receipt_with_prev(alice, [0x11; 32], [0x12; 32], Some(alice_1_hash));
    clerk.append_receipt(alice_2.clone()).unwrap();

    let bob_2 = common::mock_receipt_with_prev(bob, [0x21; 32], [0x22; 32], Some(bob_1_hash));
    clerk.append_receipt(bob_2.clone()).unwrap();

    assert_eq!(clerk.receipt_log_length(), 4, "the node log is total");
    assert_eq!(clerk.agent_receipt_count(&alice), 2);
    assert_eq!(clerk.agent_receipt_count(&bob), 2);
    assert_eq!(
        clerk.agent_receipt_head_hash(&alice),
        Some(alice_2.receipt_hash())
    );
    assert_eq!(
        clerk.agent_receipt_head_hash(&bob),
        Some(bob_2.receipt_hash())
    );

    let alice_chain: Vec<_> = clerk.agent_receipts(&alice).cloned().collect();
    let bob_chain: Vec<_> = clerk.agent_receipts(&bob).cloned().collect();
    verify_receipt_chain(&alice_chain).expect("Alice's projected chain is valid");
    verify_receipt_chain(&bob_chain).expect("Bob's projected chain is valid");
    assert!(
        verify_receipt_chain(clerk.receipt_log()).is_err(),
        "an interleaved node log must not masquerade as one agent's chain"
    );

    // Boot recovery rebuilds the same independent causal indices from the
    // immutable total log.
    let log = clerk.receipt_log().to_vec();
    let mut restored = common::cclerk_from_label("restored-interleaved-node-log");
    assert_eq!(restored.restore_receipt_chain(log), 4);
    assert_eq!(
        restored.agent_receipt_head_hash(&alice),
        Some(alice_2.receipt_hash())
    );
    assert_eq!(
        restored.agent_receipt_head_hash(&bob),
        Some(bob_2.receipt_hash())
    );
    restored
        .verify_own_chain()
        .expect("all restored agent chains verify");
}

#[test]
fn missing_predecessor_is_rejected_after_that_agents_genesis() {
    let mut clerk = common::cclerk_from_label("missing-predecessor");
    let alice = clerk.cell_id("alice");
    let bob = clerk.cell_id("bob");

    let alice_1 = common::mock_receipt(alice, [0x10; 32], [0x11; 32]);
    clerk.append_receipt(alice_1).unwrap();
    let expected = clerk.agent_receipt_head_hash(&alice);

    // An unrelated agent's genesis remains valid; causality is scoped by
    // agent, not by whether the global node log is empty.
    clerk
        .append_receipt(common::mock_receipt(bob, [0x20; 32], [0x21; 32]))
        .unwrap();

    let unlinked_alice_2 = common::mock_receipt(alice, [0x11; 32], [0x12; 32]);
    let original_hash = unlinked_alice_2.receipt_hash();
    let error = clerk
        .append_receipt(unlinked_alice_2)
        .expect_err("None cannot reset a non-genesis agent chain");
    assert_eq!(
        error,
        ChainAppendError::ReceiptChainMismatch {
            expected,
            got: None,
        }
    );
    assert_eq!(clerk.receipt_log_length(), 2, "rejection is atomic");
    assert_eq!(clerk.agent_receipt_count(&alice), 1);
    assert_eq!(clerk.agent_receipt_head_hash(&alice), expected);
    assert_ne!(
        clerk.receipt_head().unwrap().receipt_hash(),
        original_hash,
        "the rejected receipt was not logged"
    );
}

#[test]
fn append_preserves_signed_bytes_hash_and_executor_signature() {
    let mut clerk = common::cclerk_from_label("signed-receipt-stability");
    let alice = clerk.cell_id("alice");
    let bob = clerk.cell_id("bob");
    let executor_seed = [0xA7; 32];
    let executor_pk = ed25519_dalek::SigningKey::from_bytes(&executor_seed)
        .verifying_key()
        .to_bytes();
    let durable = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let durable_sink = durable.clone();
    clerk.set_receipt_persist(std::sync::Arc::new(move |index, receipt| {
        durable_sink
            .lock()
            .unwrap()
            .push((index, postcard::to_allocvec(receipt).unwrap()));
    }));

    let alice_1 = signed(
        common::mock_receipt(alice, [0x10; 32], [0x11; 32]),
        &executor_seed,
    );
    let alice_1_wire = postcard::to_allocvec(&alice_1).unwrap();
    let alice_1_hash = alice_1.receipt_hash();
    let alice_1_signature = alice_1.executor_signature.clone();
    clerk.append_receipt(alice_1).unwrap();

    let stored_alice_1 = clerk.agent_receipt_head(&alice).unwrap();
    assert_eq!(postcard::to_allocvec(stored_alice_1).unwrap(), alice_1_wire);
    assert_eq!(stored_alice_1.receipt_hash(), alice_1_hash);
    assert_eq!(stored_alice_1.executor_signature, alice_1_signature);
    verify_receipt_signature_with_keys(stored_alice_1, &[executor_pk])
        .expect("append must preserve the executor's signature");
    assert_eq!(
        durable.lock().unwrap()[0],
        (0, alice_1_wire),
        "the durability sink receives the exact signed bytes"
    );

    // Interleave Bob before Alice's second receipt. Alice 2 still points to
    // Alice 1, not to the most recently observed global receipt.
    clerk
        .append_receipt(common::mock_receipt(bob, [0x20; 32], [0x21; 32]))
        .unwrap();
    let alice_2 = signed(
        common::mock_receipt_with_prev(alice, [0x11; 32], [0x12; 32], Some(alice_1_hash)),
        &executor_seed,
    );
    let alice_2_wire = postcard::to_allocvec(&alice_2).unwrap();
    let alice_2_hash = alice_2.receipt_hash();
    clerk.append_receipt(alice_2).unwrap();

    let stored_alice_2 = clerk.agent_receipt_head(&alice).unwrap();
    assert_eq!(postcard::to_allocvec(stored_alice_2).unwrap(), alice_2_wire);
    assert_eq!(stored_alice_2.receipt_hash(), alice_2_hash);
    assert_eq!(stored_alice_2.previous_receipt_hash, Some(alice_1_hash));
    verify_receipt_signature_with_keys(stored_alice_2, &[executor_pk])
        .expect("interleaved append must preserve the executor's signature");
    assert_eq!(
        durable.lock().unwrap()[2],
        (2, alice_2_wire),
        "the persisted global-log entry is byte-identical to the signed receipt"
    );
}
