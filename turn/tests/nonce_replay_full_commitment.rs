//! Adversarial test: full-commitment (`CommitmentMode::Full`) signing-message
//! replay seam.
//!
//! `TurnExecutor::compute_signing_message` (the Full-commitment preimage) binds
//! federation_id, target, method, args, effects, may_delegate, commitment_mode,
//! balance_change, and preconditions — but historically NOT the turn nonce or
//! the receipt-chain position. Every OTHER authorization path (Partial, Stealth,
//! Custom, Hybrid) binds `turn_nonce` into the signed message.
//!
//! The two commit-path replay gates — the nonce gate
//! (`agent.state.nonce() == turn.nonce`, executor/execute.rs) and the
//! receipt-chain gate (`turn.previous_receipt_hash == stored head`,
//! executor/mod.rs `check_previous_receipt_hash`) — are BOTH satisfiable by an
//! adversary who only observes PUBLIC values (the current on-ledger nonce and
//! the public receipt-chain head). Neither `turn.nonce` nor
//! `turn.previous_receipt_hash` is covered by the action-level signature, and
//! the executor verifies no turn-level signature. So a captured Full-commitment
//! signed action can be lifted onto an advanced (nonce, receipt-head) pair and
//! re-committed — a value-draining replay.
//!
//! This test captures a Full-commitment signed Transfer, commits it once, then
//! (as an attacker who never held the signer's key) mutates ONLY the two
//! unsigned turn fields to their current public values and resubmits. The
//! post-fix invariant is that the replay is REJECTED and the victim cell's
//! balance is debited exactly once.

use std::collections::HashMap;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, symbol};
use dregg_turn::{CallForest, ComputronCosts, Effect, Turn, TurnExecutor, TurnResult};
use ed25519_dalek::{Signer, SigningKey, VerifyingKey};

/// Deterministic Ed25519 keypair from a one-byte seed; the cell's public key is
/// the verifying key so signatures verify against the cell identity.
fn keypair(seed: u8) -> (SigningKey, [u8; 32]) {
    let sk = SigningKey::from_bytes(&[seed; 32]);
    let vk: VerifyingKey = (&sk).into();
    (sk, vk.to_bytes())
}

fn sig_cell(seed: u8, balance: i64) -> (Cell, SigningKey) {
    let (sk, pk) = keypair(seed);
    // Default permissions require a Signature for `send` (the Transfer path).
    let cell = Cell::with_balance(pk, [0u8; 32], balance);
    (cell, sk)
}

/// A wide-open recipient cell (no auth required) so it can receive the transfer
/// and act as the turn's submitting agent without needing its own signature.
fn open_cell(seed: u8, balance: i64) -> Cell {
    let (_, pk) = keypair(seed);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell
}

fn build_turn(
    agent: dregg_cell::CellId,
    nonce: u64,
    action: Action,
    prev: Option<[u8; 32]>,
) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: prev,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// Capture a Full-commitment signed Transfer, commit it once, then replay it
/// against the advanced (nonce, receipt-head) pair without the signer's key.
#[test]
fn full_commitment_signature_is_not_nonce_replayable() {
    // Victim signs the transfer out of its own balance; recipient is the turn
    // agent (open perms) and the transfer destination.
    let (victim, victim_sk) = sig_cell(1, 10_000);
    let victim_id = victim.id();
    let mut recipient = open_cell(2, 0);
    let recipient_id = recipient.id();

    // The submitting agent must hold a capability to the victim (the action
    // target) to route the call.
    recipient.capabilities.grant(victim_id, AuthRequired::None);

    let mut ledger = Ledger::new();
    ledger.insert_cell(victim).unwrap();
    ledger.insert_cell(recipient).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());

    // The signed action: Transfer 1000 out of the victim, authorized by the
    // victim's Full-commitment signature.
    let effects = vec![Effect::Transfer {
        from: victim_id,
        to: recipient_id,
        amount: 1_000,
    }];
    let unsigned = Action {
        target: victim_id,
        method: symbol("transfer"),
        args: vec![],
        authorization: Authorization::Unchecked, // placeholder for message computation
        preconditions: Default::default(),
        effects: effects.clone(),
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    // Full-commitment signing message (federation id = executor default zeros).
    // The signer commits to the nonce the legitimate turn will submit under
    // (the agent's nonce 0 for `turn1`). After the fix binds `turn_nonce`, a
    // replay onto an advanced nonce recomputes a DIFFERENT message, so the
    // captured signature no longer verifies.
    let message = TurnExecutor::compute_signing_message(&unsigned, &[0u8; 32], 0);
    let sig = victim_sk.sign(&message).to_bytes();
    let signed_action = Action {
        authorization: Authorization::from_sig_bytes(sig),
        ..unsigned
    };

    // ---- Turn 1: the legitimate commit at the victim-agent's nonce 0. ----
    let turn1 = build_turn(recipient_id, 0, signed_action.clone(), None);
    let r1 = executor.execute(&turn1, &mut ledger);
    assert!(
        r1.is_committed(),
        "honest signed transfer must commit first (setup sanity): {r1:?}",
    );
    assert_eq!(
        ledger.get(&victim_id).unwrap().state.balance(),
        9_000,
        "victim debited exactly once after the legitimate turn",
    );

    // The attacker observes two PUBLIC values: the agent's current on-ledger
    // nonce and the receipt-chain head. Neither requires the signer's key.
    let public_nonce = ledger.get(&recipient_id).unwrap().state.nonce();
    let public_head = executor
        .get_last_receipt_hash(&recipient_id)
        .expect("agent has a committed receipt head after turn 1");

    // ---- Replay: identical signed action, only the two UNSIGNED turn fields
    // (nonce + previous_receipt_hash) advanced to current public values. ----
    let replay = build_turn(recipient_id, public_nonce, signed_action, Some(public_head));
    let r2 = executor.execute(&replay, &mut ledger);

    assert!(
        matches!(r2, TurnResult::Rejected { .. }),
        "a captured full-commitment signature must NOT be replayable onto an \
         advanced nonce/receipt-head; got {r2:?}",
    );
    assert_eq!(
        ledger.get(&victim_id).unwrap().state.balance(),
        9_000,
        "replay must not debit the victim a second time",
    );
}
