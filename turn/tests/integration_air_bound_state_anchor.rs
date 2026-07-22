//! Integration test: **the receipt's state anchor is the AIR-bound chip 8-felt
//! commitment, not the trusted-Rust BLAKE3 ledger root.**
//!
//! Assurance-perimeter #1/#2: what a receipt chains, an executor signs, and a
//! federation quorum certifies used to be `dregg_cell::Ledger::root()` — a
//! hand-written BLAKE3 Merkle tree with no AIR and no proof obligation. It is
//! now `dregg_turn::state_commit::consensus_state_commitment`, the chip
//! `wire_commit_8` chain the deployed rotated EffectVM trace publishes as its
//! wide `STATE_COMMIT` carrier.
//!
//! ⚑ What this does NOT establish (see `dregg_turn::state_commit`'s module docs):
//! the flagship `⟺` refinement theorems certify the **1-felt** `wireCommitR`,
//! not this 8-felt chain — the 8-felt anchor is chip-bound and soundness-
//! ADDITIVE, with `air_accepts ⟺ spec` at 8 felts awaiting the S2 flag-day and
//! an 8-felt re-derivation (itself gated on the vacuous-at-params
//! `Poseidon2WideCR` / `InjectiveFloorRegrounded`). And this is a **per-cell /
//! per-transition** commitment, not the whole-ledger snapshot `Ledger::root()`
//! was; the whole-ledger 8-felt state root is the deferred `cells_root` Phase-E.

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::{Turn, TurnReceipt, TurnResult},
};

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

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn single_effect_turn(agent: CellId, target: CellId, nonce: u64, effect: Effect) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![effect],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn unwrap_receipt(result: TurnResult) -> TurnReceipt {
    match result {
        TurnResult::Committed { receipt, .. } => receipt,
        other => panic!("expected Committed, got {other:?}"),
    }
}

/// THE test: a committed turn's `post_state_hash` IS the chip 8-felt anchor,
/// and is NOT the BLAKE3 `Ledger::root()`.
#[test]
fn committed_receipt_anchors_on_the_chip_8_felt_not_blake3() {
    let agent = make_open_cell(1, 1_000);
    let peer = make_open_cell(2, 0);
    let (agent_id, peer_id) = (agent.id(), peer.id());
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(peer).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());

    // The BLAKE3 root of the PRE-state, for the negative assertion below.
    let blake3_pre = ledger.root();
    let anchor_pre = executor.consensus_state_commitment(&ledger, &agent_id);
    assert_ne!(
        anchor_pre, blake3_pre,
        "the pre-state anchor must not be the trusted-Rust BLAKE3 ledger root"
    );

    let turn = single_effect_turn(
        agent_id,
        agent_id,
        0,
        Effect::Transfer {
            from: agent_id,
            to: peer_id,
            amount: 250,
        },
    );
    let receipt = unwrap_receipt(executor.execute(&turn, &mut ledger));

    // The receipt's pre-state is the anchor we computed before executing.
    assert_eq!(
        receipt.pre_state_hash, anchor_pre,
        "the receipt's pre_state_hash must be the AIR-bound anchor"
    );

    // The post-state is the anchor of the POST ledger — and is not BLAKE3.
    let anchor_post = executor.consensus_state_commitment(&ledger, &agent_id);
    assert_eq!(
        receipt.post_state_hash, anchor_post,
        "the receipt's post_state_hash must be the AIR-bound anchor"
    );
    assert_ne!(
        receipt.post_state_hash,
        ledger.root(),
        "the receipt's post_state_hash must NOT be the BLAKE3 ledger root"
    );

    // The anchor fills the WHOLE 32-byte slot (8 felts × 4 LE bytes), unlike the
    // 1-felt encoding that leaves 28 bytes zero — the anti-waist tooth.
    assert!(
        receipt.post_state_hash[8..].iter().any(|b| *b != 0),
        "the 8-felt anchor must fill the whole slot, not just the low felt"
    );

    // And it MOVED: a transfer changed the agent's balance.
    assert_ne!(
        receipt.pre_state_hash, receipt.post_state_hash,
        "a balance-changing turn must move the anchor"
    );
}

/// Chain continuity still verifies: `pre` and `post` come from the SAME
/// function, so `verify_receipt_chain`'s `curr.pre == prev.post` check holds
/// across consecutive turns by the same agent.
#[test]
fn receipt_chain_continuity_holds_under_the_anchor() {
    let agent = make_open_cell(3, 1_000);
    let peer = make_open_cell(7, 0);
    let (agent_id, peer_id) = (agent.id(), peer.id());
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(peer).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());

    let mut receipts: Vec<TurnReceipt> = Vec::new();
    for nonce in 0..3u64 {
        let mut turn = single_effect_turn(
            agent_id,
            agent_id,
            nonce,
            Effect::Transfer {
                from: agent_id,
                to: peer_id,
                amount: 10,
            },
        );
        // Thread the chain link on the TURN — the executor gates on it and
        // stamps the receipt's `previous_receipt_hash` from it.
        turn.previous_receipt_hash = receipts.last().map(|r: &TurnReceipt| r.receipt_hash());
        let receipt = unwrap_receipt(executor.execute(&turn, &mut ledger));
        receipts.push(receipt);
    }

    // Adjacent receipts must be state-continuous.
    for pair in receipts.windows(2) {
        assert_eq!(
            pair[1].pre_state_hash, pair[0].post_state_hash,
            "chain continuity: each turn's pre-anchor must be the previous post-anchor"
        );
    }

    dregg_turn::verify::verify_receipt_chain(&receipts)
        .expect("the receipt chain must verify under the AIR-bound anchor");
}

/// A tampered post-state anchor is caught by executor authentication, not by
/// treating per-agent snapshots as a globally contiguous state log.
#[test]
fn tampered_post_anchor_breaks_strict_authenticated_verification() {
    let agent = make_open_cell(4, 1_000);
    let peer = make_open_cell(8, 0);
    let (agent_id, peer_id) = (agent.id(), peer.id());
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(peer).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());

    let mut receipts: Vec<TurnReceipt> = Vec::new();
    for nonce in 0..2u64 {
        let mut turn = single_effect_turn(
            agent_id,
            agent_id,
            nonce,
            Effect::Transfer {
                from: agent_id,
                to: peer_id,
                amount: 10,
            },
        );
        // Thread the chain link on the TURN — the executor gates on it and
        // stamps the receipt's `previous_receipt_hash` from it.
        turn.previous_receipt_hash = receipts.last().map(|r: &TurnReceipt| r.receipt_hash());
        let receipt = unwrap_receipt(executor.execute(&turn, &mut ledger));
        receipts.push(receipt);
    }
    let signing_seed = [0x42u8; 32];
    for receipt in &mut receipts {
        receipt.executor_signature = Some(dregg_turn::sign_receipt(receipt, &signing_seed));
    }
    let executor_pk = ed25519_dalek::SigningKey::from_bytes(&signing_seed)
        .verifying_key()
        .to_bytes();
    dregg_turn::verify::verify_receipt_chain_strict(&receipts, &[executor_pk])
        .expect("baseline signed chain must verify");

    // Flip one byte of the first receipt's post anchor.
    let mut tampered = receipts.clone();
    tampered[0].post_state_hash[3] ^= 0x01;
    // Re-link after tampering so structural hash causality remains valid.
    tampered[1].previous_receipt_hash = Some(tampered[0].receipt_hash());

    dregg_turn::verify::verify_receipt_chain(&tampered).expect(
        "the structural verifier checks per-agent hash causality, not global-state adjacency",
    );
    assert!(
        matches!(
            dregg_turn::verify::verify_receipt_chain_strict(&tampered, &[executor_pk]),
            Err(dregg_turn::VerifyError::ExecutorSignatureInvalid { index: 0 })
        ),
        "executor authentication must reject the tampered state snapshot at receipt 0"
    );
}

/// The anchor moves when the agent's state moves — a turn that changes nothing
/// observable about the agent still advances the nonce, and the anchor tracks it.
#[test]
fn anchor_tracks_agent_state_not_unrelated_cells() {
    let agent = make_open_cell(5, 500);
    let bystander = make_open_cell(6, 500);
    let (agent_id, bystander_id) = (agent.id(), bystander.id());
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(bystander).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let before = executor.consensus_state_commitment(&ledger, &agent_id);

    // A turn by the BYSTANDER that does not touch the agent's cell.
    let turn = single_effect_turn(
        bystander_id,
        bystander_id,
        0,
        Effect::IncrementNonce { cell: bystander_id },
    );
    let _ = unwrap_receipt(executor.execute(&turn, &mut ledger));

    let after = executor.consensus_state_commitment(&ledger, &agent_id);

    // The BLAKE3 whole-ledger root necessarily moved (a different cell changed).
    // The per-cell anchor does NOT — this is exactly residual (ii): the anchor is
    // a per-cell/per-transition commitment, not a whole-ledger snapshot. It binds
    // the rest of the ledger only through `cells_root` (an existence fold over the
    // SET of present cells), which a nonce bump does not move.
    assert_eq!(
        before, after,
        "the per-cell anchor does not move for an unrelated cell's state change \
         — the whole-ledger 8-felt state root is the deferred `cells_root` Phase-E"
    );
}
