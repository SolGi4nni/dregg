//! End-to-end exercise of the SDK `factories::mint_supply` affordance against a
//! real `TurnExecutor` (`docs/SUPPLY-MODEL.md`, the cap-gated supply entry).
//!
//! Proves the SDK builder is genuinely wired through to the executor's
//! `Effect::Mint` handler: a turn carrying `mint_supply(..)` COMMITS and leaves
//! a receipt when (and ONLY when) the agent holds a control-grade mint-cap over
//! the asset's issuer well; an uncapped agent's mint is REFUSED and the supply
//! well does not grow.

use dregg_cell::{AuthRequired, Cell, CellId, EFFECT_MINT, Ledger, Permissions};
use dregg_sdk::factories::mint_supply;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, TurnExecutor,
    turn::{Turn, TurnResult},
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

fn open_cell(seed: u8, token_id: [u8; 32], balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37).wrapping_add(1);
    let mut cell = Cell::with_balance(pk, token_id, balance);
    cell.permissions = open_permissions();
    cell
}

/// The deterministic per-asset well id (mirrors the executor's
/// `derive_issuer_well`).
fn derived_well_id(token_id: &[u8; 32]) -> CellId {
    let well_pubkey = blake3::derive_key("dregg-issuer-well-key-v1", token_id);
    CellId::derive_raw(&well_pubkey, token_id)
}

/// A single-action turn whose effects come from the SDK `mint_supply` builder.
fn mint_turn(actor: CellId, recipient: CellId, amount: u64) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: recipient,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: mint_supply(recipient, amount),
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent: actor,
        nonce: 0,
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

#[test]
fn sdk_mint_supply_capped_commits_and_grows_the_well() {
    let token_id = [21u8; 32];
    let well_id = derived_well_id(&token_id);

    let recipient = open_cell(1, token_id, 0);
    let recipient_id = recipient.id();

    // The issuer holds a control-grade EFFECT_MINT cap over the well (the
    // mint authority) plus an access cap over the recipient (the cross-cell
    // action gate).
    let mut issuer = open_cell(2, token_id, 0);
    issuer
        .capabilities
        .grant_faceted(well_id, AuthRequired::None, EFFECT_MINT)
        .expect("grant mint-cap");
    issuer
        .capabilities
        .grant(recipient_id, AuthRequired::None)
        .expect("grant recipient access");
    let issuer_id = issuer.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(recipient).unwrap();
    ledger.insert_cell(issuer).unwrap();

    let amount = 2_500u64;
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = mint_turn(issuer_id, recipient_id, amount);
    let result = executor.execute(&turn, &mut ledger);

    let TurnResult::Committed { receipt, .. } = &result else {
        panic!("SDK cap-gated mint must commit: {result:?}");
    };
    assert_eq!(receipt.turn_hash, turn.hash(), "receipt binds the mint turn");
    assert_ne!(
        receipt.pre_state_hash, receipt.post_state_hash,
        "the mint mutated state"
    );

    assert_eq!(
        ledger.get(&recipient_id).unwrap().state.balance(),
        amount as i64,
        "recipient credited the minted amount"
    );
    assert_eq!(
        ledger.get(&well_id).unwrap().state.balance(),
        -(amount as i64),
        "the supply well grew (more negative) under the cap",
    );
    // Standing invariant Σholders + well = 0.
    let supply_sum: i128 = ledger.iter().map(|(_, c)| c.state.balance() as i128).sum();
    assert_eq!(supply_sum, 0, "Σholders + well = 0");
}

#[test]
fn sdk_mint_supply_uncapped_is_refused_and_well_does_not_grow() {
    let token_id = [23u8; 32];
    let well_id = derived_well_id(&token_id);

    let recipient = open_cell(1, token_id, 0);
    let recipient_id = recipient.id();

    // No mint-cap — only ordinary access to the recipient.
    let mut actor = open_cell(2, token_id, 0);
    actor
        .capabilities
        .grant(recipient_id, AuthRequired::None)
        .expect("grant recipient access");
    let actor_id = actor.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(recipient).unwrap();
    ledger.insert_cell(actor).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&mint_turn(actor_id, recipient_id, 2_500), &mut ledger);
    assert!(
        !matches!(result, TurnResult::Committed { .. }),
        "SDK mint with no mint-cap must be REFUSED: {result:?}"
    );
    assert_eq!(
        ledger.get(&recipient_id).unwrap().state.balance(),
        0,
        "refused mint must not credit the recipient"
    );
    // The well either never materialized or stayed at 0 — supply did not grow.
    assert_eq!(
        ledger.get(&well_id).map(|c| c.state.balance()).unwrap_or(0),
        0,
        "the supply well must not grow without the mint-cap"
    );
}
