//! SUPPLY-MODEL Stage 2a mint tests (`docs/SUPPLY-MODEL.md`).
//!
//! `Effect::Mint` is the cap-gated SUPPLY ENTRY — the sign-flipped dual of
//! `Burn`. The asset's ISSUER WELL (resolved from the recipient's `token_id`)
//! is DEBITED negative-capably (going more negative as supply enters) and the
//! recipient is CREDITED, so a mint CONSERVES exactly (per-turn, per-asset
//! Σδ=0). The one place mint ≠ burn is the AUTHORITY GATE: minting requires a
//! CONTROL-GRADE capability over the well carrying the `EFFECT_MINT` facet (the
//! Rust image of Lean `mintAuthorizedB` — issuer authority, NOT bare ownership;
//! "a cell cannot coin its own supply").
//!
//! These tests assert:
//!  - an AUTHORIZED mint (mint-cap held) CONSERVES (well -= amt, holder += amt,
//!    Σδ=0) and RESTORES the standing invariant `Σholders + well = 0` for a
//!    freshly-minted asset (the well starts at 0, goes to −amt = −supply);
//!  - an UNAUTHORIZED mint (no mint-cap, or a non-`EFFECT_MINT` cap) is
//!    REJECTED;
//!  - a SELF-MINT (actor == recipient, or actor == well) is REJECTED.

use dregg_cell::{AuthRequired, Cell, CellId, EFFECT_MINT, EFFECT_TRANSFER, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
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

/// An open hosted cell with a chosen `token_id` (asset class) and balance.
fn open_cell(seed: u8, token_id: [u8; 32], balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37).wrapping_add(1);
    let mut cell = Cell::with_balance(pk, token_id, balance);
    cell.permissions = open_permissions();
    cell
}

/// The deterministic per-asset well id — mirrors `derive_issuer_well`.
fn derived_well_id(token_id: &[u8; 32]) -> CellId {
    let well_pubkey = blake3::derive_key("dregg-issuer-well-key-v1", token_id);
    CellId::derive_raw(&well_pubkey, token_id)
}

/// A single-action turn where `actor` mints `amount` of `target`'s asset into
/// `target`.
fn mint_turn(actor: CellId, target: CellId, amount: u64) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Mint {
            target,
            slot: 0,
            amount,
        }],
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

fn balances(ledger: &Ledger) -> std::collections::HashMap<CellId, i64> {
    ledger
        .iter()
        .map(|(id, c)| (*id, c.state.balance()))
        .collect()
}

fn total_delta(
    before: &std::collections::HashMap<CellId, i64>,
    after: &std::collections::HashMap<CellId, i64>,
) -> i128 {
    let mut keys: std::collections::HashSet<&CellId> = before.keys().collect();
    keys.extend(after.keys());
    keys.into_iter()
        .map(|k| {
            let b = before.get(k).copied().unwrap_or(0) as i128;
            let a = after.get(k).copied().unwrap_or(0) as i128;
            a - b
        })
        .sum()
}

/// The standing invariant `Σholders + well = 0` for a mint-authored asset.
/// Every cell in the ledger here is in the single asset class, and the well
/// carries −supply, so the whole-ledger balance sum is exactly 0.
fn supply_sum(ledger: &Ledger) -> i128 {
    ledger
        .iter()
        .map(|(_, c)| c.state.balance() as i128)
        .sum::<i128>()
}

#[test]
fn authorized_mint_conserves_and_restores_supply_invariant() {
    // The recipient (a fresh, empty holder) and the mint authority (issuer).
    let token_id = [7u8; 32];
    let well_id = derived_well_id(&token_id);

    // The recipient holds zero balance to start (a freshly-minted asset).
    let recipient = open_cell(1, token_id, 0);
    let recipient_id = recipient.id();

    // The issuer/actor: a distinct cell that HOLDS a control-grade mint-cap over
    // the well (EFFECT_MINT facet, AuthRequired::None = full control cap). It
    // also holds an ordinary cap over the recipient so the action-level
    // cross-cell authority gate (actor must hold a cap over `action.target`)
    // passes — minting INTO another cell is a cross-cell act.
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

    let amount = 1_000u64;
    let before = balances(&ledger);
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = mint_turn(issuer_id, recipient_id, amount);
    let result = executor.execute(&turn, &mut ledger);

    // The cap-gated mint COMMITS a real verified turn and LEAVES A RECEIPT
    // (the end-to-end wiring: dispatch → `apply_mint` → conserving move →
    // committed receipt). Bind the receipt to this turn and to a genuine
    // state transition.
    let TurnResult::Committed { receipt, .. } = &result else {
        panic!("authorized mint must commit: {result:?}");
    };
    assert_eq!(
        receipt.agent, issuer_id,
        "receipt records the minting issuer as the turn agent"
    );
    assert_eq!(
        receipt.turn_hash,
        turn.hash(),
        "receipt binds the executed mint turn by hash"
    );
    assert_ne!(
        receipt.pre_state_hash, receipt.post_state_hash,
        "the mint mutated state (well debit + holder credit), so the receipt's \
         post-state hash must differ from its pre-state hash"
    );
    let after = balances(&ledger);

    // PER-TURN CONSERVATION: every balance delta nets to zero.
    assert_eq!(
        total_delta(&before, &after),
        0,
        "per-turn Σδ must be zero (well debit == holder credit)"
    );

    // The recipient was credited exactly `amount`.
    assert_eq!(
        ledger.get(&recipient_id).unwrap().state.balance(),
        amount as i64,
        "recipient credited the minted amount"
    );

    // The well exists and carries −amount (it started at 0, debited negative).
    let well = ledger
        .get(&well_id)
        .expect("well must be lazily created and carry −supply");
    assert_eq!(
        well.state.balance(),
        -(amount as i64),
        "well debited to −supply (negative-capable leg)"
    );
    assert_eq!(
        well.token_id(),
        &token_id,
        "well must share the recipient's asset class"
    );

    // STANDING INVARIANT: Σ(all balances) = 0 for the mint-authored asset
    // (holders + well = 0; the issuer holds 0, recipient +amount, well −amount).
    assert_eq!(
        supply_sum(&ledger),
        0,
        "Σholders + well = 0 for a freshly-minted asset"
    );
}

#[test]
fn unauthorized_mint_no_cap_is_rejected() {
    let token_id = [9u8; 32];

    let recipient = open_cell(1, token_id, 0);
    let recipient_id = recipient.id();

    // The actor holds NO mint-cap over the well — only an ordinary access cap
    // over the recipient (so the action-level gate passes and the rejection
    // comes precisely from the MINT authority gate).
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
    let result = executor.execute(&mint_turn(actor_id, recipient_id, 500), &mut ledger);
    assert!(
        !matches!(result, TurnResult::Committed { .. }),
        "mint with no mint-cap must be REJECTED: {result:?}"
    );
    // The recipient balance is untouched.
    assert_eq!(
        ledger.get(&recipient_id).unwrap().state.balance(),
        0,
        "rejected mint must not credit the recipient"
    );
}

#[test]
fn unauthorized_mint_wrong_facet_is_rejected() {
    let token_id = [11u8; 32];
    let well_id = derived_well_id(&token_id);

    let recipient = open_cell(1, token_id, 0);
    let recipient_id = recipient.id();

    // The actor holds a control-grade cap over the well, but it carries only the
    // EFFECT_TRANSFER facet — NOT EFFECT_MINT. A non-mint cap does not authorize
    // minting (the facet is load-bearing).
    let mut actor = open_cell(2, token_id, 0);
    actor
        .capabilities
        .grant_faceted(well_id, AuthRequired::None, EFFECT_TRANSFER)
        .expect("grant transfer-cap");
    actor
        .capabilities
        .grant(recipient_id, AuthRequired::None)
        .expect("grant recipient access");
    let actor_id = actor.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(recipient).unwrap();
    ledger.insert_cell(actor).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&mint_turn(actor_id, recipient_id, 500), &mut ledger);
    assert!(
        !matches!(result, TurnResult::Committed { .. }),
        "mint with a non-EFFECT_MINT cap must be REJECTED: {result:?}"
    );
    assert_eq!(
        ledger.get(&recipient_id).unwrap().state.balance(),
        0,
        "rejected mint must not credit the recipient"
    );
}

#[test]
fn self_mint_is_rejected() {
    // A cell cannot coin its own supply: actor == recipient is rejected even if
    // the actor somehow holds a mint-cap over its own asset's well.
    let token_id = [13u8; 32];
    let well_id = derived_well_id(&token_id);

    let mut actor = open_cell(1, token_id, 0);
    actor
        .capabilities
        .grant_faceted(well_id, AuthRequired::None, EFFECT_MINT)
        .expect("grant mint-cap");
    let actor_id = actor.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    // actor mints INTO itself.
    let result = executor.execute(&mint_turn(actor_id, actor_id, 500), &mut ledger);
    assert!(
        !matches!(result, TurnResult::Committed { .. }),
        "self-mint (actor == recipient) must be REJECTED: {result:?}"
    );
    assert_eq!(
        ledger.get(&actor_id).unwrap().state.balance(),
        0,
        "rejected self-mint must not credit"
    );
}
