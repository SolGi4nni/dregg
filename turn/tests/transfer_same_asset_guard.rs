//! FALSIFIER (#1, cross-asset teleport / inflation): `Effect::Transfer` moves a
//! SINGLE asset column, welded to the verified kernel `recTransferBal`
//! (`Dregg2.Exec.RecordKernel.lean:641`), which debits `src` and credits `dst`
//! in ONE `AssetId`. A cell's committed `token_id` IS its asset identity.
//!
//! Before the guard, `apply_transfer` did `from.bal -= amt; to.bal += amt`
//! across cells of DIFFERENT `token_id` with NO check, and the apply-time
//! Transfer path never feeds the per-asset `asset_deltas` accumulator (only an
//! action's `balance_change` does), so the turn-end `Σδ=0` gate could not see a
//! cross-asset teleport: a `Transfer { from: cheap-asset-X, to: valuable-asset-Y }`
//! inflated `Σbal[Y]` out of worthless X.
//!
//! Both directions of the falsifier:
//!   * a CROSS-asset Transfer (from token X, to token Y, X ≠ Y) is REJECTED;
//!   * a SAME-asset Transfer succeeds and CONSERVES the per-asset total.

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnError,
    TurnExecutor,
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

/// A live, fully-open cell with an explicit `token_id` (asset class) and balance.
fn make_cell(seed: u8, token_id: [u8; 32], balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, token_id, balance);
    cell.permissions = open_permissions();
    cell
}

fn transfer_turn(agent: CellId, from: CellId, to: CellId, amount: u64, nonce: u64) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer { from, to, amount }],
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

const ASSET_X: [u8; 32] = [0x11u8; 32];
const ASSET_Y: [u8; 32] = [0x22u8; 32];

/// Direction 1: a CROSS-asset Transfer (source asset X, dest asset Y, X ≠ Y) is
/// REJECTED with a distinct `InvalidEffect` reason. This is the inflation hole:
/// without the guard, `Σbal[Y]` would grow out of worthless X while the scalar
/// excess (and the per-asset gate, which Transfer never feeds) stayed put.
#[test]
fn cross_asset_transfer_is_rejected() {
    let agent = make_cell(1, ASSET_X, 1_000); // holds asset X
    let peer = make_cell(2, ASSET_Y, 0); // holds asset Y ≠ X
    let (agent_id, peer_id) = (agent.id(), peer.id());
    assert_ne!(
        agent.token_id(),
        peer.token_id(),
        "fixture invariant: the two cells must hold DIFFERENT assets"
    );

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(peer).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = transfer_turn(agent_id, agent_id, peer_id, 250, 0);

    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => match reason {
            TurnError::InvalidEffect { reason } => assert!(
                reason.contains("cross-asset"),
                "cross-asset Transfer must be refused with a distinct cross-asset reason, got: {reason}"
            ),
            other => panic!("expected InvalidEffect (cross-asset), got {other:?}"),
        },
        other => panic!("cross-asset Transfer must be REJECTED, got {other:?}"),
    }

    // And crucially: NO value was minted into asset Y. `peer` still holds 0.
    assert_eq!(
        ledger.get(&peer_id).unwrap().state.balance(),
        0,
        "a rejected cross-asset Transfer must not inflate the destination asset"
    );
    assert_eq!(
        ledger.get(&agent_id).unwrap().state.balance(),
        1_000,
        "a rejected cross-asset Transfer must leave the source untouched (rolled back)"
    );
}

/// Direction 2: a SAME-asset Transfer succeeds and CONSERVES the asset's total —
/// the debit and credit cancel exactly (kernel `recTransferBal_sum_conserve_moved`).
#[test]
fn same_asset_transfer_succeeds_and_conserves() {
    let agent = make_cell(3, ASSET_X, 1_000);
    let peer = make_cell(4, ASSET_X, 0); // SAME asset X
    let (agent_id, peer_id) = (agent.id(), peer.id());
    assert_eq!(
        agent.token_id(),
        peer.token_id(),
        "fixture invariant: the two cells must hold the SAME asset"
    );

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(peer).unwrap();

    let total_before = ledger.get(&agent_id).unwrap().state.balance()
        + ledger.get(&peer_id).unwrap().state.balance();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = transfer_turn(agent_id, agent_id, peer_id, 250, 0);

    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed { .. } => {}
        other => panic!("same-asset Transfer must be COMMITTED, got {other:?}"),
    }

    let agent_after = ledger.get(&agent_id).unwrap().state.balance();
    let peer_after = ledger.get(&peer_id).unwrap().state.balance();
    assert_eq!(agent_after, 750, "source debited by the transfer amount");
    assert_eq!(
        peer_after, 250,
        "destination credited by the transfer amount"
    );
    assert_eq!(
        agent_after + peer_after,
        total_before,
        "a same-asset Transfer CONSERVES the asset total (debit and credit cancel)"
    );
}

// =============================================================================
// The NAME-SALT / ASSET split (`dregg_cell::Cell::asset`)
// =============================================================================
//
// `Cell.token_id` used to be read as BOTH the `derive_raw` name salt and the
// cell's asset class. Splitting them is what made a factory-born cell fundable
// (it is born in its creator's currency, with the deal tag as its salt), and it
// opens exactly one new question the two tests above cannot answer: the guard
// used to get "same salt ⇒ same asset" FOR FREE. It no longer does. So the
// falsifier is re-run against the split shape.

/// A live, fully-open cell whose NAME SALT and ASSET differ — the shape that
/// did not exist before the split.
fn make_split_cell(seed: u8, name_salt: [u8; 32], asset: [u8; 32], balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, name_salt, balance).in_asset(CellId::from_bytes(asset));
    cell.permissions = open_permissions();
    cell
}

fn effects_turn(agent: CellId, effects: Vec<Effect>, nonce: u64) -> Turn {
    effects_turn_after(agent, effects, nonce, None)
}

/// As [`effects_turn`], but chained onto the agent's previous receipt (the
/// executor's per-agent receipt chain refuses a second turn that claims none).
fn effects_turn_after(
    agent: CellId,
    effects: Vec<Effect>,
    nonce: u64,
    previous_receipt_hash: Option<[u8; 32]>,
) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
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
        previous_receipt_hash,
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

/// THE REGRESSION THAT MATTERS MOST. A COLLIDING NAME SALT DOES NOT LAUNDER A
/// CROSS-ASSET MOVE.
///
/// Both cells carry the IDENTICAL `token_id` (`ASSET_X` used purely as a name),
/// so a guard still reading the salt would wave this through — and it is a real
/// teleport: the source's 1000 units are denominated in X, the destination's
/// balance in Y, so a credit here inflates `Σbal[Y]` out of X exactly as the
/// pre-guard hole did. The guard reads `asset()`, so it is refused.
#[test]
fn a_colliding_name_salt_does_not_launder_a_cross_asset_transfer() {
    // Same salt, different currency.
    let agent = make_split_cell(5, ASSET_X, ASSET_X, 1_000);
    let peer = make_split_cell(6, ASSET_X, ASSET_Y, 0);
    let (agent_id, peer_id) = (agent.id(), peer.id());
    assert_eq!(
        agent.token_id(),
        peer.token_id(),
        "fixture invariant: the two cells share a name salt (the laundering attempt)"
    );
    assert_ne!(
        agent.asset(),
        peer.asset(),
        "fixture invariant: but they hold DIFFERENT currencies"
    );

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(peer).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = transfer_turn(agent_id, agent_id, peer_id, 250, 0);

    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => match reason {
            TurnError::InvalidEffect { reason } => assert!(
                reason.contains("cross-asset"),
                "a salt collision must NOT launder a cross-asset move, got: {reason}"
            ),
            other => panic!("expected InvalidEffect (cross-asset), got {other:?}"),
        },
        other => panic!(
            "cross-asset Transfer must be REJECTED even under a salt collision, got {other:?}"
        ),
    }
    assert_eq!(
        ledger.get(&peer_id).unwrap().state.balance(),
        0,
        "no value may be minted into asset Y"
    );
    assert_eq!(
        ledger.get(&agent_id).unwrap().state.balance(),
        1_000,
        "the source is untouched (rolled back)"
    );
}

/// The FIX, end to end: a cell created by an effect under a NAME tag is born in
/// its CREATOR's currency, and the create-then-fund pattern therefore commits.
///
/// `NAME_TAG` is the only free axis an app has for "one cell per (owner, deal)"
/// — it goes in the salt. It must NOT become a private currency; that is what
/// made every factory-born cell unfundable.
#[test]
fn a_created_cell_is_born_in_its_creators_asset_and_can_be_funded() {
    const NAME_TAG: [u8; 32] = [0x77u8; 32];
    let creator = make_cell(7, ASSET_X, 10_000);
    let creator_id = creator.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(creator).unwrap();

    let child_pk = [0x5Au8; 32];
    let child_id = CellId::derive_raw(&child_pk, &NAME_TAG);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let create_receipt = match executor.execute(
        &effects_turn(
            creator_id,
            vec![Effect::CreateCell {
                public_key: child_pk,
                token_id: NAME_TAG,
                balance: 0,
            }],
            0,
        ),
        &mut ledger,
    ) {
        TurnResult::Committed { receipt, .. } => receipt.receipt_hash(),
        other => panic!("the create turn must COMMIT, got {other:?}"),
    };

    let born = ledger.get(&child_id).expect("the child cell exists");
    assert_eq!(
        born.token_id(),
        &NAME_TAG,
        "the name axis still works: the payload tag IS the child's salt"
    );
    assert_eq!(
        born.asset(),
        CellId::from_bytes(ASSET_X),
        "but the child is denominated in its CREATOR's currency, not in its own name"
    );

    // Now fund it — the move the whole create-then-fund pattern depends on.
    match executor.execute(
        &effects_turn_after(
            creator_id,
            vec![Effect::Transfer {
                from: creator_id,
                to: child_id,
                amount: 2_500,
            }],
            1,
            Some(create_receipt),
        ),
        &mut ledger,
    ) {
        TurnResult::Committed { .. } => {}
        other => panic!("funding a freshly created cell must COMMIT, got {other:?}"),
    }
    assert_eq!(
        ledger.get(&child_id).unwrap().state.balance(),
        2_500,
        "the created cell holds the funded value"
    );
    assert_eq!(
        ledger.get(&creator_id).unwrap().state.balance(),
        7_500,
        "the funder was debited the same amount (same-asset move conserves)"
    );
}

/// AND THE GUARD DID NOT GET CHEAPER: an effect payload cannot conjure a
/// currency. A creator holding asset X cannot birth a cell into asset Y by
/// naming Y in the payload — the child is in X, so a Y-holder funding it is
/// still refused. Inheritance NARROWS what a turn can mint (before the split,
/// the payload chose the new cell's asset outright).
#[test]
fn an_effect_payload_cannot_birth_a_cell_into_a_foreign_asset() {
    let creator = make_cell(8, ASSET_X, 10_000);
    let y_holder = make_cell(9, ASSET_Y, 10_000);
    let (creator_id, y_holder_id) = (creator.id(), y_holder.id());

    let mut ledger = Ledger::new();
    ledger.insert_cell(creator).unwrap();
    ledger.insert_cell(y_holder).unwrap();

    // The payload NAMES asset Y. The creator holds only X.
    let child_pk = [0x6Bu8; 32];
    let child_id = CellId::derive_raw(&child_pk, &ASSET_Y);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(
        &effects_turn(
            creator_id,
            vec![Effect::CreateCell {
                public_key: child_pk,
                token_id: ASSET_Y,
                balance: 0,
            }],
            0,
        ),
        &mut ledger,
    ) {
        TurnResult::Committed { .. } => {}
        other => panic!("the create turn must COMMIT, got {other:?}"),
    }
    assert_eq!(
        ledger.get(&child_id).unwrap().asset(),
        CellId::from_bytes(ASSET_X),
        "naming Y in the payload does NOT denominate the child in Y"
    );

    // So the Y holder cannot pay into it.
    match executor.execute(
        &effects_turn(
            y_holder_id,
            vec![Effect::Transfer {
                from: y_holder_id,
                to: child_id,
                amount: 100,
            }],
            0,
        ),
        &mut ledger,
    ) {
        TurnResult::Rejected {
            reason: TurnError::InvalidEffect { reason },
            ..
        } => assert!(
            reason.contains("cross-asset"),
            "a Y-funded X cell is a cross-asset move and must be refused, got: {reason}"
        ),
        other => panic!("expected a cross-asset refusal, got {other:?}"),
    }
    assert_eq!(
        ledger.get(&child_id).unwrap().state.balance(),
        0,
        "no value crossed the asset boundary"
    );
}
