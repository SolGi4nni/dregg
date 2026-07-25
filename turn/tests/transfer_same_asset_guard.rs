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
