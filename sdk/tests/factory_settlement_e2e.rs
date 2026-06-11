//! End-to-end teeth for the dregg3 settlement factories (escrow / obligation
//! / bridge-cell) on the REAL executor.
//!
//! These tests drive `AgentRuntime` (the embedded `TurnExecutor`) with turns
//! built by `dregg_sdk::factories` — surviving verbs ONLY
//! (`CreateCellFromFactory` / `SetField` / `Transfer` / the one-time
//! `GrantCapability` adopt self-grant). Every safety property is enforced by
//! the cell program the factory installs (the executor's per-touched-cell
//! program gate in `turn/src/executor/execute_tree.rs`), NOT by SDK-side
//! checks: the negative tests hand the executor a well-signed, well-formed
//! turn and assert the EXECUTOR rejects it with
//! `TurnError::ProgramViolation`.
//!
//! The Lean spec being mirrored (see `cell/src/blueprint.rs` for the exact
//! constraint set): `Dregg2.Apps.EscrowFactory`,
//! `Dregg2.Apps.ObligationFactory`, `Dregg2.Apps.BridgeCell`.

use dregg_cell::blueprint::{
    BridgeTerms, EscrowTerms, ObligationTerms, PARTY_B_SLOT, STATE_OPEN, STATE_RESOLVED_A,
    STATE_RESOLVED_B, STATE_SLOT,
};
use dregg_cell::{Cell, CellId, field_from_u64};
use dregg_sdk::factories::{
    ADOPT_TURN_FEE, SettlementCellPlan, bridge_lock_cell, cancel_bridge, create_escrow_cell,
    create_obligation_cell, finalize_bridge, fulfill_obligation, party_field, refund_escrow,
    release_escrow, slash_obligation,
};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, Effect, SdkError};
use dregg_turn::TurnError;

// =============================================================================
// Harness
// =============================================================================

/// A runtime + its agent's cell id + two zero-balance party cells.
///
/// The settlement cell is owned by the AGENT's key (the runtime signs every
/// turn with it) and the agent is the operator + funder; the deal parties
/// (`party_a` = depositor/obligor/originator, `party_b` =
/// beneficiary/obligee/pot) are separate zero-balance cells so payout
/// assertions are exact (no turn-fee noise). The CELL PROGRAM is the
/// deciding gate — exactly the property under test.
fn harness(domain: &str) -> (AgentRuntime, CellId, CellId, CellId) {
    let runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), domain);
    let agent = runtime.cell_id();
    // Party cells that can receive payouts (receive: AuthRequired::None).
    let party = |tag: u8| {
        let cell = Cell::with_balance([tag; 32], *blake3::hash(domain.as_bytes()).as_bytes(), 0);
        let id = cell.id();
        runtime
            .ledger()
            .lock()
            .unwrap()
            .insert_cell(cell)
            .expect("fresh party cell");
        id
    };
    let party_a = party(0xAA);
    let party_b = party(0xBB);
    (runtime, agent, party_a, party_b)
}

fn agent_pubkey(runtime: &AgentRuntime) -> [u8; 32] {
    runtime
        .cipherclerk()
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .public_key()
        .0
}

fn balance_of(runtime: &AgentRuntime, cell: CellId) -> u64 {
    runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&cell)
        .expect("cell exists")
        .state
        .balance()
}

fn state_slot_of(runtime: &AgentRuntime, cell: CellId) -> [u8; 32] {
    runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&cell)
        .expect("cell exists")
        .state
        .fields[STATE_SLOT as usize]
}

/// Deploy the plan's factory and run its create + fund + adopt + open turns.
///
/// Create and fund are ordinary agent turns; adopt is the one cell-agent
/// bootstrap turn (the cell self-grants the operator a capability, burning
/// `ADOPT_TURN_FEE` of the funded balance); open is an operator turn
/// targeting the cell (`execute_on`), gated by the installed program.
fn deploy_and_open(runtime: &mut AgentRuntime, plan: &SettlementCellPlan) {
    runtime.deploy_factory(plan.descriptor.clone());
    runtime
        .execute(plan.create_effects.clone())
        .expect("create turn (factory birth) must commit");
    runtime
        .execute(plan.fund_effects.clone())
        .expect("fund turn (value + adopt fee in) must commit");
    runtime
        .execute_as(plan.cell_id, plan.adopt_effects.clone(), ADOPT_TURN_FEE)
        .expect("adopt turn (operator self-grant) must commit");
    runtime
        .execute_on(plan.cell_id, plan.open_effects.clone())
        .expect("open turn (terms + OPEN) must commit");
}

/// Assert an executor-level cell-program rejection (NOT an SDK-side error).
fn assert_program_violation(result: Result<dregg_turn::TurnReceipt, SdkError>, what: &str) {
    match result {
        Err(SdkError::Turn(TurnError::ProgramViolation { .. })) => {}
        Err(other) => panic!("{what}: expected ProgramViolation, got {other:?}"),
        Ok(_) => panic!("{what}: expected the EXECUTOR to reject, but the turn committed"),
    }
}

/// Assert the executor rejected the turn for ANY reason. Used for the
/// full builder-shaped double-resolve attempts, where the payout `Transfer`
/// can fail on the already-drained balance BEFORE the program gate runs —
/// either gate stops the double spend; the program-specific tooth is proven
/// separately on a balance-free transition attempt.
fn assert_rejected(result: Result<dregg_turn::TurnReceipt, SdkError>, what: &str) {
    assert!(
        result.is_err(),
        "{what}: expected the EXECUTOR to reject, but the turn committed"
    );
}

/// A balance-free transition attempt: just the state-machine step (and an
/// optional witness write), no `Transfer`. Isolates the program's
/// `AllowedTransitions` tooth from balance accounting.
fn step_state_only(cell: CellId, witness: Option<[u8; 32]>, next_state: u64) -> Vec<Effect> {
    let mut effects = Vec::new();
    if let Some(w) = witness {
        effects.push(Effect::SetField {
            cell,
            index: dregg_cell::blueprint::WITNESS_SLOT as usize,
            value: w,
        });
    }
    effects.push(Effect::SetField {
        cell,
        index: STATE_SLOT as usize,
        value: field_from_u64(next_state),
    });
    effects
}

// =============================================================================
// Escrow — Dregg2.Apps.EscrowFactory
// =============================================================================

fn escrow_terms(depositor: CellId, beneficiary: CellId, timeout_height: u64) -> EscrowTerms {
    EscrowTerms {
        amount: 40,
        depositor: party_field(depositor),
        beneficiary: party_field(beneficiary),
        condition: field_from_u64(99),
        timeout_height,
    }
}

/// Happy path: fund → release with the correct condition witness. The value
/// is held in the escrow cell's own balance and conserved through release
/// (Lean `release_conserves` + keystone (d) `open_releasable`).
#[test]
fn escrow_fund_then_release_on_condition_commits() {
    let (mut runtime, agent, depositor, beneficiary) = harness("escrow-release");
    let terms = escrow_terms(depositor, beneficiary, 0);
    let plan = create_escrow_cell(&terms, agent_pubkey(&runtime), [0x01u8; 32], agent, agent)
        .expect("valid terms");
    deploy_and_open(&mut runtime, &plan);

    assert_eq!(
        balance_of(&runtime, plan.cell_id),
        40,
        "value held IN the escrow cell"
    );
    assert_eq!(
        state_slot_of(&runtime, plan.cell_id),
        field_from_u64(STATE_OPEN)
    );

    runtime
        .execute_on(
            plan.cell_id,
            release_escrow(plan.cell_id, &terms, field_from_u64(99)),
        )
        .expect("release with the correct witness must commit");

    assert_eq!(balance_of(&runtime, plan.cell_id), 0, "escrow drained");
    assert_eq!(
        balance_of(&runtime, beneficiary),
        40,
        "beneficiary credited exactly"
    );
    assert_eq!(
        state_slot_of(&runtime, plan.cell_id),
        field_from_u64(STATE_RESOLVED_A)
    );
}

/// Lean keystone (c) `release_requires_condition`: a release turn that does
/// not exhibit the condition witness — or exhibits a WRONG one — is rejected
/// by the cell program at the executor.
#[test]
fn escrow_release_without_condition_rejected_by_program() {
    let (mut runtime, agent, depositor, beneficiary) = harness("escrow-no-witness");
    let terms = escrow_terms(depositor, beneficiary, 0);
    let plan = create_escrow_cell(&terms, agent_pubkey(&runtime), [0x02u8; 32], agent, agent)
        .expect("valid terms");
    deploy_and_open(&mut runtime, &plan);

    // (a) A hand-built release that never writes the witness slot.
    let no_witness = vec![
        Effect::SetField {
            cell: plan.cell_id,
            index: STATE_SLOT as usize,
            value: field_from_u64(STATE_RESOLVED_A),
        },
        Effect::Transfer {
            from: plan.cell_id,
            to: beneficiary,
            amount: terms.amount,
        },
    ];
    assert_program_violation(
        runtime.execute_on(plan.cell_id, no_witness),
        "release without witness",
    );

    // (b) The builder's shape with a WRONG witness.
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            release_escrow(plan.cell_id, &terms, field_from_u64(7)),
        ),
        "release with wrong witness",
    );

    // Nothing moved; the escrow is still open and settleable.
    assert_eq!(balance_of(&runtime, plan.cell_id), 40);
    assert_eq!(balance_of(&runtime, beneficiary), 0);
    assert_eq!(
        state_slot_of(&runtime, plan.cell_id),
        field_from_u64(STATE_OPEN)
    );
}

/// The published refund timeout gates the refund leg on REAL block height:
/// before `timeout_height` the executor rejects; at the height it commits
/// (verb-era `CreateEscrow.timeout_height` semantics on the factory path).
#[test]
fn escrow_refund_before_timeout_rejected_after_timeout_commits() {
    let (mut runtime, agent, depositor, beneficiary) = harness("escrow-timeout");
    let terms = escrow_terms(depositor, beneficiary, 100);
    let plan = create_escrow_cell(&terms, agent_pubkey(&runtime), [0x03u8; 32], agent, agent)
        .expect("valid terms");
    deploy_and_open(&mut runtime, &plan);

    runtime.set_block_height(99);
    assert_program_violation(
        runtime.execute_on(plan.cell_id, refund_escrow(plan.cell_id, &terms)),
        "refund at height 99 < timeout 100",
    );
    assert_eq!(balance_of(&runtime, plan.cell_id), 40, "value still locked");

    runtime.set_block_height(100);
    runtime
        .execute_on(plan.cell_id, refund_escrow(plan.cell_id, &terms))
        .expect("refund at the timeout height must commit");
    assert_eq!(balance_of(&runtime, plan.cell_id), 0);
    assert_eq!(
        balance_of(&runtime, depositor),
        40,
        "depositor refunded exactly"
    );
    assert_eq!(
        state_slot_of(&runtime, plan.cell_id),
        field_from_u64(STATE_RESOLVED_B)
    );
}

/// Lean keystone (b) `no_double_resolve`: a released escrow is terminally
/// inert — no refund after release, no second release, and not even a
/// Transfer INTO it (terminal states have no transition row at all, so value
/// can never be stranded into a resolved cell).
#[test]
fn escrow_no_double_resolve() {
    let (mut runtime, agent, depositor, beneficiary) = harness("escrow-double");
    let terms = escrow_terms(depositor, beneficiary, 0);
    let plan = create_escrow_cell(&terms, agent_pubkey(&runtime), [0x04u8; 32], agent, agent)
        .expect("valid terms");
    deploy_and_open(&mut runtime, &plan);

    runtime
        .execute_on(
            plan.cell_id,
            release_escrow(plan.cell_id, &terms, field_from_u64(99)),
        )
        .expect("first release commits");

    // Balance-free attempts: the PROGRAM (no transition row out of a
    // terminal state) rejects, independent of the drained balance.
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            step_state_only(plan.cell_id, None, STATE_RESOLVED_B),
        ),
        "refund state-step after release",
    );
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            step_state_only(plan.cell_id, Some(field_from_u64(99)), STATE_RESOLVED_A),
        ),
        "second release state-step",
    );
    // Full builder-shaped attempts: also rejected (the drained balance stops
    // the payout even before the program gate).
    assert_rejected(
        runtime.execute_on(plan.cell_id, refund_escrow(plan.cell_id, &terms)),
        "refund after release",
    );
    assert_rejected(
        runtime.execute_on(
            plan.cell_id,
            release_escrow(plan.cell_id, &terms, field_from_u64(99)),
        ),
        "second release",
    );
    assert_program_violation(
        runtime.execute(vec![Effect::Transfer {
            from: agent,
            to: plan.cell_id,
            amount: 1,
        }]),
        "transfer into a resolved escrow",
    );
    assert_eq!(balance_of(&runtime, beneficiary), 40, "paid exactly once");
}

/// Deal-term integrity: once OPEN, re-pointing the published beneficiary is
/// rejected (the per-deal `Immutable` caveats / term pins).
#[test]
fn escrow_term_rewrite_rejected() {
    let (mut runtime, agent, depositor, beneficiary) = harness("escrow-tamper");
    let terms = escrow_terms(depositor, beneficiary, 0);
    let plan = create_escrow_cell(&terms, agent_pubkey(&runtime), [0x05u8; 32], agent, agent)
        .expect("valid terms");
    deploy_and_open(&mut runtime, &plan);

    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            vec![Effect::SetField {
                cell: plan.cell_id,
                index: PARTY_B_SLOT as usize,
                value: party_field(agent), // re-point the beneficiary to myself
            }],
        ),
        "beneficiary rewrite while open",
    );
}

// =============================================================================
// Obligation — Dregg2.Apps.ObligationFactory
// =============================================================================

fn obligation_terms(obligor: CellId, obligee: CellId) -> ObligationTerms {
    ObligationTerms {
        bond: 50,
        obligor: party_field(obligor),
        obligee: party_field(obligee),
        condition: field_from_u64(42),
        deadline_height: 200,
    }
}

/// Happy path: post bond → fulfil with the discharge witness (time-ungated);
/// the bond returns to the obligor (Lean `fulfil_requires_condition` +
/// conservation), and the discharged obligation cannot then be slashed.
#[test]
fn obligation_fulfill_on_condition_commits() {
    let (mut runtime, agent, obligor, obligee) = harness("obligation-fulfill");
    let terms = obligation_terms(obligor, obligee);
    let plan = create_obligation_cell(&terms, agent_pubkey(&runtime), [0x06u8; 32], agent, agent)
        .expect("valid terms");
    deploy_and_open(&mut runtime, &plan);
    assert_eq!(
        balance_of(&runtime, plan.cell_id),
        50,
        "bond held IN the cell"
    );

    runtime
        .execute_on(
            plan.cell_id,
            fulfill_obligation(plan.cell_id, &terms, field_from_u64(42)),
        )
        .expect("fulfil with the discharge witness must commit");
    assert_eq!(balance_of(&runtime, plan.cell_id), 0);
    assert_eq!(
        balance_of(&runtime, obligor),
        50,
        "bond returned to the obligor exactly"
    );

    // No-double-resolve: a fulfilled obligation cannot be slashed even past
    // the deadline (Lean `no_double_resolve_fulfilled`).
    runtime.set_block_height(1_000);
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            step_state_only(plan.cell_id, None, STATE_RESOLVED_B),
        ),
        "slash state-step after fulfilment",
    );
    assert_rejected(
        runtime.execute_on(plan.cell_id, slash_obligation(plan.cell_id, &terms)),
        "slash after fulfilment",
    );
    let _ = obligee;
}

/// The slash leg's two gates, on the real executor: (1) slashing before the
/// deadline is rejected; (2) a slash that exhibits the discharge condition is
/// rejected even past the deadline (Lean `slash_rejects_when_condition_met`);
/// a plain slash past the deadline forfeits the bond to the obligee.
#[test]
fn obligation_slash_gates_on_deadline_and_condition() {
    let (mut runtime, agent, obligor, obligee) = harness("obligation-slash");
    let terms = obligation_terms(obligor, obligee);
    let plan = create_obligation_cell(&terms, agent_pubkey(&runtime), [0x07u8; 32], agent, agent)
        .expect("valid terms");
    deploy_and_open(&mut runtime, &plan);

    // (1) Before the deadline: rejected.
    runtime.set_block_height(199);
    assert_program_violation(
        runtime.execute_on(plan.cell_id, slash_obligation(plan.cell_id, &terms)),
        "slash at height 199 < deadline 200",
    );

    // (2) Past the deadline but exhibiting the discharge condition: rejected.
    runtime.set_block_height(200);
    let mut slash_with_condition = slash_obligation(plan.cell_id, &terms);
    slash_with_condition.insert(
        0,
        Effect::SetField {
            cell: plan.cell_id,
            index: dregg_cell::blueprint::WITNESS_SLOT as usize,
            value: terms.condition,
        },
    );
    assert_program_violation(
        runtime.execute_on(plan.cell_id, slash_with_condition),
        "slash that exhibits the discharge condition",
    );

    // (3) Plain slash past the deadline: commits, bond to the obligee.
    runtime
        .execute_on(plan.cell_id, slash_obligation(plan.cell_id, &terms))
        .expect("slash past the deadline must commit");
    assert_eq!(balance_of(&runtime, plan.cell_id), 0);
    assert_eq!(
        balance_of(&runtime, obligee),
        50,
        "bond forfeited to the obligee"
    );
    assert_eq!(
        state_slot_of(&runtime, plan.cell_id),
        field_from_u64(STATE_RESOLVED_B)
    );

    // No-double-resolve (Lean `no_double_resolve_slashed`).
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            step_state_only(plan.cell_id, Some(field_from_u64(42)), STATE_RESOLVED_A),
        ),
        "fulfil state-step after slash",
    );
    assert_rejected(
        runtime.execute_on(
            plan.cell_id,
            fulfill_obligation(plan.cell_id, &terms, field_from_u64(42)),
        ),
        "fulfil after slash",
    );
}

// =============================================================================
// Bridge — Dregg2.Apps.BridgeCell
// =============================================================================

fn bridge_terms(originator: CellId, pot: CellId, timeout_height: u64) -> BridgeTerms {
    BridgeTerms {
        amount: 75,
        originator: party_field(originator),
        pot: party_field(pot),
        finality_witness: field_from_u64(777),
        timeout_height,
    }
}

/// Lean `finalize_requires_finality_witness` + `no_double_finalize`: a
/// finalize without the finality witness is rejected; with it, the locked
/// value moves to the pot exactly once.
#[test]
fn bridge_finalize_requires_finality_witness() {
    let (mut runtime, agent, originator, pot) = harness("bridge-finalize");
    let terms = bridge_terms(originator, pot, 0);
    let plan = bridge_lock_cell(&terms, agent_pubkey(&runtime), [0x08u8; 32], agent, agent)
        .expect("valid terms");
    deploy_and_open(&mut runtime, &plan);
    assert_eq!(
        balance_of(&runtime, plan.cell_id),
        75,
        "locked IN the bridge cell"
    );

    // Without the witness: a hand-built finalize is rejected.
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            vec![
                Effect::SetField {
                    cell: plan.cell_id,
                    index: STATE_SLOT as usize,
                    value: field_from_u64(STATE_RESOLVED_A),
                },
                Effect::Transfer {
                    from: plan.cell_id,
                    to: pot,
                    amount: terms.amount,
                },
            ],
        ),
        "finalize without the finality witness",
    );

    runtime
        .execute_on(
            plan.cell_id,
            finalize_bridge(plan.cell_id, &terms, field_from_u64(777)),
        )
        .expect("finalize with the finality witness must commit");
    assert_eq!(balance_of(&runtime, pot), 75, "pot credited exactly");
    assert_eq!(balance_of(&runtime, plan.cell_id), 0);

    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            step_state_only(plan.cell_id, Some(field_from_u64(777)), STATE_RESOLVED_A),
        ),
        "second finalize state-step",
    );
    assert_rejected(
        runtime.execute_on(
            plan.cell_id,
            finalize_bridge(plan.cell_id, &terms, field_from_u64(777)),
        ),
        "second finalize",
    );
}

/// Lean `locked_cancellable` + `no_refinalize_after_cancel`: with a zero
/// timeout the lock is cancellable any time while locked (value can never be
/// trapped); a cancelled lock cannot be finalized afterwards.
#[test]
fn bridge_cancel_recovers_value_and_blocks_refinalize() {
    let (mut runtime, agent, originator, pot) = harness("bridge-cancel");
    let terms = bridge_terms(originator, pot, 0);
    let plan = bridge_lock_cell(&terms, agent_pubkey(&runtime), [0x09u8; 32], agent, agent)
        .expect("valid terms");
    deploy_and_open(&mut runtime, &plan);

    runtime
        .execute_on(plan.cell_id, cancel_bridge(plan.cell_id, &terms))
        .expect("cancel of a zero-timeout lock must commit any time while locked");
    assert_eq!(
        balance_of(&runtime, originator),
        75,
        "locked value recovered by the originator exactly"
    );

    runtime.set_block_height(900);
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            step_state_only(plan.cell_id, Some(field_from_u64(777)), STATE_RESOLVED_A),
        ),
        "finalize state-step after cancel",
    );
    assert_rejected(
        runtime.execute_on(
            plan.cell_id,
            finalize_bridge(plan.cell_id, &terms, field_from_u64(777)),
        ),
        "finalize after cancel",
    );
    let _ = pot;
}

/// The nonzero-timeout cancel leg mirrors the verb-era `BridgeLock`
/// recovery: cancellation is admitted only once the timeout height passes.
#[test]
fn bridge_cancel_before_timeout_rejected() {
    let (mut runtime, agent, originator, pot) = harness("bridge-cancel-timeout");
    let terms = bridge_terms(originator, pot, 500);
    let plan = bridge_lock_cell(&terms, agent_pubkey(&runtime), [0x0Au8; 32], agent, agent)
        .expect("valid terms");
    deploy_and_open(&mut runtime, &plan);

    runtime.set_block_height(499);
    assert_program_violation(
        runtime.execute_on(plan.cell_id, cancel_bridge(plan.cell_id, &terms)),
        "cancel at height 499 < timeout 500",
    );

    runtime.set_block_height(500);
    runtime
        .execute_on(plan.cell_id, cancel_bridge(plan.cell_id, &terms))
        .expect("cancel at the timeout height must commit");
}
