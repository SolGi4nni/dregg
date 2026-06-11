//! End-to-end teeth for the polis AGENT-ORCHESTRATION layer (budgeted
//! delegation via worker mandate cells) on the REAL executor.
//!
//! The orchestrator (this runtime's agent cell) births per-worker mandate
//! cells from content-addressed factories; each worker's budget slice IS the
//! mandate cell's own funded balance (kernel conservation is the spend cap —
//! `starbridge_polis` lib docs, gap 5), its tool scope and delegating
//! orchestrator are pinned literals, and revocation steps the cell into a
//! terminal state with NO outgoing transition row — every subsequent touch
//! is rejected by the EXECUTOR (`TurnError::ProgramViolation`), not by SDK
//! checks.

use dregg_cell::{Cell, CellId, field_from_u64};
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_sdk::polis::{
    GovernanceCellPlan, WorkerMandate, activate_worker, revoke_worker, spawn_worker_mandate,
    tool_scope_commitment, worker_factory_descriptor, worker_spend,
};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, Effect, SdkError};
use dregg_turn::TurnReceipt;
use dregg_turn::TurnError;
use starbridge_polis::STATE_SLOT;
use starbridge_polis::mandate::{STATE_ACTIVE, STATE_REVOKED, TOOL_SCOPE_SLOT};

// =============================================================================
// Harness (matches sdk/tests/factory_settlement_e2e.rs)
// =============================================================================

fn harness(domain: &str) -> (AgentRuntime, CellId, CellId) {
    let runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), domain);
    let orchestrator = runtime.cell_id();
    let vendor = {
        let cell = Cell::with_balance([0xEE; 32], *blake3::hash(domain.as_bytes()).as_bytes(), 0);
        let id = cell.id();
        runtime
            .ledger()
            .lock()
            .unwrap()
            .insert_cell(cell)
            .expect("fresh vendor cell");
        id
    };
    (runtime, orchestrator, vendor)
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

fn slot_of(runtime: &AgentRuntime, cell: CellId, slot: u8) -> [u8; 32] {
    runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&cell)
        .expect("cell exists")
        .state
        .fields[slot as usize]
}

/// Deploy + create + fund(slice + fee) + adopt + activate one worker.
fn spawn_and_activate(
    runtime: &mut AgentRuntime,
    mandate: &WorkerMandate,
    token_id: [u8; 32],
    funder: CellId,
) -> GovernanceCellPlan {
    let plan = spawn_worker_mandate(mandate, agent_pubkey(runtime), token_id, funder)
        .expect("valid mandate");
    runtime.deploy_factory(plan.descriptor.clone());
    runtime
        .execute(plan.create_effects.clone())
        .expect("create turn (worker birth) must commit");
    runtime
        .execute(plan.fund_effects.clone())
        .expect("fund turn (slice + adopt fee) must commit");
    runtime
        .execute_as(plan.cell_id, plan.adopt_effects.clone(), ADOPT_TURN_FEE)
        .expect("adopt turn must commit");
    runtime
        .execute_on(plan.cell_id, activate_worker(plan.cell_id, mandate))
        .expect("activate turn (mandate terms + ACTIVE) must commit");
    plan
}

fn assert_program_violation(result: Result<TurnReceipt, SdkError>, what: &str) {
    match result {
        Err(SdkError::Turn(TurnError::ProgramViolation { .. })) => {}
        Err(other) => panic!("{what}: expected ProgramViolation, got {other:?}"),
        Ok(_) => panic!("{what}: expected the EXECUTOR to reject, but the turn committed"),
    }
}

/// Assert the executor rejected for ANY reason (used for overspends, where
/// the conservation gate — not the program — stops the turn).
fn assert_rejected(result: Result<TurnReceipt, SdkError>, what: &str) {
    assert!(
        result.is_err(),
        "{what}: expected the EXECUTOR to reject, but the turn committed"
    );
}

// =============================================================================
// The budgeted-delegation usecase
// =============================================================================

/// Two workers under one orchestrator: distinct slices, distinct tool
/// scopes; one worker tries to exceed its slice → REJECTED (conservation —
/// the slice IS the balance); the other is revoked → all further spends
/// REJECTED (terminal, inert); receipts chain the whole orchestration and
/// every worker cell resolves to its content-addressed mandate.
#[test]
fn orchestrate_two_workers_slices_and_revocation() {
    let (mut runtime, orchestrator, vendor) = harness("polis-orchestration");

    let mandate_a = WorkerMandate {
        orchestrator,
        slice: 30,
        tool_scope: tool_scope_commitment(&["search", "fetch"]),
        worker_tag: field_from_u64(1),
    };
    let mandate_b = WorkerMandate {
        orchestrator,
        slice: 20,
        tool_scope: tool_scope_commitment(&["deploy"]),
        worker_tag: field_from_u64(2),
    };
    let worker_a = spawn_and_activate(&mut runtime, &mandate_a, [0x41; 32], orchestrator);
    let worker_b = spawn_and_activate(&mut runtime, &mandate_b, [0x42; 32], orchestrator);

    // The slices are the funded balances, exactly.
    assert_eq!(balance_of(&runtime, worker_a.cell_id), 30);
    assert_eq!(balance_of(&runtime, worker_b.cell_id), 20);
    assert_eq!(
        slot_of(&runtime, worker_a.cell_id, STATE_SLOT),
        field_from_u64(STATE_ACTIVE)
    );

    // Provenance: each worker cell is the content-addressed image of its
    // mandate — anyone can rederive the descriptor from the published terms.
    assert_eq!(
        worker_a.descriptor.hash(),
        worker_factory_descriptor(&mandate_a).unwrap().hash()
    );
    assert_ne!(
        worker_a.factory_vk, worker_b.factory_vk,
        "distinct mandates, distinct factories"
    );

    // Worker A spends within its slice.
    let spend_a1 = runtime
        .execute_on(worker_a.cell_id, worker_spend(worker_a.cell_id, vendor, 25))
        .expect("spend within the slice must commit");
    assert_eq!(balance_of(&runtime, vendor), 25);
    assert_eq!(balance_of(&runtime, worker_a.cell_id), 5);

    // Worker A tries to exceed the remaining slice: the kernel conservation
    // law rejects (the slice IS the balance — there is nothing else to draw).
    assert_rejected(
        runtime.execute_on(worker_a.cell_id, worker_spend(worker_a.cell_id, vendor, 10)),
        "spend exceeding the remaining slice",
    );
    assert_eq!(balance_of(&runtime, vendor), 25, "nothing moved");
    assert_eq!(balance_of(&runtime, worker_a.cell_id), 5);

    // Worker B spends, then the orchestrator revokes it, recovering the
    // unspent remainder in the same (last possible) turn.
    let spend_b1 = runtime
        .execute_on(worker_b.cell_id, worker_spend(worker_b.cell_id, vendor, 5))
        .expect("worker B spend must commit");
    assert_eq!(balance_of(&runtime, vendor), 30);
    let revoke_receipt = runtime
        .execute_on(
            worker_b.cell_id,
            revoke_worker(worker_b.cell_id, Some((orchestrator, 15))),
        )
        .expect("revoke + recovery must commit");
    assert_eq!(
        slot_of(&runtime, worker_b.cell_id, STATE_SLOT),
        field_from_u64(STATE_REVOKED)
    );
    assert_eq!(
        balance_of(&runtime, worker_b.cell_id),
        0,
        "remainder recovered"
    );

    // The revoked worker is INERT: spends, re-activation, even funding it
    // again — all rejected by the EXECUTOR. (The drained balance stops the
    // builder-shaped spend even before the program gate — either gate stops
    // it, matching the settlement-suite precedent; the program-specific
    // tooth is the balance-free state-step and the transfer-in below.)
    assert_rejected(
        runtime.execute_on(worker_b.cell_id, worker_spend(worker_b.cell_id, vendor, 1)),
        "spend after revocation",
    );
    assert_program_violation(
        runtime.execute_on(
            worker_b.cell_id,
            vec![Effect::SetField {
                cell: worker_b.cell_id,
                index: STATE_SLOT as usize,
                value: field_from_u64(STATE_ACTIVE),
            }],
        ),
        "re-activating a revoked worker",
    );
    assert_program_violation(
        runtime.execute(vec![Effect::Transfer {
            from: orchestrator,
            to: worker_b.cell_id,
            amount: 1,
        }]),
        "re-funding a revoked worker",
    );

    // Worker A is unaffected and can still spend its remainder.
    runtime
        .execute_on(worker_a.cell_id, worker_spend(worker_a.cell_id, vendor, 5))
        .expect("worker A still active");
    assert_eq!(balance_of(&runtime, vendor), 35);

    // Provenance chain: every orchestration action is a receipt on the
    // operator chain, hash-linked from the first spend through the
    // revocation (the audit trail back to the mandates).
    let chain = runtime
        .cipherclerk()
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .receipt_chain()
        .to_vec();
    let pos = |r: &TurnReceipt| {
        chain
            .iter()
            .position(|c| c.receipt_hash() == r.receipt_hash())
            .expect("orchestration receipt is on the operator chain")
    };
    let (a1, b1, rv) = (pos(&spend_a1), pos(&spend_b1), pos(&revoke_receipt));
    assert!(a1 < b1 && b1 < rv, "ceremony order is the chain order");
    for w in chain[a1..=rv].windows(2) {
        assert_eq!(
            w[1].previous_receipt_hash,
            Some(w[0].receipt_hash()),
            "orchestration receipts are hash-chained"
        );
    }
}

/// The mandate terms are pinned: rewriting the tool scope (widening the
/// mandate) or the published slice is rejected by the program.
#[test]
fn worker_mandate_terms_pinned() {
    let (mut runtime, orchestrator, _vendor) = harness("polis-mandate-pin");
    let mandate = WorkerMandate {
        orchestrator,
        slice: 10,
        tool_scope: tool_scope_commitment(&["search"]),
        worker_tag: field_from_u64(7),
    };
    let worker = spawn_and_activate(&mut runtime, &mandate, [0x43; 32], orchestrator);

    assert_program_violation(
        runtime.execute_on(
            worker.cell_id,
            vec![Effect::SetField {
                cell: worker.cell_id,
                index: TOOL_SCOPE_SLOT as usize,
                value: tool_scope_commitment(&["search", "deploy", "rm-rf"]),
            }],
        ),
        "widening the pinned tool scope",
    );

    // A second cell from the SAME mandate descriptor: rejected — a mandate
    // is a per-worker singleton (creation_budget = 1); a second worker needs
    // its own tag (its own content address).
    let twin = spawn_worker_mandate(&mandate, agent_pubkey(&runtime), [0x4F; 32], orchestrator)
        .expect("valid mandate");
    assert!(
        runtime.execute(twin.create_effects.clone()).is_err(),
        "a worker mandate is a singleton (creation_budget = 1)"
    );

    // Activating with terms that differ from the published literals is also
    // rejected (a lying activation cannot commit).
    let mandate2 = WorkerMandate {
        worker_tag: field_from_u64(8),
        ..mandate.clone()
    };
    let plan2 = spawn_worker_mandate(&mandate2, agent_pubkey(&runtime), [0x44; 32], orchestrator)
        .expect("valid mandate");
    runtime.deploy_factory(plan2.descriptor.clone());
    runtime
        .execute(plan2.create_effects.clone())
        .expect("create");
    runtime.execute(plan2.fund_effects.clone()).expect("fund");
    runtime
        .execute_as(plan2.cell_id, plan2.adopt_effects.clone(), ADOPT_TURN_FEE)
        .expect("adopt");
    let lying = WorkerMandate {
        slice: 9_999, // claim a bigger published slice than the descriptor's
        ..mandate2.clone()
    };
    assert_program_violation(
        runtime.execute_on(plan2.cell_id, activate_worker(plan2.cell_id, &lying)),
        "activating with unpublished mandate terms",
    );
}

/// Build-time fail-closed: a zero slice or zero tool scope never becomes a
/// descriptor at all.
#[test]
fn worker_mandate_build_fail_closed() {
    let (runtime, orchestrator, _vendor) = harness("polis-mandate-build");
    let zero_slice = WorkerMandate {
        orchestrator,
        slice: 0,
        tool_scope: tool_scope_commitment(&["search"]),
        worker_tag: field_from_u64(1),
    };
    assert!(
        spawn_worker_mandate(
            &zero_slice,
            agent_pubkey(&runtime),
            [0x45; 32],
            orchestrator
        )
        .is_err()
    );
    let zero_scope = WorkerMandate {
        orchestrator,
        slice: 10,
        tool_scope: [0u8; 32],
        worker_tag: field_from_u64(1),
    };
    assert!(
        spawn_worker_mandate(
            &zero_scope,
            agent_pubkey(&runtime),
            [0x46; 32],
            orchestrator
        )
        .is_err()
    );
}
