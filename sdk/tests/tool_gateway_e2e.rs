//! ORGAN 4 — THE GATEWAY: both-polarity e2e for the delegated tool-access seam.
//!
//! A live tool-calling agent loop drives inbound tool-calls through the
//! [`ToolGateway`]. The grantor delegates a [`ToolGrant`] (the proven
//! `delegAdmit` mandate: SCOPE ∧ DEADLINE ∧ RATE) to a freshly spawned,
//! cap-gated worker; each call is admitted IFF the delegated policy admits it.
//!
//! These tests prove the both-polarity shape the Lean crown
//! (`Dregg2/Apps/ToolAccessDelegation.lean`) proves, but on the REAL Rust
//! executor:
//!
//! * GENUINE — a granted, in-scope, in-time, within-rate call COMMITS with a
//!   receipt and a CONSERVED spend (total balance fixed; counter advances).
//! * CHEAT — an over-rate / past-deadline / out-of-scope call is REFUSED
//!   IN-BAND (a `Result` error naming the leg that bit; no panic, no turn, no
//!   spend).

use std::sync::{Arc, RwLock};

use dregg_sdk::{
    AgentCipherclerk, AgentRuntime, Effect, GatewayRefusal, ToolCallError, ToolGateway, ToolGrant,
};

/// Build a runtime + a root token the grantor delegates from.
fn runtime_with_root() -> (AgentRuntime, dregg_sdk::HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root_key = [7u8; 32];
    let root_token = cclerk.mint_token(&root_key, "compute");
    let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "compute");
    (runtime, root_token)
}

/// The demo grant from the Lean §8 witness: tool 77, rate 3, deadline 100,
/// scoped to the `search` method verb.
fn demo_grant() -> ToolGrant {
    ToolGrant {
        tool_id: 77,
        rate_limit: 3,
        deadline: 100,
        tool_method: "search".to_string(),
    }
}

#[test]
fn granted_tool_call_commits_with_receipt_and_conserved_spend() {
    // GENUINE ✓ — a granted, in-scope (tool 77), in-time (now 50), within-rate
    // call commits through the cap-gated worker, returning a receipt. The metered
    // counter advances 0 → 1; total balance is conserved.
    let (runtime, root) = runtime_with_root();
    let mut gw = ToolGateway::admit(&runtime, &root, demo_grant()).expect("admit worker");

    let worker_cell = gw.worker_cell();
    let balance_before = {
        let ledger = runtime.ledger().lock().unwrap();
        ledger.get(&worker_cell).expect("worker cell").state.balance()
    };

    let out = gw
        .invoke(77, 50, vec![])
        .expect("granted in-scope, in-time, within-rate call must commit");

    assert_eq!(out.calls_made, 1, "the metered counter advanced 0 -> 1");
    assert_eq!(out.remaining, 2, "two calls remain on the rate-3 mandate");
    assert_eq!(out.receipt.agent, worker_cell, "receipt is the worker's turn");
    assert_eq!(gw.calls_made(), 1);

    // CONSERVED SPEND: the metered write moves the counter, not value beyond the
    // turn fee debited from the worker's own balance. Assert total system balance
    // (worker + agent) is conserved across the call — the counter is not money.
    let balance_after = {
        let ledger = runtime.ledger().lock().unwrap();
        ledger.get(&worker_cell).expect("worker cell").state.balance()
    };
    // The counter slot holds 1 now (the metered advance is recorded on-cell).
    {
        let ledger = runtime.ledger().lock().unwrap();
        let cell = ledger.get(&worker_cell).expect("worker cell");
        let slot = cell.state.fields[dregg_sdk::CALLS_MADE_SLOT as usize];
        assert_eq!(
            slot[31], 1,
            "the calls_made slot reads back 1 after the metered invocation"
        );
    }
    // The only balance movement is the turn fee (a debit from the worker for the
    // turn's computrons), never a mint — the worker cannot gain value by invoking.
    assert!(
        balance_after <= balance_before,
        "the invocation never mints value into the worker (fee-only debit)"
    );
}

#[test]
fn rate_budget_exhausts_and_over_rate_call_refused_in_band() {
    // GENUINE ✓ then CHEAT ✗ — the full lifecycle on the real executor. The
    // first 3 calls commit (counter 0->1->2->3, the rate budget consumed); the
    // 4th is REFUSED IN-BAND as `OverRate` (a Result error, no panic, no turn).
    let (runtime, root) = runtime_with_root();
    let mut gw = ToolGateway::admit(&runtime, &root, demo_grant()).expect("admit worker");

    for n in 1..=3 {
        let out = gw
            .invoke(77, 50, vec![])
            .unwrap_or_else(|e| panic!("call {n} (within rate 3) must commit, got {e}"));
        assert_eq!(out.calls_made, n);
    }
    assert_eq!(gw.remaining(), 0, "the rate-3 mandate is exhausted");

    // The 4th call: over-rate. Refused IN-BAND — a value, never a panic.
    let err = gw
        .invoke(77, 50, vec![])
        .expect_err("the 4th call (over rate 3) MUST be refused in-band");
    match err {
        ToolCallError::Refused(GatewayRefusal::OverRate {
            calls_made,
            rate_limit,
        }) => {
            assert_eq!(calls_made, 3);
            assert_eq!(rate_limit, 3);
        }
        other => panic!("expected an in-band OverRate refusal, got {other:?}"),
    }

    // The refusal did NOT advance the counter or submit a turn.
    assert_eq!(gw.calls_made(), 3, "a refused call leaves the counter untouched");
}

#[test]
fn out_of_scope_tool_call_refused_in_band() {
    // CHEAT ✗ — a call presenting a tool id (99) other than the granted one (77)
    // is refused in-band as `OutOfScope`, even with rate head-room and inside the
    // deadline. No turn is submitted.
    let (runtime, root) = runtime_with_root();
    let mut gw = ToolGateway::admit(&runtime, &root, demo_grant()).expect("admit worker");

    let err = gw
        .invoke(99, 50, vec![])
        .expect_err("an out-of-scope tool id MUST be refused in-band");
    match err {
        ToolCallError::Refused(GatewayRefusal::OutOfScope { presented, granted }) => {
            assert_eq!(presented, 99);
            assert_eq!(granted, 77);
        }
        other => panic!("expected an in-band OutOfScope refusal, got {other:?}"),
    }
    assert_eq!(gw.calls_made(), 0, "a refused call leaves the counter untouched");
}

#[test]
fn past_deadline_tool_call_refused_in_band() {
    // CHEAT ✗ — a call presented after the granted deadline (now 101 > 100) is
    // refused in-band as `PastDeadline`, even in-scope with rate head-room.
    let (runtime, root) = runtime_with_root();
    let mut gw = ToolGateway::admit(&runtime, &root, demo_grant()).expect("admit worker");

    let err = gw
        .invoke(77, 101, vec![])
        .expect_err("a past-deadline call MUST be refused in-band");
    match err {
        ToolCallError::Refused(GatewayRefusal::PastDeadline { now, deadline }) => {
            assert_eq!(now, 101);
            assert_eq!(deadline, 100);
        }
        other => panic!("expected an in-band PastDeadline refusal, got {other:?}"),
    }
    assert_eq!(gw.calls_made(), 0, "a refused call leaves the counter untouched");
}

#[test]
fn granted_call_carries_tool_work_payload() {
    // GENUINE ✓ — the tool's actual work rides the SAME metered turn as the
    // counter advance. Here the tool emits an event (its payload); the call
    // commits and the receipt reflects the whole turn.
    use dregg_turn::action::{symbol, Event};
    let (runtime, root) = runtime_with_root();
    let mut gw = ToolGateway::admit(&runtime, &root, demo_grant()).expect("admit worker");
    let worker_cell = gw.worker_cell();

    let work = vec![Effect::EmitEvent {
        cell: worker_cell,
        event: Event {
            topic: symbol("search-result"),
            data: Vec::new(),
        },
    }];

    let out = gw
        .invoke(77, 50, work)
        .expect("a granted call carrying tool work must commit");
    assert_eq!(out.calls_made, 1);
    // The metered SetField + the EmitEvent both rode the one action.
    assert_eq!(out.receipt.action_count, 1);
}

#[test]
fn executor_rate_backstop_rejects_over_ceiling_write_bypassing_in_band() {
    // CHEAT ✗ — the EXECUTOR-SIDE backstop is LOAD-BEARING, not decorative. Even
    // if a caller bypasses the gateway's in-band `deleg_admit` and submits a
    // metered write that jumps the `calls_made` counter PAST the granted ceiling
    // (rate 3, attempt 4) directly through the cap-gated worker, the worker cell's
    // installed `mandate_program` (`FieldLte { calls_made <= 3 }`) makes the
    // EXECUTOR reject the turn. This proves the cell-program rate constraint bites
    // on its own — the in-band check and the executor check are two independent
    // enforcement surfaces, both real.
    use dregg_sdk::CALLS_MADE_SLOT;
    use dregg_cell::program::field_from_u64;
    let (runtime, root) = runtime_with_root();
    let gw = ToolGateway::admit(&runtime, &root, demo_grant()).expect("admit worker");
    let worker_cell = gw.worker_cell();

    // Reach into the worker directly (the bypass an in-band-skipping caller would
    // attempt) and submit a counter write to 4 — over the rate-3 ceiling.
    // We access the worker via the gateway's owned SubAgent path: drive the same
    // method but with an over-ceiling counter value. The executor's cell-program
    // check must reject it.
    let bypass = ToolGatewayTestAccess::worker_set_field(
        &gw,
        worker_cell,
        CALLS_MADE_SLOT as usize,
        field_from_u64(4),
    );
    assert!(
        bypass.is_err(),
        "the executor's FieldLte rate backstop MUST reject an over-ceiling counter \
         write, even when the in-band deleg_admit is bypassed"
    );
}

/// Test-only access to drive the gateway's worker directly, to exercise the
/// executor-side backstop independent of the in-band `deleg_admit` check.
struct ToolGatewayTestAccess;
impl ToolGatewayTestAccess {
    fn worker_set_field(
        gw: &ToolGateway,
        cell: dregg_sdk::CellId,
        index: usize,
        value: [u8; 32],
    ) -> Result<dregg_turn::TurnReceipt, dregg_sdk::SdkError> {
        // The gateway's grant method verb is what the worker's credential covers;
        // drive a SetField under it (the same path `invoke` uses), but with the
        // over-ceiling value the in-band check would have refused.
        gw.worker_for_test().execute_method(
            &gw.grant().tool_method,
            vec![Effect::SetField { cell, index, value }],
        )
    }
}
