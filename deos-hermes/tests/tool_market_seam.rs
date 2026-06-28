//! THE PAID SEAM — a Hermes ACP tool-call becomes a cap-gated, metered, AND
//! CHARGED dregg turn: the confined agent PAYS deos (the provider) per tool-call.
//!
//! This is the "pay to access another agent's tools/models" layer of the agent
//! service economy, driven through the real ACP↔ToolGateway seam:
//!
//! * GENUINE — an in-scope, within-rate, within-budget tool-call commits; the
//!   provider cell is credited the per-call price (the charge is conserved
//!   consumer → provider), and deos returns `Allow` with `paid == price`.
//! * OVER-BUDGET — once the consumer's spend allowance is exhausted, the call is
//!   REFUSED IN-BAND; deos returns `Reject` naming the budget leg. No turn, no
//!   charge.

use std::sync::{Arc, RwLock};

use deos_hermes::{GrantRegistry, HermesGateway, PermissionOutcome, ToolCallRequest, ToolMarket};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, Attenuation, CellId, HeldToken};

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root_token = cclerk.mint_token(&[7u8; 32], "deos");
    let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (runtime, root_token)
}

fn spawn_provider(runtime: &AgentRuntime, root: &HeldToken) -> CellId {
    runtime
        .spawn_sub_agent_scoped(&Attenuation::default(), root, &["provide"])
        .expect("spawn provider")
        .cell_id()
}

fn balance(runtime: &AgentRuntime, cell: CellId) -> i64 {
    let l = runtime.ledger().lock().unwrap();
    l.get(&cell).map(|c| c.state.balance()).unwrap_or(0)
}

fn args() -> serde_json::Value {
    serde_json::json!({"query": "x"})
}

#[test]
fn confined_agent_pays_provider_per_tool_call_then_refused_over_budget() {
    let (runtime, root) = grantor();
    let provider = spawn_provider(&runtime, &root);

    let price = 1_000u64;
    let budget = 2_500u64; // two paid calls, then over-budget on the third.
    let registry = GrantRegistry::default_for_session(1000);
    let market = ToolMarket::flat(provider, price, budget);
    let mut gw = HermesGateway::new_paid(&runtime, root, registry, market);

    let p0 = balance(&runtime, provider);

    // Call 1 — cap-checked + metered + CHARGED.
    let call1 = ToolCallRequest::new("s1", "tc-1", "web_search", args());
    match gw.admit_with_work(&call1, 50, Some(vec![])) {
        PermissionOutcome::Allow { paid, receipt, .. } => {
            assert_eq!(paid, price, "the verdict records the per-call charge");
            assert_eq!(receipt.len(), 64, "a real hex turn-hash receipt");
        }
        other => panic!("call 1 must be allowed + charged, got {other:?}"),
    }
    // The charge LANDED conserved consumer → provider.
    assert_eq!(
        balance(&runtime, provider),
        p0 + price as i64,
        "provider credited exactly the price"
    );
    assert_eq!(gw.total_spent(), price, "session spend tracks the charge");

    // Call 2 — charged again.
    let call2 = ToolCallRequest::new("s1", "tc-2", "web_search", args());
    assert!(gw.admit_with_work(&call2, 50, Some(vec![])).allowed());
    assert_eq!(
        balance(&runtime, provider),
        p0 + 2 * price as i64,
        "two calls credited the provider 2x price (conserved)"
    );
    assert_eq!(gw.total_spent(), 2 * price);

    // Call 3 — OVER BUDGET (2_000 spent + 1_000 > 2_500): refused IN-BAND.
    let call3 = ToolCallRequest::new("s1", "tc-3", "web_search", args());
    match gw.admit_with_work(&call3, 50, Some(vec![])) {
        PermissionOutcome::Reject { reason, .. } => {
            assert!(
                reason.contains("budget exhausted"),
                "the refusal names the budget leg: {reason}"
            );
        }
        other => panic!("call 3 must be refused over-budget, got {other:?}"),
    }
    // The refusal paid the provider nothing and did not advance the spend.
    assert_eq!(
        balance(&runtime, provider),
        p0 + 2 * price as i64,
        "an over-budget refusal pays nothing"
    );
    assert_eq!(
        gw.total_spent(),
        2 * price,
        "an over-budget refusal does not spend"
    );
}

#[test]
fn free_session_charges_nothing() {
    // A non-paid session (the original shape) behaves exactly as before: paid 0.
    let (runtime, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000);
    let mut gw = HermesGateway::new(&runtime, root, registry);
    assert!(gw.market().is_none());

    let call = ToolCallRequest::new("s1", "tc-1", "web_search", args());
    match gw.admit_with_work(&call, 50, Some(vec![])) {
        PermissionOutcome::Allow { paid, .. } => {
            assert_eq!(paid, 0, "free session charges nothing")
        }
        other => panic!("expected a free allow, got {other:?}"),
    }
    assert_eq!(gw.total_spent(), 0);
}
