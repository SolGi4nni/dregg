//! THE SEAM TEST — a Hermes-style ACP tool-call becomes a cap-gated, metered,
//! RECEIPTED dregg turn (or an in-band refusal), through the proven
//! [`ToolGateway`] over the REAL verified executor.
//!
//! Both polarities, exactly the shape the Lean crown
//! (`Dregg2/Apps/ToolAccessDelegation.lean`) proves and the SDK's
//! `tool_gateway_e2e.rs` exercises — but driven from an ACP tool-call shape:
//!
//! * GENUINE — an in-scope, in-time, within-rate Hermes tool-call commits and
//!   deos returns `Allow` with a real receipt id + remaining budget.
//! * CHEAT — an over-rate / past-deadline tool-call is refused IN-BAND; deos
//!   returns `Reject` naming the leg that bit. No turn, no spend.

use std::sync::{Arc, RwLock};

use deos_hermes::{GrantRegistry, HermesGateway, PermissionOutcome, ToolCallRequest, ToolKind};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken, ToolGrant};

/// Build a grantor runtime + root token (the deos side).
fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root_key = [7u8; 32];
    let root_token = cclerk.mint_token(&root_key, "deos");
    let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (runtime, root_token)
}

fn args() -> serde_json::Value {
    serde_json::json!({"query": "x"})
}

#[test]
fn hermes_tool_call_becomes_a_cap_gated_receipted_turn() {
    // GENUINE ✓ — a `web_search` (kind Fetch) call, in-time (now 50), within
    // the Fetch rate (50). deos admits a cap-gated worker under the Fetch grant
    // and the metered turn COMMITS on the verified executor: deos returns Allow
    // with a real receipt id and the remaining budget.
    let (runtime, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000);
    let mut gw = HermesGateway::new(&runtime, root, registry);

    let call = ToolCallRequest::new("s1", "tc-1", "web_search", args());
    assert_eq!(call.kind, ToolKind::Fetch, "web_search classifies as Fetch");

    let outcome = gw.admit_with_work(&call, 50, Some(vec![]));
    match outcome {
        PermissionOutcome::Allow {
            tool_call_id,
            receipt,
            remaining,
            ..
        } => {
            assert_eq!(tool_call_id, "tc-1");
            // A genuine 32-byte turn hash, hex-encoded — proof the metered turn
            // committed on the verified executor.
            assert_eq!(
                receipt.len(),
                64,
                "receipt is a hex-encoded 32-byte turn hash"
            );
            assert!(
                receipt.chars().all(|c| c.is_ascii_hexdigit()),
                "receipt id is hex"
            );
            assert_eq!(remaining, 49, "one of the rate-50 Fetch budget consumed");
        }
        other => panic!("expected Allow with a receipt, got {other:?}"),
    }
    assert_eq!(gw.calls_made(ToolKind::Fetch), 1);
}

#[test]
fn over_rate_tool_call_refused_in_band() {
    // CHEAT ✗ — tighten Execute to rate 1; the 2nd `terminal` call exceeds it
    // and is refused IN-BAND (no turn). deos returns Reject naming the rate leg.
    let (runtime, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000).with_grant(
        ToolKind::Execute,
        ToolGrant {
            tool_id: 40,
            rate_limit: 1,
            deadline: 1000,
            tool_method: "tool.execute".to_string(),
        },
    );
    let mut gw = HermesGateway::new(&runtime, root, registry);

    let c1 = ToolCallRequest::new("s1", "tc-1", "terminal", args());
    let c2 = ToolCallRequest::new("s1", "tc-2", "terminal", args());
    assert_eq!(c1.kind, ToolKind::Execute);

    assert!(
        gw.admit_with_work(&c1, 50, Some(vec![])).allowed(),
        "first call commits"
    );

    let outcome = gw.admit_with_work(&c2, 50, Some(vec![]));
    match outcome {
        PermissionOutcome::Reject {
            tool_call_id,
            reason,
        } => {
            assert_eq!(tool_call_id, "tc-2");
            assert!(
                reason.contains("rate exhausted"),
                "names the rate leg: {reason}"
            );
        }
        other => panic!("expected an in-band Reject, got {other:?}"),
    }
    // The refusal did NOT advance the counter.
    assert_eq!(gw.calls_made(ToolKind::Execute), 1);
}

#[test]
fn past_deadline_tool_call_refused_in_band() {
    // CHEAT ✗ — a call presented after the session mandate deadline (now 2000 >
    // 1000) is refused in-band, even in-scope with rate head-room.
    let (runtime, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000);
    let mut gw = HermesGateway::new(&runtime, root, registry);

    let call = ToolCallRequest::new("s1", "tc-1", "read_file", args());
    let outcome = gw.admit_with_work(&call, 2000, Some(vec![]));
    match outcome {
        PermissionOutcome::Reject { reason, .. } => {
            assert!(
                reason.contains("past deadline"),
                "names the deadline leg: {reason}"
            );
        }
        other => panic!("expected an in-band Reject, got {other:?}"),
    }
    assert_eq!(gw.calls_made(ToolKind::Read), 0);
}

#[test]
fn each_kind_gets_an_independent_metered_mandate() {
    // The kinds are independently confined: a Fetch call and an Edit call land
    // on different cap-gated workers under different grants, each metering its
    // own counter. (deos can deny one class entirely without touching another.)
    let (runtime, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000);
    let mut gw = HermesGateway::new(&runtime, root, registry);

    assert!(
        gw.admit_with_work(
            &ToolCallRequest::new("s1", "f1", "web_search", args()),
            50,
            Some(vec![])
        )
        .allowed()
    );
    assert!(
        gw.admit_with_work(
            &ToolCallRequest::new("s1", "e1", "write_file", args()),
            50,
            Some(vec![])
        )
        .allowed()
    );

    assert_eq!(gw.calls_made(ToolKind::Fetch), 1);
    assert_eq!(gw.calls_made(ToolKind::Edit), 1);
    assert_eq!(
        gw.calls_made(ToolKind::Execute),
        0,
        "untouched class stays at 0"
    );
}
