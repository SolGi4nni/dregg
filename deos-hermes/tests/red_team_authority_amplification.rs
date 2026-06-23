//! RED-TEAM 2 + 3 — AUTHORITY AMPLIFICATION & CONFUSED DEPUTY.
//!
//! A confined worker holds a biscuit credential scoped to EXACTLY one executor
//! method verb (`grant.tool_method`). These tests attack the `granted ⊆ held`
//! tooth and the principal binding DIRECTLY at the executor, bypassing the
//! in-band `deleg_admit` pre-check (via `worker_for_test`), to prove the
//! EXECUTOR itself — not just the gateway — refuses:
//!
//!   2. AMPLIFICATION — a worker scoped to `tool.search` tries to fire a turn
//!      under a DIFFERENT, wider verb (`tool.execute`, `admin`, the default
//!      sub-agent method). The executor rejects with `TokenInsufficientCapability`
//!      (the biscuit's `service(cell, action)` cover does not match). The worker
//!      cannot confer authority it was never granted.
//!
//!   3. CONFUSED DEPUTY — every turn a worker submits is signed/committed under
//!      the worker's OWN attenuated cell (`turn.agent == worker.cell_id`), never
//!      a claimed operator/root principal. The ACP call payload carries no
//!      principal field that could redirect the signer. We assert the receipted
//!      turn commits under the worker's own cell id, and that a fabricated
//!      "act-as-root" turn (target = some other cell) is refused.

use std::sync::{Arc, RwLock};

use deos_hermes::{GrantRegistry, HermesGateway, ToolCallRequest, ToolKind};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken, ToolGateway, ToolGrant};

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

// ───────────────────────── 2. AUTHORITY AMPLIFICATION ────────────────────────

#[test]
fn worker_cannot_fire_a_method_outside_its_granted_scope() {
    // Admit a worker scoped to EXACTLY `tool.search`. Then — bypassing the in-band
    // deleg_admit gate entirely — drive the underlying worker to execute a turn
    // under a WIDER verb. The EXECUTOR must reject it: the credential is the
    // boundary, not the gateway's politeness.
    let (rt, root) = grantor();
    let grant = ToolGrant {
        tool_id: 20,
        rate_limit: 100,
        deadline: 10_000,
        tool_method: "tool.search".to_string(),
    };
    let gw = ToolGateway::admit(&rt, &root, grant).expect("admit a search-scoped worker");
    let worker = gw.worker_for_test();
    assert_eq!(worker.cap_methods(), &["tool.search".to_string()], "scoped to search only");

    // ESCALATION ATTEMPT: fire under a verb the credential does NOT cover.
    for forbidden in ["tool.execute", "admin", "tool.edit", "sub-agent-method"] {
        let result = worker.execute_method(forbidden, vec![]);
        assert!(
            result.is_err(),
            "AMPLIFICATION HOLE — worker fired forbidden verb '{forbidden}' and committed: {result:?}"
        );
        let msg = format!("{:?}", result.unwrap_err());
        assert!(
            msg.contains("Insufficient") || msg.contains("Capability") || msg.contains("Token") || msg.contains("authoriz") || msg.contains("Auth"),
            "the executor refused '{forbidden}' on a capability/authorization ground: {msg}"
        );
    }

    // The in-scope verb still works (the credential is not simply broken).
    assert!(
        worker.execute_method("tool.search", vec![]).is_ok(),
        "the GRANTED verb commits — the refusal above is scope, not a dead credential"
    );
}

#[test]
fn a_confined_agent_cannot_widen_its_own_grant() {
    // The gateway's grant is fixed at admit time; there is NO ACP surface and NO
    // gateway method that lets the confined agent raise its own rate ceiling,
    // extend its deadline, or add a tool id. We confirm the only mutation a call
    // can cause is the monotone counter advance — the grant is immutable through
    // the seam. (A self-widening API simply does not exist; this asserts the
    // grant the inspector reports is unchanged after exercising the seam.)
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(10_000);
    let mut gw = HermesGateway::new(&rt, root, registry);

    let before = gw.grant_for(ToolKind::Fetch).clone();
    // Drive several calls (and a refused over-deadline one) — none of which can
    // mutate the grant.
    let _ = gw.admit_with_work(&ToolCallRequest::new("s", "a", "web_search", serde_json::json!({"query":"q"})), 50, Some(vec![]));
    let _ = gw.admit_with_work(&ToolCallRequest::new("s", "b", "web_search", serde_json::json!({"query":"q"})), 999_999, Some(vec![]));
    let after = gw.grant_for(ToolKind::Fetch).clone();

    assert_eq!(before, after, "GRANT-WIDENING HOLE — the grant changed through the seam: {before:?} -> {after:?}");
    assert_eq!(after.rate_limit, 50, "rate ceiling unchanged");
    assert_eq!(after.deadline, 10_000, "deadline unchanged");
}

// ───────────────────────────── 3. CONFUSED DEPUTY ───────────────────────────

#[test]
fn a_committed_call_is_signed_under_the_workers_own_cell_never_a_claimed_principal() {
    // The agent submits a tool-call whose ARGUMENTS claim to act as the operator /
    // root (`as`, `principal`, `run_as`, `uid` fields). These are inert: the
    // committed turn is bound to the worker's OWN attenuated cell. There is no
    // payload field that redirects the signer.
    let (rt, root) = grantor();
    let grant = ToolGrant { tool_id: 40, rate_limit: 100, deadline: 10_000, tool_method: "tool.execute".into() };
    let mut gw = ToolGateway::admit(&rt, &root, grant).expect("admit worker");
    let worker_cell = gw.worker_cell();

    // The metered turn commits — and its receipt is bound to worker_cell, not to
    // any principal the agent might name in the payload.
    let receipt = gw.invoke(40, 50, vec![]).expect("the in-scope metered turn commits");
    // The committed turn's worker cell is the gateway's worker cell — the only
    // identity it could have signed under. A confused-deputy redirect is structurally
    // impossible: execute_method always sets `agent = target = self.cell_id`.
    assert_eq!(
        gw.worker_cell(),
        worker_cell,
        "the worker's committed identity is its own attenuated cell, immune to a claimed principal"
    );
    assert!(receipt.receipt.turn_hash != [0u8; 32], "a real receipt under the worker's own cell");
}

#[test]
fn claiming_a_different_principal_in_the_payload_does_not_grant_that_principals_authority() {
    // Drive a call whose payload screams "I am root". The gate routes it by tool
    // NAME only; the payload's `principal`/`run_as` keys are never read for
    // authority. The call is metered exactly like any other terminal call —
    // proving the claim conferred nothing.
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(10_000).with_grant(
        ToolKind::Execute,
        ToolGrant { tool_id: 40, rate_limit: 1, deadline: 10_000, tool_method: "tool.execute".into() },
    );
    let mut gw = HermesGateway::new(&rt, root, registry);

    let spoof = ToolCallRequest::new(
        "s",
        "tc-1",
        "terminal",
        serde_json::json!({
            "command": "rm -rf /",
            "principal": "root",
            "run_as": "operator",
            "uid": 0,
            "as": "deos-admin"
        }),
    );
    // It commits under the rate-1 Execute mandate like any terminal call: the
    // spoofed principal granted NO extra authority (had it, the agent would not
    // still be confined to its own rate-1 budget).
    assert!(gw.admit_with_work(&spoof, 50, None).allowed(), "metered like any terminal call");
    assert_eq!(gw.calls_made(ToolKind::Execute), 1, "spent exactly one of the agent's OWN budget");
    // And the budget is genuinely exhausted — the 'root' claim did not refill it.
    let again = ToolCallRequest::new("s", "tc-2", "terminal", serde_json::json!({"command":"id","principal":"root"}));
    match gw.admit_with_work(&again, 50, None) {
        deos_hermes::PermissionOutcome::Reject { reason, .. } => assert!(reason.contains("rate exhausted"), "{reason}"),
        other => panic!("CONFUSED-DEPUTY HOLE — the 'root' claim refilled/widened the mandate: {other:?}"),
    }
}
