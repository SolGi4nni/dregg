//! RED-TEAM 1 — MANDATE OVERRUN. A confined agent tries to exceed its mandate
//! on each of the three confinement legs (SCOPE, DEADLINE, RATE), including at
//! the exact boundary. Every overrun must be REFUSED in-band with NO turn and NO
//! spend.
//!
//! These are adversarial: each test ATTEMPTS the escalation through the real
//! [`HermesGateway`] over the verified executor and asserts the refusal. A pass
//! means the limit HOLDS (the mechanism that stopped it is named in-band); a
//! failure here would be a genuine hole.
//!
//! Mechanism under attack: `delegAdmit g now tool old new = SCOPE ∧ DEADLINE ∧
//! (new = old+1 ∧ 0 ≤ old ∧ new ≤ rateLimit)` (the Lean-mirrored `deleg_admit`
//! in `sdk/src/tool_gateway.rs`), folded in-band before any turn is submitted.

use std::sync::{Arc, RwLock};

use deos_hermes::{GrantRegistry, HermesGateway, PermissionOutcome, ToolCallRequest, ToolKind};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken, ToolGrant};

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

fn args() -> serde_json::Value {
    serde_json::json!({"query": "x", "command": "ls", "path": "p", "content": "c"})
}

// ───────────────────────────── RATE — exact boundary ─────────────────────────

#[test]
fn rate_ceiling_holds_exactly_at_the_boundary_and_one_past() {
    // Confine Execute to rate EXACTLY 3. Three terminal calls must commit (the
    // boundary is inclusive: new ≤ rateLimit), the FOURTH must be refused in-band.
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(10_000).with_grant(
        ToolKind::Execute,
        ToolGrant {
            tool_id: 40,
            rate_limit: 3,
            deadline: 10_000,
            tool_method: "tool.execute".to_string(),
        },
    );
    let mut gw = HermesGateway::new(&rt, root, registry);

    // EXACTLY-AT-RATE: calls 1,2,3 commit (new = 1,2,3 ≤ 3).
    for i in 1..=3 {
        let call = ToolCallRequest::new("s", format!("tc-{i}"), "terminal", args());
        let outcome = gw.admit_with_work(&call, 50, Some(vec![]));
        assert!(
            outcome.allowed(),
            "call {i} is exactly at/under the rate-3 ceiling and must commit, got {outcome:?}"
        );
    }
    assert_eq!(gw.calls_made(ToolKind::Execute), 3, "three committed");

    // ONE-PAST: the 4th call (new = 4 > 3) is refused IN-BAND on the rate leg.
    let over = ToolCallRequest::new("s", "tc-4", "terminal", args());
    match gw.admit_with_work(&over, 50, Some(vec![])) {
        PermissionOutcome::Reject { reason, .. } => {
            assert!(reason.contains("rate exhausted"), "names the RATE leg: {reason}");
        }
        other => panic!("RATE OVERRUN ESCALATED — expected an in-band Reject, got {other:?}"),
    }
    // The refused overrun did NOT advance the counter (no spend, no turn).
    assert_eq!(
        gw.calls_made(ToolKind::Execute),
        3,
        "the refused 4th call left the meter at 3 — no ghost spend"
    );
}

#[test]
fn rate_zero_denies_a_tool_entirely_on_the_first_attempt() {
    // deos can confine a tool to rate 0 (the whole-tool deny). The FIRST reach for
    // it fails closed (new = 1 > 0). This is the `with_grant_for_tool_deny` face.
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(10_000).with_grant_for_tool_deny("terminal");
    let mut gw = HermesGateway::new(&rt, root, registry);

    let call = ToolCallRequest::new("s", "tc-1", "terminal", args());
    match gw.admit_with_work(&call, 50, Some(vec![])) {
        PermissionOutcome::Reject { reason, .. } => {
            assert!(reason.contains("rate exhausted"), "rate-0 denies on first try: {reason}");
        }
        other => panic!("RATE-0 DENY ESCALATED — terminal was denied entirely, got {other:?}"),
    }
    assert_eq!(gw.calls_made_for_tool("terminal"), 0, "no spend on a rate-0 tool");
}

// ───────────────────────────── DEADLINE — exact boundary ─────────────────────

#[test]
fn deadline_holds_exactly_at_the_boundary_and_one_past() {
    // Deadline EXACTLY 1000. now == 1000 admits (the predicate is `now ≤ deadline`);
    // now == 1001 is refused in-band on the deadline leg.
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000);
    let mut gw = HermesGateway::new(&rt, root, registry);

    // EXACTLY-AT-DEADLINE (now == deadline): admitted.
    let at = ToolCallRequest::new("s", "tc-1", "read_file", args());
    assert!(
        gw.admit_with_work(&at, 1000, Some(vec![])).allowed(),
        "now == deadline (1000) is in-time (now ≤ deadline) and must commit"
    );

    // ONE-PAST-DEADLINE (now == deadline + 1): refused in-band.
    let past = ToolCallRequest::new("s", "tc-2", "read_file", args());
    match gw.admit_with_work(&past, 1001, Some(vec![])) {
        PermissionOutcome::Reject { reason, .. } => {
            assert!(reason.contains("past deadline"), "names the DEADLINE leg: {reason}");
        }
        other => panic!("DEADLINE OVERRUN ESCALATED — expected in-band Reject, got {other:?}"),
    }
    // The clock-past refusal spent nothing.
    assert_eq!(gw.calls_made(ToolKind::Read), 1, "only the in-time call committed");
}

// ───────────────────────────── SCOPE — wrong worker / unknown tool ───────────

#[test]
fn an_unknown_tool_falls_closed_into_the_most_restricted_class() {
    // An UNKNOWN tool name the agent invents is not free authority: it classifies
    // to `Other` (rate 10, the most-restricted floor), never an unbounded path.
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(10_000);
    let mut gw = HermesGateway::new(&rt, root, registry);

    let bogus = ToolCallRequest::new("s", "tc-1", "totally_made_up_superpower", args());
    assert_eq!(bogus.kind, ToolKind::Other, "unknown tool fails closed into Other");

    // It is admitted under Other's TIGHT floor (rate 10), and metered there — not
    // an escape. Exhaust the Other-10 budget and confirm it then refuses.
    for i in 0..10 {
        let c = ToolCallRequest::new("s", format!("o-{i}"), "totally_made_up_superpower", args());
        assert!(gw.admit_with_work(&c, 50, Some(vec![])).allowed(), "Other call {i} within rate-10");
    }
    let over = ToolCallRequest::new("s", "o-11", "totally_made_up_superpower", args());
    match gw.admit_with_work(&over, 50, Some(vec![])) {
        PermissionOutcome::Reject { reason, .. } => {
            assert!(reason.contains("rate exhausted"), "Other floor is metered, not unbounded: {reason}");
        }
        other => panic!("UNKNOWN-TOOL ESCALATED past the Other floor, got {other:?}"),
    }
}

#[test]
fn scope_is_per_worker_an_overrun_on_one_kind_does_not_leak_budget_to_another() {
    // Confine Execute to rate 1, leave Fetch generous. Exhaust Execute; the agent
    // cannot then borrow Fetch's budget for a terminal call — the workers are
    // independent cap-gated cells. (Cross-mandate amplification is impossible.)
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(10_000).with_grant(
        ToolKind::Execute,
        ToolGrant { tool_id: 40, rate_limit: 1, deadline: 10_000, tool_method: "tool.execute".into() },
    );
    let mut gw = HermesGateway::new(&rt, root, registry);

    assert!(gw.admit_with_work(&ToolCallRequest::new("s", "x1", "terminal", args()), 50, Some(vec![])).allowed());
    // Execute is now exhausted: the next terminal is refused, regardless of how
    // much Fetch budget exists.
    match gw.admit_with_work(&ToolCallRequest::new("s", "x2", "terminal", args()), 50, Some(vec![])) {
        PermissionOutcome::Reject { reason, .. } => assert!(reason.contains("rate exhausted"), "{reason}"),
        other => panic!("CROSS-MANDATE AMPLIFICATION — terminal borrowed budget, got {other:?}"),
    }
    // Fetch is untouched and still works (proving the budgets are genuinely separate).
    assert!(gw.admit_with_work(&ToolCallRequest::new("s", "f1", "web_search", args()), 50, Some(vec![])).allowed());
    assert_eq!(gw.calls_made(ToolKind::Execute), 1);
    assert_eq!(gw.calls_made(ToolKind::Fetch), 1);
}
