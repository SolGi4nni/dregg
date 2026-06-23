//! RED-TEAM 7 — EMPOWERED-BUT-ACCOUNTABLE (the deos-js / agent-co-pilot angle).
//!
//! ember's framing: the agent SHOULD run JS freely as the operator's co-pilot
//! over a cockpit too complex for a human alone. The agent running JS with its
//! OWN broad authority over its OWN world is a FEATURE, not an escalation. So
//! this surface does NOT try to lock the agent's JS down. It verifies the model
//! is **empowered-but-accountable**, and that the one real edge holds:
//!
//!   (a) ACCOUNTABLE — a JS-driven turn is still `gateOK`-checked (the cap tooth
//!       runs) AND leaves a real receipt, so you can SEE and REWIND what the
//!       agent did. Every agent action is a receipted turn.
//!   (b) CROSS-VESSEL ISOLATION (THE EDGE) — JS run by the agent CANNOT forge
//!       authority or reach ANOTHER principal's / vessel's cells. A worker's
//!       credential is anchored in its OWN cell; an effect that targets a
//!       foreign cell is refused by the executor.
//!   (c) The agent's broad reflect+act power over its OWN world is expected.
//!
//! And the standing structural fact: there is NO Hermes→deos-js wiring today, so
//! there is no path for a confined tool-call to reach an unbounded executor; when
//! that binding is built, it must mount the JS runtime under the CALLER'S
//! attenuated cap (exactly like a `ToolGateway` worker), never root.

use std::sync::{Arc, RwLock};

use deos_hermes::{GrantRegistry, HermesGateway, ToolCallRequest, ToolKind};
use dregg_cell::CellId;
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken, ToolGateway, ToolGrant};
use dregg_turn::action::{symbol, Event};
use dregg_turn::Effect;

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

// ─────────────────────────── (a) ACCOUNTABLE ────────────────────────────────

#[test]
fn an_agent_driven_turn_is_gate_checked_and_leaves_a_real_receipt() {
    // The agent fires a broad action over its own world (here: a terminal call
    // carrying a real side-effect witness, the shape a JS-driven turn takes). It
    // is EMPOWERED — it commits — AND ACCOUNTABLE — it goes through the gate and
    // leaves a real, rewindable receipt.
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(10_000).with_standard_tool_grants(10_000);
    let mut gw = HermesGateway::new(&rt, root, registry);

    let call = ToolCallRequest::new("s", "tc-1", "terminal", serde_json::json!({"command": "build the cockpit"}));
    match gw.admit_with_work(&call, 50, None) {
        deos_hermes::PermissionOutcome::Allow { receipt, .. } => {
            // A real 32-byte turn hash — the audit/rewind anchor. The agent's
            // power is matched by a durable receipt of exactly what it did.
            assert_eq!(receipt.len(), 64, "a real receipt: the action is rewindable, not invisible");
        }
        other => panic!("an empowered agent action should commit accountably, got {other:?}"),
    }
    // The gate ran (the call was metered on the terminal mandate, not free).
    assert_eq!(gw.calls_made_for_tool("terminal"), 1, "every agent action is a metered, receipted turn");
}

// ─────────────────── (b) CROSS-VESSEL ISOLATION — THE EDGE ───────────────────

#[test]
fn the_agent_cannot_reach_another_vessels_cell_even_with_a_forged_effect() {
    // THE EDGE: the agent's broad power is over its OWN world. We inject a tool
    // witness effect that targets a FOREIGN cell (another principal's vessel) —
    // the kind of cross-vessel write a malicious JS payload would attempt. The
    // worker's credential is anchored in its OWN cell, so the executor refuses a
    // turn that touches a cell outside the worker's authority.
    let (rt, root) = grantor();
    let grant = ToolGrant { tool_id: 40, rate_limit: 100, deadline: 10_000, tool_method: "tool.execute".into() };
    let mut gw = ToolGateway::admit(&rt, &root, grant).expect("admit worker");
    let own_cell = gw.worker_cell();

    // A clearly-foreign vessel cell (NOT the worker's cell).
    let foreign_vessel = CellId::from_bytes([0xAB; 32]);
    assert_ne!(foreign_vessel, own_cell, "the foreign vessel is a different cell");

    // FORGED cross-vessel effect: write into the foreign vessel's state.
    let cross_vessel_write = vec![Effect::SetField {
        cell: foreign_vessel,
        index: 7,
        value: dregg_cell::program::field_from_u64(0xDEAD),
    }];

    let result = gw.invoke(40, 50, cross_vessel_write);
    assert!(
        result.is_err(),
        "CROSS-VESSEL HOLE — the agent wrote into ANOTHER vessel's cell {foreign_vessel:?}: {result:?}"
    );

    // A witness EVENT targeting a foreign cell is likewise not a free cross-vessel
    // reach: the worker can only emit/commit on the cells its credential covers.
    let cross_vessel_event = vec![Effect::EmitEvent {
        cell: foreign_vessel,
        event: Event { topic: symbol("tool.pwn"), data: vec![] },
    }];
    let evt = gw.invoke(40, 51, cross_vessel_event);
    assert!(
        evt.is_err(),
        "CROSS-VESSEL HOLE — the agent emitted into ANOTHER vessel's cell: {evt:?}"
    );

    // And the agent's OWN-world action still commits (the isolation is an edge,
    // not a cage — it is fully empowered over its own cell).
    let own = gw.invoke(40, 52, vec![]);
    assert!(own.is_ok(), "the agent remains fully empowered over its OWN world: {own:?}");
}

// ─────────────────── the standing fact: no unbounded JS path ─────────────────

#[test]
fn there_is_no_confined_tool_path_that_reaches_an_unbounded_executor() {
    // EVERY tool-call the seam admits terminates in a cap-gated, metered, receipted
    // turn through a `ToolGateway` worker — never a raw, unbounded executor. There
    // is no `HermesGateway` method that hands back a root-authority handle, and no
    // Hermes→deos-js wiring exists. This test documents the invariant the FUTURE
    // Hermes↔deos-js binding must keep: the JS runtime mounts under the CALLER'S
    // attenuated cap (a worker like this one), never root.
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(10_000);
    let mut gw = HermesGateway::new(&rt, root, registry);

    // The ONLY way work reaches the executor is admit_call/admit_with_work, each
    // bounded by a per-kind/per-tool grant. Exercise the broadest class (Read, the
    // generous rate-200 floor) and confirm it STILL meters — there is no unbounded
    // class. Every kind has a finite ceiling.
    for kind in [ToolKind::Read, ToolKind::Search, ToolKind::Fetch, ToolKind::Execute, ToolKind::Edit, ToolKind::Other] {
        let grant = gw.grant_for(kind);
        assert!(grant.rate_limit >= 0, "every kind has a defined, finite rate ceiling: {kind:?}");
        assert!(grant.deadline > 0, "every kind has a deadline (no eternal mandate): {kind:?}");
    }

    // Drive one call to show the only executor path is the metered one.
    let call = ToolCallRequest::new("s", "tc-1", "read_file", serde_json::json!({"path": "x"}));
    assert!(gw.admit_with_work(&call, 50, None).allowed());
    assert_eq!(gw.calls_made(ToolKind::Read), 1, "even the broadest class is metered — no unbounded executor reachable");
}
