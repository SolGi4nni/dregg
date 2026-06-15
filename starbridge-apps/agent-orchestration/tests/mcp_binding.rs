//! # Live MCP tool-call binding — an agent loop's tool invocation IS a verified worker step.
//!
//! The seam the record names made executable: the MCP `tools/call` an LLM emits is run AS a verified
//! [`WorkStep`] through the real executor, so the receipt cryptographically binds the EXACT tool +
//! arguments, and a call OUTSIDE the worker's mandate is REFUSED in the fire path — the enforcement the
//! four integrators all punted on, at the exact seam.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, EmbeddedExecutor,
};
use dregg_cell::FactoryCreationParams;
use starbridge_agent_orchestration::{
    Mandate, ORCHESTRATION_FACTORY_VK, OrchestrationEngine, OrchestrationError, OrchestrationLog,
    Tool, WorkerSlot, audit_run, coordinator_child_program_vk,
    mcp::{McpStepError, McpToolCall, step_from_mcp_call, tool_for_mcp_name},
    orchestration_factory_descriptor,
};

fn born_board(cclerk: &AppCipherclerk, exec: &EmbeddedExecutor, seed: &[u8]) -> CellId {
    exec.deploy_factory(orchestration_factory_descriptor());
    let agent = cclerk.cell_id();
    exec.with_ledger_mut(|l| {
        if let Some(c) = l.get_mut(&agent) {
            c.state.set_balance(100_000_000);
        }
    });
    let owner = cclerk.public_key().0;
    let token = *blake3::hash(seed).as_bytes();
    let params = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(coordinator_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(ORCHESTRATION_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth).expect("board birth commits");
    let board = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|l| {
        if let Some(a) = l.get_mut(&agent) {
            a.capabilities.grant(board, AuthRequired::Signature);
        }
    });
    board
}

/// Coordinator holds read+search+summarize+write; worker-A is a researcher (read+search+summarize, no
/// write/spend); worker-B reads only.
fn mandates() -> (Mandate, Mandate, Mandate) {
    let c = Mandate::coordinator(
        [Tool::Read, Tool::Search, Tool::Summarize, Tool::Write],
        1000,
        "task",
    );
    let a = c.attenuate([Tool::Read, Tool::Search, Tool::Summarize], 700, "research");
    let b = c.attenuate([Tool::Read], 300, "fact-check");
    (c, a, b)
}

#[test]
fn an_mcp_tool_call_runs_as_a_verified_worker_step() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x81u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = born_board(&cclerk, &exec, b"mcp-ok");
    let (coord, a, b) = mandates();

    let mut log = OrchestrationLog::new();
    let mut engine =
        OrchestrationEngine::new(&cclerk, &exec, board, coord.clone(), a.clone(), b.clone());
    engine.open("lead").expect("opens");

    // worker-A's LLM emits an MCP `search` call — it maps to Tool::Search (in A's mandate) and runs
    // as a verified step. The receipt binds the call's content-address.
    let call = McpToolCall::new("search", serde_json::json!({"query": "dregg provenance"}));
    let receipt = step_from_mcp_call(&mut engine, WorkerSlot::A, &call, &mut log)
        .expect("an in-mandate MCP search runs as a verified step");
    assert_ne!(receipt.receipt_hash(), [0u8; 32]);
    assert_eq!(log.len(), 1);
    // The committed step's sub-task binds the exact MCP call (name + arguments digest).
    let logged = &log.entries[0];
    assert_eq!(logged.step.tool, Tool::Search);
    assert!(
        logged.step.sub_task.starts_with("mcp/search/"),
        "the step binds the MCP call's content-address: {}",
        logged.step.sub_task
    );
    assert!(
        logged.step.sub_task.ends_with(&call.digest_hex()),
        "the bound digest is the call's content-address"
    );
}

#[test]
fn an_mcp_call_for_a_tool_outside_the_mandate_is_refused_in_the_fire_path() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x82u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = born_board(&cclerk, &exec, b"mcp-overmandate");
    let (coord, a, b) = mandates();

    let mut log = OrchestrationLog::new();
    let mut engine = OrchestrationEngine::new(&cclerk, &exec, board, coord, a, b);
    engine.open("lead").expect("opens");

    // worker-B (read only) emits an MCP `write_file` call — Tool::Write is NOT in B's mandate. The
    // call is REFUSED in the fire path (before any effect), and nothing is logged.
    let call = McpToolCall::new(
        "write_file",
        serde_json::json!({"path": "/etc/passwd", "data": "x"}),
    );
    let err = step_from_mcp_call(&mut engine, WorkerSlot::B, &call, &mut log)
        .expect_err("an out-of-mandate MCP call must be refused");
    assert!(
        matches!(
            err,
            McpStepError::Refused(OrchestrationError::OutOfMandate {
                worker: WorkerSlot::B,
                tool: Tool::Write,
                ..
            })
        ),
        "expected OutOfMandate(write) in the fire path, got {err:?}"
    );
    assert!(
        log.is_empty(),
        "a refused MCP call commits nothing (fail-closed)"
    );
}

#[test]
fn an_unknown_mcp_tool_is_refused_fail_closed() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x83u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = born_board(&cclerk, &exec, b"mcp-unknown");
    let (coord, a, b) = mandates();

    let mut log = OrchestrationLog::new();
    let mut engine = OrchestrationEngine::new(&cclerk, &exec, board, coord, a, b);
    engine.open("lead").expect("opens");

    // A tool the policy does not classify is REFUSED (fail-closed) — it never reaches the executor.
    let call = McpToolCall::new("exfiltrate_secrets", serde_json::json!({}));
    let err = step_from_mcp_call(&mut engine, WorkerSlot::A, &call, &mut log)
        .expect_err("an unclassified MCP tool must be refused");
    assert!(
        matches!(err, McpStepError::UnknownTool(ref n) if n == "exfiltrate_secrets"),
        "expected UnknownTool, got {err:?}"
    );
    assert!(log.is_empty());
    assert!(tool_for_mcp_name("exfiltrate_secrets").is_none());
}

#[test]
fn a_run_of_mcp_calls_audits_clean_binding_each_tool() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x84u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = born_board(&cclerk, &exec, b"mcp-audit");
    let (coord, a, b) = mandates();

    let mut log = OrchestrationLog::new();
    let open_receipt;
    {
        let mut engine =
            OrchestrationEngine::new(&cclerk, &exec, board, coord.clone(), a.clone(), b.clone());
        engine.open("lead").expect("opens");
        open_receipt = engine.open_receipt().cloned().unwrap();
        // A worker loop drives three real MCP calls; each runs as a verified step.
        for (worker, call) in [
            (
                WorkerSlot::A,
                McpToolCall::new("web_search", serde_json::json!({"q": "x"})),
            ),
            (
                WorkerSlot::A,
                McpToolCall::new("summarize", serde_json::json!({"doc": "y"})),
            ),
            (
                WorkerSlot::B,
                McpToolCall::new("fetch", serde_json::json!({"url": "z"})),
            ),
        ] {
            step_from_mcp_call(&mut engine, worker, &call, &mut log)
                .unwrap_or_else(|e| panic!("MCP call should run: {e}"));
        }
    }
    assert_eq!(log.len(), 3);
    // The auditor proves no agent exceeded its mandate — every step a classified, in-scope tool call.
    let ok = audit_run(&open_receipt, &log, &coord, &a, &b).expect("the MCP run audits clean");
    assert_eq!(ok.steps, 3);
    // worker-A ran web_search (100) + summarize (150) = 250; worker-B ran fetch (50).
    assert_eq!(ok.spent_a, 250);
    assert_eq!(ok.spent_b, 50);
}
