//! `deos-hermes` — a CLI demonstration of the seam: a Hermes-style tool-call
//! becomes a cap-gated, metered, receipted dregg turn (or an in-band refusal).
//!
//! This drives a MOCKED ACP source (a handful of representative Hermes
//! tool-calls) through the real [`HermesGateway`] over a live verified-executor
//! runtime. It prints, per call, the deos verdict deos would send back to
//! Hermes over ACP: ALLOW + the dregg receipt id (+ remaining budget) or
//! REJECT + the leg that bit.
//!
//! Run: `cd deos-hermes && cargo run`

use std::sync::{Arc, RwLock};

use deos_hermes::{GrantRegistry, HermesGateway, PermissionOutcome, ToolCallRequest, ToolKind};
use dregg_sdk::{AgentCipherclerk, AgentRuntime};

fn main() {
    // The grantor: deos's runtime over the verified executor, holding a root
    // token it delegates each tool-class worker's mandate from.
    let mut cclerk = AgentCipherclerk::new();
    let root_key = [7u8; 32];
    let root_token = cclerk.mint_token(&root_key, "deos");
    let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");

    // deos's confinement: the standard per-kind mandate, deadline (clock) 1000.
    // We tighten Execute to rate 2 to show a rate exhaustion live.
    let registry = GrantRegistry::default_for_session(1000).with_grant(
        ToolKind::Execute,
        dregg_sdk::ToolGrant {
            tool_id: 40,
            rate_limit: 2,
            deadline: 1000,
            tool_method: "tool.execute".to_string(),
        },
    );

    let mut gw = HermesGateway::new(&runtime, root_token, registry);

    println!("deos-hermes seam demo — every Hermes tool-call → a cap-gated receipted dregg turn\n");

    // A mocked ACP source: representative Hermes tool-calls (the kind of
    // `tool_call` payload `acp_adapter` emits on `session/request_permission`).
    let session = "sess-demo";
    let calls = vec![
        ToolCallRequest::new(session, "tc-1", "web_search", json_args(r#"{"query":"dregg"}"#)),
        ToolCallRequest::new(session, "tc-2", "read_file", json_args(r#"{"path":"src/lib.rs"}"#)),
        ToolCallRequest::new(session, "tc-3", "terminal", json_args(r#"{"command":"cargo build"}"#)),
        ToolCallRequest::new(session, "tc-4", "terminal", json_args(r#"{"command":"cargo test"}"#)),
        // The 3rd Execute call: over the rate-2 Execute mandate -> refused.
        ToolCallRequest::new(session, "tc-5", "terminal", json_args(r#"{"command":"rm -rf /"}"#)),
        // A past-deadline call (now 2000 > mandate deadline 1000) -> refused.
        ToolCallRequest::new(session, "tc-6", "read_file", json_args(r#"{"path":"late"}"#)),
    ];

    for call in &calls {
        // `now` = the ACP request arrival clock; tc-6 arrives "late" (2000).
        let now = if call.tool_call_id == "tc-6" { 2000 } else { 50 };
        // No tool payload here (a pure metered admission): the metering IS the
        // receipted proof the call was authorized.
        let outcome = gw.admit_call(call, now, vec![]);
        print_outcome(call, &outcome);
    }

    println!();
    println!(
        "Execute calls made: {} (mandate rate 2)",
        gw.calls_made(ToolKind::Execute)
    );
    println!(
        "Fetch calls made: {} | Read calls made: {}",
        gw.calls_made(ToolKind::Fetch),
        gw.calls_made(ToolKind::Read),
    );
}

fn json_args(s: &str) -> serde_json::Value {
    serde_json::from_str(s).unwrap_or(serde_json::Value::Null)
}

fn print_outcome(call: &ToolCallRequest, outcome: &PermissionOutcome) {
    match outcome {
        PermissionOutcome::Allow {
            receipt, remaining, ..
        } => {
            println!(
                "  ALLOW  {:<7} {:<12} ({:?})  -> receipt {}…  [{} left]",
                call.tool_call_id,
                call.name,
                call.kind,
                &receipt[..16.min(receipt.len())],
                remaining,
            );
        }
        PermissionOutcome::Reject { reason, .. } => {
            println!(
                "  REJECT {:<7} {:<12} ({:?})  -> {}",
                call.tool_call_id, call.name, call.kind, reason,
            );
        }
    }
}
