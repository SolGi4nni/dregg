//! RED-TEAM 6 — SANDBOX ESCAPE. From inside the confined firmament host-PD, the
//! agent body attempts AMBIENT OS authority — open a file outside its grant, dial
//! the network, hold an extra fd. Every attempt must be DENIED (fail-closed); the
//! agent's only channel is its firmament Endpoint.
//!
//! This drives the REAL confined launch (`spawn_hermes_in_pd` →
//! `spawn_pd_confined`: macOS Seatbelt / Linux ns+seccomp+landlock applied after
//! fork, before the body) and asserts the four confinement teeth via the child's
//! probe-verdict exit code. A tooth that did NOT hold is a genuine escape hole.
//!
//! This complements `tests/confined_launch.rs` (which also asserts the ACP
//! round-trip): here the focus is purely the ESCAPE teeth, each asserted
//! individually so a single failing tooth is named.

#![cfg(unix)]

use std::sync::{Arc, RwLock};

use deos_hermes::confined::{probe, spawn_hermes_in_pd};
use deos_hermes::{GrantRegistry, HermesGateway, ScriptedCall};
use dregg_firmament::process_kernel::ProcessKernel;
use dregg_sdk::{AgentCipherclerk, AgentRuntime};

#[test]
fn a_confined_agent_cannot_open_files_dial_the_network_or_hold_extra_fds() {
    // The grantor side (irrelevant to the escape teeth, but needed to drive ACP).
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    let registry = GrantRegistry::default_for_session(10_000).with_standard_tool_grants(10_000);
    let gateway = HermesGateway::new(&rt, root, registry);

    // A scripted turn so the child runs a real ACP session (and the probes).
    let script = vec![ScriptedCall::new("web_search", serde_json::json!({"query": "escape?"}))];

    let kernel = ProcessKernel::new();
    let agent = spawn_hermes_in_pd(&kernel, "sess-escape", script, None, None)
        .expect("fork the confined PD");

    // Drive the session so the child completes and exits with its probe verdict.
    let transport = agent.transport().expect("Endpoint transport");
    let mut client = deos_hermes::AcpClient::new(transport, gateway, 10);
    let _ = client.run_prompt("/sandboxed/cwd", "attempt escape");

    let verdict = agent.join_verdict().expect("reap the confined child");

    // ── ESCAPE TOOTH 1: ambient FILE open denied (open(/etc/passwd) failed). ──
    assert_eq!(
        verdict & probe::OPEN_DENIED,
        probe::OPEN_DENIED,
        "SANDBOX ESCAPE — the confined agent OPENED /etc/passwd (ambient file authority leaked); verdict={verdict:#x}"
    );

    // ── ESCAPE TOOTH 2: ambient NETWORK dial denied (socket/connect blocked). ──
    assert_eq!(
        verdict & probe::NET_DENIED,
        probe::NET_DENIED,
        "SANDBOX ESCAPE — the confined agent reached the NETWORK (ambient net authority leaked); verdict={verdict:#x}"
    );

    // ── ESCAPE TOOTH 3: exactly ONE non-std fd (the Endpoint) — no leaked fds. ──
    assert_eq!(
        verdict & probe::ONLY_ENDPOINT_FD,
        probe::ONLY_ENDPOINT_FD,
        "SANDBOX ESCAPE — the confined agent held an fd beyond its Endpoint (ambient fd leaked); verdict={verdict:#x}"
    );

    // The Endpoint channel itself works (the confinement is not just a dead process).
    assert_eq!(
        verdict & probe::IPC_WORKS,
        probe::IPC_WORKS,
        "the agent's ONLY channel (the firmament Endpoint) is live — confinement, not death; verdict={verdict:#x}"
    );

    assert_eq!(
        verdict,
        probe::ALL,
        "ALL FOUR confinement teeth held: file/net/exec ambient authority denied, one fd, Endpoint live. verdict={verdict:#x}"
    );
}
