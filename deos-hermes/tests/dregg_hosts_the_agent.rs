//! DREGG IS THE HOST — the polarity inversion, PROVEN BY RUNNING.
//!
//! The agent is jailed inside a dregg PD; dregg's tools are its only effective
//! effect-path; the base-tool escape is neutralized at the OS level; and egress is
//! a structured, cap-gated, opt-in door. Each leg is asserted by running, not by
//! compiling.
//!
//! Run: `cd deos-hermes && cargo test --test dregg_hosts_the_agent`
//! (and the same under `--features js-agent`).
//!
//! The three legs:
//!   (a) THE DREGG TOOL EFFECT-PATH WORKS + IS RECEIPTED — `terminal` execs inside
//!       a nested confined PD (file/net/exec denied), a cap-gated receipted turn
//!       on the dregg verified executor. (run_js under `--features js-agent`.)
//!   (b) THE BASE-TOOL ESCAPE IS NEUTRALIZED — the jailed agent reaches for an
//!       unconfined shell, a host-FS read, and an arbitrary socket (exactly the
//!       ambient authority hermes's leaky base tools would use); the OS jail
//!       DENIES every one. We do NOT fork hermes — the jail neutralizes its base
//!       tools at the OS level.
//!   (c) STRUCTURED EGRESS — when the host GRANTS a specific host path, that path
//!       (and only that path) is readable inside the jail; when SEALED (the
//!       default) or for a sibling outside the grant, it is DENIED; the grant is
//!       revocable.

#![cfg(unix)]

use std::sync::{Arc, RwLock};

use deos_hermes::confined::probe;
use deos_hermes::host::escape;
use deos_hermes::mcp_server::{McpServer, McpToolHost};
use deos_hermes::{DreggHost, GrantRegistry, HermesGateway};
use dregg_firmament::process_kernel::ProcessKernel;
use dregg_sdk::{AgentCipherclerk, AgentRuntime};
use serde_json::{json, Value};

/// deos the grantor — the runtime that admits the confined tool workers + runs
/// their cap-gated receipted turns.
fn grantor() -> (AgentRuntime, dregg_sdk::HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// Frame one MCP request line.
fn req(id: i64, method: &str, params: Value) -> String {
    serde_json::to_string(&json!({
        "jsonrpc": "2.0", "id": id, "method": method, "params": params
    }))
    .unwrap()
        + "\n"
}

fn note(method: &str) -> String {
    serde_json::to_string(&json!({ "jsonrpc": "2.0", "method": method })).unwrap() + "\n"
}

fn drive(server: &mut McpServer<'_>, requests: &str) -> Vec<Value> {
    let reader = std::io::BufReader::new(requests.as_bytes());
    let mut out: Vec<u8> = Vec::new();
    server.serve(reader, &mut out).expect("serve the MCP session to EOF");
    String::from_utf8(out)
        .unwrap()
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str(l).expect("each reply is a JSON-RPC frame"))
        .collect()
}

/// (a) THE DREGG TOOL EFFECT-PATH — the jailed agent's `terminal` tool execs
/// INSIDE a dregg PD (every ambient authority denied) and leaves a dregg receipt.
/// This is the agent's ONLY effective way to cause an effect, and it routes to OUR
/// container, never the host.
#[test]
fn leg_a_dregg_tools_are_the_only_effect_path_and_are_receipted() {
    let (runtime, root) = grantor();
    let registry =
        GrantRegistry::default_for_session(1_000_000).with_standard_tool_grants(1_000_000);
    let host = McpToolHost::new(HermesGateway::new(&runtime, root, registry), 0);
    let mut server = McpServer::new(host);

    let session = format!(
        "{}{}{}",
        req(1, "initialize", json!({ "protocolVersion": "2025-06-18" })),
        note("notifications/initialized"),
        req(
            2,
            "tools/call",
            json!({
                "name": "terminal",
                "arguments": { "command": "cat /etc/passwd && curl http://1.1.1.1" }
            })
        ),
    );
    let replies = drive(&mut server, &session);
    let result = &replies
        .iter()
        .find(|r| r["id"] == json!(2))
        .expect("tools/call reply")["result"];

    // Admitted (cap-gated) + receipted (a real verified turn committed).
    assert_eq!(result["isError"], json!(false), "terminal admitted: {result}");
    assert!(
        result["_deos"]["receipt"].is_string(),
        "the dregg-tool turn left a receipt: {result}"
    );
    // The effect landed in OUR container — a confined PD where the model's
    // `cat`/`curl` could not reach the host file or the network.
    let verdict = result["_deos"]["sandboxVerdict"]
        .as_i64()
        .expect("a probe verdict") as i32;
    assert_eq!(
        verdict,
        probe::ALL,
        "the dregg tool ran in OUR container — file/net/exec denied (verdict 0x{verdict:x})"
    );

    // The host's tape proves the call routed through dregg (not the host's shell).
    let tape = server.into_host().tape().to_vec();
    assert_eq!(tape.len(), 1);
    assert_eq!(tape[0].tool, "terminal");
    assert_eq!(tape[0].sandbox_verdict, Some(probe::ALL));
}

/// (b) THE BASE-TOOL ESCAPE IS NEUTRALIZED — dregg hosts the agent inside a jail
/// whose OS sandbox denies the exact ambient reaches a leaky hermes base tool
/// makes. The agent IS jailed (four base teeth) AND all three base-tool escapes
/// (unconfined shell / host-FS read / arbitrary socket) are denied. We do NOT fork
/// hermes — the jail neutralizes the base tools at the OS level.
#[test]
fn leg_b_the_jail_neutralizes_the_base_tool_escape() {
    let kernel = ProcessKernel::new();
    // dregg the host, SEALED egress (the default) — no door to the outside at all.
    let host = DreggHost::new();

    let report = host
        .run_hosted_agent(&kernel, None, None)
        .expect("spawn the agent into the dregg jail and reap its verdict");

    // THE AGENT IS JAILED — file/net/exec/extra-fd denied, the dregg Endpoint live.
    assert!(
        report.jailed,
        "the agent is jailed (the four base confinement teeth held); verdict=0x{:x}",
        report.verdict
    );

    // THE BASE-TOOL ESCAPE IS NEUTRALIZED — each leaky base tool's ambient reach
    // is denied by the jail. Assert each tooth individually so a single leak names.
    assert_eq!(
        report.verdict & escape::UNCONFINED_SHELL_DENIED,
        escape::UNCONFINED_SHELL_DENIED,
        "BASE-TOOL LEAK — an unconfined shell (hermes `terminal`) ran; verdict=0x{:x}",
        report.verdict
    );
    assert_eq!(
        report.verdict & escape::HOST_FS_READ_DENIED,
        escape::HOST_FS_READ_DENIED,
        "BASE-TOOL LEAK — a host-FS read (hermes `read_file`) succeeded; verdict=0x{:x}",
        report.verdict
    );
    assert_eq!(
        report.verdict & escape::ARBITRARY_SOCKET_DENIED,
        escape::ARBITRARY_SOCKET_DENIED,
        "BASE-TOOL LEAK — an arbitrary socket (hermes `web`) opened; verdict=0x{:x}",
        report.verdict
    );
    assert!(
        report.base_tools_neutralized,
        "ALL base-tool escapes neutralized at the OS level; verdict=0x{:x}",
        report.verdict
    );

    // SEALED by default — no egress door was wired, so nothing outside was reached.
    assert!(!report.egress_granted_open, "sealed host opened no egress door");
}

/// (c) STRUCTURED EGRESS — the host grants ONE specific host subpath; inside the
/// jail that path is readable (the door is open) while a SIBLING outside the grant
/// stays denied (the door is to a named resource, not a hole). Sealing/revoking
/// closes it. The base jail still holds around the door.
#[test]
fn leg_c_structured_egress_is_a_specific_grantable_revocable_door() {
    // A real granted resource on the host: a temp dir + a file inside it, and a
    // SIBLING dir outside the grant.
    let base = std::env::temp_dir().join(format!("deos_egress_{}", std::process::id()));
    let granted_dir = base.join("granted");
    let sibling_dir = base.join("sibling");
    std::fs::create_dir_all(&granted_dir).expect("mkdir granted");
    std::fs::create_dir_all(&sibling_dir).expect("mkdir sibling");
    let granted_file = granted_dir.join("notes.txt");
    let sibling_file = sibling_dir.join("secret.txt");
    std::fs::write(&granted_file, b"egress ok").expect("write granted file");
    std::fs::write(&sibling_file, b"should stay denied").expect("write sibling file");
    let granted_file = granted_file.to_str().unwrap().to_string();
    let sibling_file = sibling_file.to_str().unwrap().to_string();

    let kernel = ProcessKernel::new();

    // ── SEALED (default): the granted path is DENIED — no door at all. ──
    let sealed = DreggHost::new();
    assert!(sealed.egress.is_sealed());
    let r = sealed
        .run_hosted_agent(&kernel, Some(&granted_file), None)
        .expect("sealed hosted run");
    assert!(r.jailed, "still jailed; verdict=0x{:x}", r.verdict);
    assert!(
        !r.egress_granted_open,
        "SEALED host must DENY the path (no egress door); verdict=0x{:x}",
        r.verdict
    );

    // ── GRANTED: the host opens a door to exactly `granted_dir`. ──
    let host = DreggHost::new().with_egress_read(granted_dir.to_str().unwrap());
    assert!(!host.egress.is_sealed());
    // The policy admits the granted file but NOT the sibling (host-side check).
    assert!(host.egress.admits_read(&granted_file));
    assert!(!host.egress.admits_read(&sibling_file));

    let r = host
        .run_hosted_agent(&kernel, Some(&granted_file), Some(&sibling_file))
        .expect("granted hosted run");
    // The jail STILL holds around the door (file-other/net/exec/fd denied).
    assert!(
        r.jailed,
        "the base jail still holds around the egress door; verdict=0x{:x}",
        r.verdict
    );
    assert!(
        r.base_tools_neutralized,
        "base tools still neutralized with a door open; verdict=0x{:x}",
        r.verdict
    );
    // THE GRANTED door is open inside the jail…
    assert!(
        r.egress_granted_open,
        "the GRANTED host path must be readable inside the jail; verdict=0x{:x}",
        r.verdict
    );
    // …and the SIBLING outside the grant stays denied — a specific door, not a hole.
    assert!(
        r.egress_sibling_denied,
        "a SIBLING outside the grant must STAY DENIED (the door is specific); verdict=0x{:x}",
        r.verdict
    );

    // ── REVOKE: the door closes; the next jail is sealed against the path again. ──
    let mut revoked = DreggHost::new().with_egress_read(granted_dir.to_str().unwrap());
    revoked.egress.revoke(granted_dir.to_str().unwrap());
    assert!(revoked.egress.is_sealed(), "revoke closed the door");
    let r = revoked
        .run_hosted_agent(&kernel, Some(&granted_file), None)
        .expect("revoked hosted run");
    assert!(
        !r.egress_granted_open,
        "after REVOKE the path is DENIED again; verdict=0x{:x}",
        r.verdict
    );

    let _ = std::fs::remove_dir_all(&base);
}
