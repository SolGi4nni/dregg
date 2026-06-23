//! `deos-hermes` — drive the confined Hermes agent loop, two ways.
//!
//! 1. THE LIVE-SHAPED ACP LOOP (default, or `cargo run -- mock`): the real ACP
//!    client drives a session against the faithful [`MockHermesPeer`] (replaying
//!    `acp_adapter`'s message shapes), answering every `session/request_permission`
//!    with the [`HermesGateway`] verdict — a cap-gated, metered, receipted dregg
//!    turn (with the tool's side-effect riding it) or an in-band refusal. Then it
//!    prints the agent dock view (chat + tool-call ledger + the mandate inspector).
//!
//! 2. THE LIVE SUBPROCESS (`cargo run -- live`): spawns the REAL `hermes-acp`
//!    stdio server and drives the SAME client over its stdio — `initialize` →
//!    `session/new` → `session/set_model` → `session/prompt`, answering each
//!    `session/request_permission` through the [`HermesGateway`]. The prompt asks
//!    Hermes to run a command Hermes's own dangerous-command detector flags
//!    (`rm -rf …`), which is what makes Hermes issue a real
//!    `session/request_permission` back to the client — exercising the gateway
//!    seam against a LIVE agent loop.
//!
//!    The live ceiling, honestly: the agent loop needs a model provider +
//!    credentials. `hermes-acp` advertises AWS Bedrock models; if no Bedrock
//!    credentials / network are present the provider call fails inside Hermes and
//!    no tool-call (hence no permission request) is produced — the handshake +
//!    session still complete. `run_live` reports exactly how far it got.
//!
//! Run: `cd deos-hermes && cargo run` (mock) or `cargo run -- live`.

use std::sync::{Arc, RwLock};

use deos_hermes::surface::AgentDockModel;
use deos_hermes::{
    AcpClient, AcpTransport, GrantRegistry, HermesGateway, MockHermesPeer, ScriptedCall,
};
use dregg_sdk::{AgentCipherclerk, AgentRuntime};

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "mock".to_string());
    match mode.as_str() {
        "live" => run_live(),
        _ => run_mock(),
    }
}

/// Build the grantor runtime + root token + the standard confinement (per-kind
/// floors + the curated per-tool tightenings, deadline/clock 1000).
fn confinement() -> (AgentRuntime, dregg_sdk::HeldToken, GrantRegistry) {
    let mut cclerk = AgentCipherclerk::new();
    let root_token = cclerk.mint_token(&[7u8; 32], "deos");
    let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    // The per-tool grants tighten `terminal` (rate 5), `web_extract` (15), etc.
    let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
    (runtime, root_token, registry)
}

/// The live-shaped ACP loop over the faithful mock peer.
fn run_mock() {
    println!("deos-hermes — the confined Hermes ACP loop (mock peer)\n");
    let (runtime, root_token, registry) = confinement();
    let gateway = HermesGateway::new(&runtime, root_token, registry);

    // A scripted Hermes turn: a search, a file write, three terminal calls (the
    // 3rd over a tightened rate, in a tighter demo registry below), a fetch.
    let script = vec![
        ScriptedCall::new("web_search", serde_json::json!({"query": "dregg ocap"})),
        ScriptedCall::new(
            "write_file",
            serde_json::json!({"path": "notes/plan.md", "content": "the plan"}),
        ),
        ScriptedCall::new("terminal", serde_json::json!({"command": "cargo build"})),
        ScriptedCall::new("terminal", serde_json::json!({"command": "cargo test"})),
        ScriptedCall::new("read_file", serde_json::json!({"path": "src/lib.rs"})),
    ];

    let peer = MockHermesPeer::new("sess-demo", script);
    let mut client = AcpClient::new(peer, gateway, 10);

    let run = client
        .run_prompt("/Users/ember/dev/breadstuffs", "help me confine hermes")
        .expect("the ACP loop runs end-to-end over the mock peer");

    let model = AgentDockModel::from_run("sess-demo", &run, client.gateway());
    print!("{}", model.render_text());
}

/// The `hermes-acp` program deos spawns for the live loop. Overridable via
/// `HERMES_ACP_BIN` (e.g. the Homebrew shim `/opt/homebrew/bin/hermes-acp`).
fn hermes_acp_program() -> String {
    std::env::var("HERMES_ACP_BIN").unwrap_or_else(|_| "hermes-acp".to_string())
}

/// The provider model deos pins for the live loop via `session/set_model`.
/// Overridable via `HERMES_ACP_MODEL`. The default is a Bedrock model `hermes-acp`
/// advertises; the live agent loop only reaches the provider once a model is
/// pinned (session/new alone leaves an empty `modelId`).
fn hermes_acp_model() -> String {
    std::env::var("HERMES_ACP_MODEL")
        .unwrap_or_else(|_| "bedrock:global.amazon.nova-2-lite-v1:0".to_string())
}

/// The live subprocess path: spawn the REAL `hermes-acp`, complete the handshake,
/// pin a model, prompt with a command Hermes flags as dangerous (so it issues a
/// `session/request_permission` back), and answer through the gateway.
///
/// Reports exactly how far the live env let it get (handshake / session / a real
/// permission round-trip / a full provider-backed turn), so the live ceiling is
/// honest from the output alone.
fn run_live() {
    println!("deos-hermes — the confined Hermes ACP loop (LIVE subprocess)\n");
    let program = hermes_acp_program();
    let model = hermes_acp_model();
    println!("spawning `{program}` (model `{model}`)…\n");

    let (runtime, root_token, registry) = confinement();
    let gateway = HermesGateway::new(&runtime, root_token, registry);

    let transport = match AcpTransport::spawn_hermes(&program, &[]) {
        Ok(t) => t,
        Err(e) => {
            eprintln!(
                "could not spawn `{program}`: {e}\n\
                 (set HERMES_ACP_BIN to the hermes-acp shim, e.g. \
                 /opt/homebrew/bin/hermes-acp; or `cargo run` for the mock loop)"
            );
            return;
        }
    };

    let mut client = AcpClient::new(transport, gateway, 10);
    // The prompt asks for a command Hermes's dangerous-command detector flags
    // (`rm -rf …` = "recursive delete"), so Hermes issues a real
    // `session/request_permission` — the gateway seam exercised LIVE. The target
    // path is a harmless scratch dir, and the gateway answer the test path expects
    // is the gateway's own verdict (allow/deny), not a blanket allow.
    let prompt = "Run exactly this shell command and nothing else: \
                  rm -rf /tmp/deos_hermes_live_probe";
    match client.run_prompt_with_model("/tmp", prompt, Some(&model)) {
        Ok(run) => {
            let dock = AgentDockModel::from_run("live", &run, client.gateway());
            print!("{}", dock.render_text());
            println!("\n── live ceiling ──");
            println!("handshake + session/new + session/prompt: COMPLETED (stop_reason = {})", run.stop_reason);
            if run.verdicts.is_empty() {
                println!(
                    "permission round-trip: NOT reached — Hermes produced no tool-call.\n\
                     (the live agent loop needs a working model provider + credentials; \
                     with none, the provider call fails inside Hermes before any tool-call \
                     is emitted. The handshake/session above is fully LIVE.)"
                );
            } else {
                println!(
                    "permission round-trip: REACHED — {} tool-call(s) were gated through the \
                     HermesGateway LIVE (a cap-gated, receipted dregg turn per allow).",
                    run.verdicts.len()
                );
            }
        }
        Err(e) => {
            eprintln!(
                "live hermes-acp loop ended early: {e}\n\
                 (the handshake may not have completed — check that `{program}` runs \
                 `--check` cleanly: its venv needs the `agent-client-protocol` package)"
            );
        }
    }
}
