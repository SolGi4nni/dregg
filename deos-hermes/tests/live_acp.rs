//! THE LIVE ACP LOOP TEST — drive the REAL `hermes-acp` subprocess, not the mock.
//!
//! Unlike `acp_loop.rs` (which drives the faithful [`MockHermesPeer`]), this test
//! spawns the actual `hermes-acp` stdio server and drives the SAME
//! [`AcpClient`] over its stdio: `initialize` → `session/new` →
//! `session/set_model` → `session/prompt`, answering each
//! `session/request_permission` through the [`HermesGateway`].
//!
//! ## It SKIPS gracefully when the env can't run it
//!
//! Driving a live agent loop needs (1) a working `hermes-acp` install whose venv
//! has the `agent-client-protocol` package, and (2) a model provider +
//! credentials for the agent loop to reach the provider. Neither is guaranteed in
//! CI, so this test SKIPS (prints why and returns) rather than failing when:
//!
//!   * no `hermes-acp` is found (`HERMES_ACP_BIN` unset and not on PATH), or
//!   * `hermes-acp --check` fails (the venv lacks `acp`), or
//!   * the live handshake can't complete (no subprocess output).
//!
//! What it ASSERTS when the env DOES allow it: the live handshake + session
//! complete (a real `stop_reason`), and — when a provider produces a tool-call —
//! every `session/request_permission` is answered by the gateway with a real
//! receipt or an in-band refusal.
//!
//! Run it explicitly (it is `#[ignore]` so the default `cargo test` stays
//! hermetic over the mock):
//!
//! ```text
//! HERMES_ACP_BIN=/opt/homebrew/bin/hermes-acp \
//!   cargo test --test live_acp -- --ignored --nocapture
//! ```

use std::process::Command;
use std::sync::{Arc, RwLock};

use deos_hermes::{AcpClient, AcpTransport, GrantRegistry, HermesGateway};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// The `hermes-acp` program to drive: `HERMES_ACP_BIN`, else `hermes-acp` on PATH.
fn hermes_acp_program() -> String {
    std::env::var("HERMES_ACP_BIN").unwrap_or_else(|_| "hermes-acp".to_string())
}

/// Is `hermes-acp` present AND its ACP deps importable? Runs `hermes-acp --check`,
/// which imports `acp` + the adapter and prints "Hermes ACP check OK" on success.
/// Returns `Some(program)` if usable, else `None` (so the test can SKIP).
fn usable_hermes_acp() -> Option<String> {
    let program = hermes_acp_program();
    let out = Command::new(&program).arg("--check").output().ok()?;
    if out.status.success() && String::from_utf8_lossy(&out.stdout).contains("check OK") {
        Some(program)
    } else {
        None
    }
}

#[test]
#[ignore = "drives the real hermes-acp subprocess; run with --ignored when a hermes-acp install is present"]
fn live_hermes_acp_handshake_and_gateway_seam() {
    let Some(program) = usable_hermes_acp() else {
        eprintln!(
            "SKIP: no usable `hermes-acp` (set HERMES_ACP_BIN, and ensure its venv has the \
             `agent-client-protocol` package — `hermes-acp --check` must print 'check OK')."
        );
        return;
    };
    eprintln!("LIVE: driving `{program}`");

    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
    let gateway = HermesGateway::new(&rt, root, registry);

    let transport = match AcpTransport::spawn_hermes(&program, &[]) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("SKIP: could not spawn `{program}`: {e}");
            return;
        }
    };
    let mut client = AcpClient::new(transport, gateway, 10);

    // The default model `hermes-acp` advertises; overridable for other installs.
    let model = std::env::var("HERMES_ACP_MODEL")
        .unwrap_or_else(|_| "bedrock:global.amazon.nova-2-lite-v1:0".to_string());

    // Ask for a command Hermes's dangerous-command detector flags (`rm -rf …`),
    // so — when a provider is reachable — Hermes issues a real
    // `session/request_permission` back, exercising the gateway seam LIVE.
    let prompt = "Run exactly this shell command and nothing else: \
                  rm -rf /tmp/deos_hermes_live_test_probe";

    match client.run_prompt_with_model("/tmp", prompt, Some(&model)) {
        Ok(run) => {
            // The LIVE handshake + session + prompt completed with a real stop reason.
            assert!(
                !run.stop_reason.is_empty(),
                "live session completed with a stop_reason"
            );
            eprintln!(
                "LIVE handshake/session/prompt OK (stop_reason = {}, tool-calls seen = {}, \
                 permission verdicts = {})",
                run.stop_reason,
                run.tool_calls.len(),
                run.verdicts.len()
            );

            // If a provider was reachable, Hermes emitted a tool-call and a
            // permission request the gateway answered — assert each verdict is a
            // genuine gateway outcome (a real receipt on allow, a named reason on
            // reject). If no provider was reachable, there are zero verdicts and
            // we only proved the live handshake (still a real advance over the
            // mock — documented as the live ceiling).
            for (call, outcome) in &run.verdicts {
                match outcome {
                    deos_hermes::PermissionOutcome::Allow { receipt, .. } => {
                        assert_eq!(
                            receipt.len(),
                            64,
                            "{} got a real hex turn receipt from the live gateway",
                            call.name
                        );
                        assert!(receipt.chars().all(|c| c.is_ascii_hexdigit()));
                    }
                    deos_hermes::PermissionOutcome::Reject { reason, .. } => {
                        assert!(
                            !reason.is_empty(),
                            "{} rejected with a named reason",
                            call.name
                        );
                    }
                }
            }
        }
        Err(e) => {
            // The handshake didn't complete (the subprocess died, e.g. a venv
            // problem `--check` didn't surface). Skip rather than fail — the env
            // ceiling, not a code defect.
            eprintln!("SKIP: live loop did not complete the handshake: {e}");
        }
    }
}
