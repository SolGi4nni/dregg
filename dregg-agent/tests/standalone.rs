//! The hackathon proof: a bounded + cap-gated + receipted agent driven by an
//! OpenAI-compatible / Hermes model, running entirely on the dregg substrate
//! with **zero** cloud / private dependency.
//!
//! Everything here uses only `dregg-agent`'s public API. The brain is the
//! recorded OpenAI-compatible transport (the deterministic stand-in for a live
//! Hermes / Kimi / any-OpenAI-compatible model); the compute tool is wired
//! through the **injected runner** seam, so there is no sandbox engine and no
//! host dependency — the open core owns the witness, the caller owns the run.

use dregg_agent::agent::{AgentCloud, AgentSpec, verify_agent_run};
use dregg_agent::brain::{OpenAICompatBrain, ProviderKey, RecordedOpenAICaller};
use dregg_agent::toolkit::{HealthSnapshot, RunReport, Toolkit};

fn spec(id: &str, budget: i64, services: &[&str], cells: &[&str]) -> AgentSpec {
    let mut s = AgentSpec::new(id, budget);
    s.services = services.iter().map(|s| s.to_string()).collect();
    s.cells = cells.iter().map(|s| s.to_string()).collect();
    s
}

/// A recorded OpenAI tool-call message (the exact provider wire shape).
fn tool_call(name: &str, args: &str) -> serde_json::Value {
    serde_json::json!({
        "choices": [{
            "message": {
                "role": "assistant",
                "content": null,
                "tool_calls": [{
                    "id": format!("call_{name}"),
                    "type": "function",
                    "function": { "name": name, "arguments": args }
                }]
            },
            "finish_reason": "tool_calls"
        }]
    })
}

fn finish(text: &str) -> serde_json::Value {
    serde_json::json!({
        "choices": [{
            "message": { "role": "assistant", "content": text },
            "finish_reason": "stop"
        }]
    })
}

/// THE HACKATHON-CRITICAL PATH: an OpenAI-compatible / Hermes agent reasons,
/// proposes tool calls, and every one is cap-gated, budget-drawn, and receipted —
/// then the whole run re-witnesses without trusting the host. No private cloud,
/// no sandbox engine: substrate-only.
#[test]
fn a_hermes_agent_runs_bounded_and_receipted_with_no_cloud() {
    let cloud = AgentCloud::from_seed([7u8; 32]);
    let handle = cloud
        .deploy(&spec(
            "agent:hackathon",
            10,
            &["run_tests", "check_health"],
            &["/deploy"],
        ))
        .unwrap();

    // The compute tool is wired behind the INJECTED runner — a std closure here,
    // a real sandbox in the cloud. The open core never depends on an engine.
    let toolkit = Toolkit::new()
        .with_run_tests("run_tests", "rust", "fn main(){}", |_lang, _src| {
            Ok(RunReport::new(["0"], "WasmSandbox"))
        })
        .with_check_health("check_health", || HealthSnapshot::healthy("node up · Σδ=0"));

    // The model's reasoning, recorded as the real OpenAI tool-call shape:
    //   write the deploy cell → run the tests → check health → finish.
    let caller = RecordedOpenAICaller::new(vec![
        tool_call(
            "cell_write",
            r#"{"path":"/deploy","value":"site@commit-abc"}"#,
        ),
        tool_call("invoke", r#"{"service":"run_tests"}"#),
        tool_call("invoke", r#"{"service":"check_health"}"#),
        finish("Deployed, tests green, node healthy."),
    ]);
    let mut brain = OpenAICompatBrain::with_defaults(
        "Deploy the site, run the tests, and confirm the node is healthy.",
        vec!["run_tests".into(), "check_health".into()],
        vec!["/deploy".into()],
        ProviderKey::new("moonshot", "sk-TEST-DONOTLEAK-0123456789"),
        caller,
    );

    let report = cloud.run_with_toolkit(&handle, &mut brain, &toolkit);

    // The agent did real, bounded work: the deploy write + 2 tool calls were
    // admitted, each drew from the budget, each is receipted.
    assert_eq!(
        report.admitted, 3,
        "deploy + run_tests + check_health admitted"
    );
    assert_eq!(report.consumed, 3, "each action drew from the budget");
    assert_eq!(
        report.receipts.len(),
        3,
        "the whole sequence is in the chain"
    );

    // Every tool verdict passed and is bound into the receipt.
    assert!(
        report.all_tools_passed(),
        "QA all green: {:?}",
        report.tool_results()
    );

    // The BYO key never leaked into the recorded transport bodies.
    assert!(
        !brain.caller().key_leak_in_body(),
        "the secret never hits the wire body"
    );

    // THE TEETH: the whole run re-witnesses without trusting the host — a forged
    // verdict would break the ed25519 receipt signature.
    let verified = verify_agent_run(&report).expect("the run re-witnesses end to end");
    assert_eq!(
        verified.actions, 3,
        "all three actions accounted for in the proof"
    );
}

/// THE BOUND: an over-budget agent is contained in-band — the runaway stops at the
/// ceiling, not by trusting the model to behave.
#[test]
fn the_budget_bounds_a_runaway_agent() {
    let cloud = AgentCloud::from_seed([8u8; 32]);
    // Budget 2: only two calls fit.
    let handle = cloud
        .deploy(&spec("agent:runaway", 2, &["check_health"], &[]))
        .unwrap();
    let toolkit =
        Toolkit::new().with_check_health("check_health", || HealthSnapshot::healthy("ok"));

    // The model keeps proposing the same tool call, over and over.
    let caller =
        RecordedOpenAICaller::repeating(vec![tool_call("invoke", r#"{"service":"check_health"}"#)]);
    let mut brain = OpenAICompatBrain::with_defaults(
        "Check health repeatedly.",
        vec!["check_health".into()],
        vec![],
        ProviderKey::unauthenticated(),
        caller,
    );

    let report = cloud.run_with_toolkit(&handle, &mut brain, &toolkit);
    assert_eq!(report.admitted, 2, "the budget admits exactly two calls");
    assert!(report.budget_refused >= 1, "the rest are bounded in-band");
    assert_eq!(report.headroom, 0, "the ceiling is fully drawn");
    verify_agent_run(&report).expect("the bounded run still re-witnesses");
}

/// THE GATE: a tool the agent's bundle does not grant is refused before it runs —
/// authority is the attenuable powerbox, not the model's discretion.
#[test]
fn the_cap_gate_refuses_an_ungranted_tool() {
    let cloud = AgentCloud::from_seed([9u8; 32]);
    // The bundle grants ONLY check_health.
    let handle = cloud
        .deploy(&spec("agent:narrow", 10, &["check_health"], &[]))
        .unwrap();
    let toolkit = Toolkit::new()
        .with_check_health("check_health", || HealthSnapshot::healthy("ok"))
        .with_run_tests("run_tests", "rust", "fn main(){}", |_l, _s| {
            Ok(RunReport::new(["0"], "WasmSandbox"))
        });

    let caller = RecordedOpenAICaller::new(vec![
        tool_call("invoke", r#"{"service":"check_health"}"#), // granted
        tool_call("invoke", r#"{"service":"run_tests"}"#),    // NOT granted
        finish("done"),
    ]);
    let mut brain = OpenAICompatBrain::with_defaults(
        "Check health, then run tests.",
        vec!["check_health".into()],
        vec![],
        ProviderKey::unauthenticated(),
        caller,
    );

    let report = cloud.run_with_toolkit(&handle, &mut brain, &toolkit);
    assert_eq!(report.admitted, 1, "only the granted tool ran");
    assert_eq!(
        report.cap_refused, 1,
        "the ungranted tool is refused before running"
    );
    verify_agent_run(&report).expect("the run re-witnesses");
}
