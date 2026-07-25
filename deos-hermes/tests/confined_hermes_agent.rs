//! THE REAL CONFINED AGENT — a brain-driven ACP loop through the gate.
//!
//! These tests drive the UNCHANGED [`AcpClient`] over [`HermesAgentPeer`] — the
//! peer that replaced the scripted stand-in with a real [`LlmBrain`] closed loop.
//! They prove the four things the stand-in could not:
//!
//!   1. the agent RUNS a real multi-step ACP session whose tool-calls a BRAIN
//!      decided (not a pre-written list), each one cap-gated + receipted;
//!   2. a tool-call is cap-gated — ADMITTED when granted, REFUSED in-band when
//!      outside caps — and the BRAIN ADAPTS to the refusal (it does not bang on a
//!      denied tool; it falls back to a tool it is allowed);
//!   3. an admitted tool-call drives a real World action — a committed verified
//!      turn carrying both the meter advance and the tool's effect (the receipt);
//!   4. the BYO LLM keys are CONFINED — the operator's provider secret reaches the
//!      provider and NOWHERE the agent's reach (tool args / receipts / wire /
//!      final text) travels. Proven over a mock provider; the live BYO-key path is
//!      the same brain over a real `LlmHttpCaller`.

use std::collections::VecDeque;
use std::sync::{Arc, RwLock};

use deos_hermes::{
    AcpClient, GrantRegistry, HermesAgentPeer, HttpLlm, LlmHttpCaller, LlmKeys, LocalBrain,
    PermissionOutcome,
};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};
use serde_json::{Value, json};

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// (1) The agent runs a real multi-step ACP loop whose calls the brain decided.
#[test]
fn confined_agent_runs_a_real_brain_driven_acp_loop() {
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
    let gateway = deos_hermes::HermesGateway::new(&rt, root, registry);

    // The brain reads the prompt and forms its own plan — search + write + run.
    let peer = HermesAgentPeer::new("sess-agent", LocalBrain::new());
    let mut client = AcpClient::new(peer, gateway, 100);

    let run = client
        .run_prompt(
            "/tmp/proj",
            "search the docs, write a notes file, then run the build",
        )
        .expect("the brain-driven ACP loop runs end-to-end");

    assert_eq!(run.stop_reason, "end_turn");
    assert!(
        run.agent_text.contains("thinking"),
        "agent streamed a reply: {:?}",
        run.agent_text
    );

    // The brain decided MORE THAN ONE tool-call (a loop, not a one-shot), and each
    // was gated to a real verdict.
    assert!(
        run.verdicts.len() >= 3,
        "brain drove a multi-step turn, got {} verdicts",
        run.verdicts.len()
    );
    // Within the standard floors every call is admitted = a receipted turn.
    for (call, outcome) in &run.verdicts {
        match outcome {
            PermissionOutcome::Allow { receipt, .. } => {
                assert_eq!(receipt.len(), 64, "{} got a real hex receipt", call.name);
            }
            other => panic!("{} expected Allow within floors, got {other:?}", call.name),
        }
    }
    // The final message reports the agent worked within its caps.
    assert!(
        run.agent_text.contains("completed"),
        "the brain summarized its turn: {:?}",
        run.agent_text
    );
}

/// (2) A tool-call is cap-gated both ways, AND the brain adapts to the refusal.
#[test]
fn tool_call_cap_gated_and_brain_adapts_to_refusal() {
    let (rt, root) = grantor();
    // Deny `write_file` outright (rate 0); everything else within floors.
    let registry = GrantRegistry::default_for_session(1000)
        .with_standard_tool_grants(1000)
        .with_grant_for_tool_deny("write_file");
    let gateway = deos_hermes::HermesGateway::new(&rt, root, registry);

    let peer = HermesAgentPeer::new("sess-deny", LocalBrain::new());
    let mut client = AcpClient::new(peer, gateway, 100);

    let run = client
        .run_prompt("/tmp/proj", "write a notes file and run the build")
        .expect("loop completes even when a tool is denied");

    // The write_file the brain reached for was REFUSED in-band, naming the leg.
    let write = run
        .verdicts
        .iter()
        .find(|(c, _)| c.name == "write_file")
        .expect("the brain reached for write_file");
    match &write.1 {
        PermissionOutcome::Reject { reason, .. } => {
            assert!(
                reason.contains("scope") || reason.contains("rate"),
                "refusal names the leg that bit: {reason}"
            );
        }
        other => panic!("write_file outside caps must be refused, got {other:?}"),
    }

    // The brain ADAPTED: it reached write_file exactly once (never banged on the
    // denied tool) and fell back to a read_file that was NOT in its first plan.
    let write_calls = run
        .verdicts
        .iter()
        .filter(|(c, _)| c.name == "write_file")
        .count();
    assert_eq!(write_calls, 1, "brain did not retry the denied tool");
    let read_after = run
        .verdicts
        .iter()
        .any(|(c, o)| c.name == "read_file" && o.allowed());
    assert!(
        read_after,
        "brain fell back to a read-only tool it was allowed: {:?}",
        run.verdicts
            .iter()
            .map(|(c, _)| &c.name)
            .collect::<Vec<_>>()
    );

    // The terminal call still landed (a granted tool), so the agent made progress.
    assert!(
        run.verdicts
            .iter()
            .any(|(c, o)| c.name == "terminal" && o.allowed()),
        "a granted tool still committed under partial confinement"
    );
}

/// (3) An admitted tool-call drives a real World action — a committed verified
/// turn (the receipt) carrying the meter advance + the tool's effect.
#[test]
fn admitted_tool_call_drives_a_real_receipted_turn() {
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
    let gateway = deos_hermes::HermesGateway::new(&rt, root, registry);

    let peer = HermesAgentPeer::new("sess-world", LocalBrain::new());
    let mut client = AcpClient::new(peer, gateway, 100);
    let run = client
        .run_prompt("/tmp/proj", "write a notes file")
        .expect("loop completes");

    let (_, outcome) = run
        .verdicts
        .iter()
        .find(|(c, _)| c.name == "write_file")
        .expect("the brain wrote a file");
    match outcome {
        PermissionOutcome::Allow { receipt, .. } => {
            assert_eq!(receipt.len(), 64);
            assert!(receipt.chars().all(|c| c.is_ascii_hexdigit()));
        }
        other => panic!("expected a receipted World turn, got {other:?}"),
    }
    // The metered counter advanced exactly once for the per-tool write worker — a
    // real committed turn on the verified executor, not a no-op.
    assert_eq!(client.gateway().calls_made_for_tool("write_file"), 1);
}

/// (4a) The on-box brain's BYO keys never leak into the agent's reach.
#[test]
fn llm_keys_are_confined_on_the_on_box_brain() {
    const SECRET: &str = "sk-live-DO-NOT-LEAK-9f3a7c";
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
    let gateway = deos_hermes::HermesGateway::new(&rt, root, registry);

    let brain = LocalBrain::new().with_keys(LlmKeys::new("acme", SECRET));
    let peer = HermesAgentPeer::new("sess-keys", brain);
    let mut client = AcpClient::new(peer, gateway, 100);
    let run = client
        .run_prompt("/tmp/proj", "search and write and run")
        .expect("loop completes");

    assert_secret_absent_from_agent_reach(SECRET, &run, client.peer().convo());

    // The redacted Debug is a confinement tooth: even a stray log can't leak it.
    let dbg = format!("{:?}", client.peer().brain().keys());
    assert!(dbg.contains("<redacted>"), "keys Debug is redacted: {dbg}");
    assert!(!dbg.contains(SECRET), "keys Debug leaked the secret: {dbg}");
}

/// (4b) The LIVE BYO-key path — the same brain over a (mock) provider caller. The
/// key flows to the provider and NOWHERE else; the loop is gated identically.
#[test]
fn byo_key_live_path_over_a_mock_provider() {
    const SECRET: &str = "sk-live-BYO-KEY-7b21e0";
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
    let gateway = deos_hermes::HermesGateway::new(&rt, root, registry);

    // The provider's canned tool-use stream: search → run → finish. (A real
    // endpoint returns this shape; here a mock caller does, so the key path + the
    // parse + the gate fire end-to-end without a live key.)
    let responses = VecDeque::from(vec![
        json!({ "content": [{ "type": "tool_use", "name": "web_search", "input": { "query": "dregg" } }] }),
        json!({ "content": [{ "type": "tool_use", "name": "terminal", "input": { "command": "cargo build" } }] }),
        json!({ "content": [{ "type": "text", "text": "done — both tool-calls landed as receipted turns." }] }),
    ]);
    let caller = MockHttpCaller {
        responses,
        seen_keys: Vec::new(),
        seen_bodies: Vec::new(),
    };
    let brain = HttpLlm::new(
        LlmKeys::new("acme", SECRET),
        "https://provider.example/v1/messages",
        "acme-large",
        caller,
    );
    let peer = HermesAgentPeer::new("sess-byo", brain);
    let mut client = AcpClient::new(peer, gateway, 100);

    let run = client
        .run_prompt("/tmp/proj", "do some work")
        .expect("the BYO-key brain drives the loop");

    // The provider returned two tool-calls; both were gated to real receipts.
    assert_eq!(run.verdicts.len(), 2, "two provider tool-calls were gated");
    assert!(run.verdicts.iter().all(|(_, o)| o.allowed()));
    assert!(
        run.agent_text.contains("done"),
        "final provider text streamed"
    );

    let brain = client.peer().brain();
    // The confined channel is live: the key reached the provider caller…
    assert!(
        brain.key_reached_provider(),
        "the BYO key was handed to the provider"
    );
    let caller = brain.caller();
    assert!(
        caller.seen_keys.iter().all(|k| k == SECRET) && !caller.seen_keys.is_empty(),
        "the provider caller received exactly the BYO key"
    );
    // …and NOWHERE else: not in the request bodies (it travels in the auth header,
    // not the payload), not in the agent's reach.
    for body in &caller.seen_bodies {
        let body_s = serde_json::to_string(body).unwrap();
        assert!(
            !body_s.contains(SECRET),
            "the BYO key must not be embedded in the provider request body"
        );
    }
    assert_secret_absent_from_agent_reach(SECRET, &run, client.peer().convo());
}

/// Scan the WHOLE agent reach — the streamed text, every tool-call's args, every
/// gate verdict (receipt / refusal), and the conversation the brain reasoned over
/// — and assert the secret appears in none of it.
fn assert_secret_absent_from_agent_reach(
    secret: &str,
    run: &deos_hermes::PromptRun,
    convo: &deos_hermes::AgentConvo,
) {
    assert!(
        !run.agent_text.contains(secret),
        "secret leaked into the agent's streamed text"
    );
    for call in &run.tool_calls {
        let s = serde_json::to_string(&call.arguments).unwrap();
        assert!(!s.contains(secret), "secret leaked into a tool-call's args");
    }
    for (call, outcome) in &run.verdicts {
        let s = serde_json::to_string(call).unwrap();
        assert!(!s.contains(secret), "secret leaked into a gated tool-call");
        match outcome {
            PermissionOutcome::Allow { receipt, .. } => {
                assert!(!receipt.contains(secret), "secret leaked into a receipt")
            }
            PermissionOutcome::Reject { reason, .. } => {
                assert!(!reason.contains(secret), "secret leaked into a refusal")
            }
        }
    }
    for obs in &convo.observations {
        let s = serde_json::to_string(&obs.arguments).unwrap();
        assert!(!s.contains(secret), "secret leaked into the conversation");
        assert!(
            !obs.detail.contains(secret),
            "secret leaked into a tool result"
        );
    }
}

/// (5) A LOOPING model is CAPPED — a paid HttpLlm that NEVER emits a final
/// message (every response is another tool_use) would drive unbounded PAID
/// provider round-trips (a live DoS). `with_max_steps(N)` forces a Finish after
/// exactly N tool-calls, and the provider is called exactly N times — no round
/// trip past the cap.
#[test]
fn looping_model_is_capped_after_n_tool_calls() {
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
    let gateway = deos_hermes::HermesGateway::new(&rt, root, registry);

    // The model never finishes: every completion is another tool_use.
    let brain = HttpLlm::new(
        LlmKeys::new("acme", "sk-test-loop"),
        "https://provider.example/v1/messages",
        "acme-large",
        LoopingCaller { calls: 0 },
    );

    const CAP: usize = 4;
    let peer = HermesAgentPeer::with_max_steps("sess-cap", brain, CAP);
    let mut client = AcpClient::new(peer, gateway, 100);

    // WITHOUT the cap this run would never return (an unbounded loop). It returns
    // BECAUSE the cap forces a Finish.
    let run = client
        .run_prompt("/tmp/proj", "loop forever")
        .expect("the per-turn cap terminates a looping model");

    assert_eq!(run.stop_reason, "end_turn", "the capped turn ended cleanly");
    assert_eq!(
        run.verdicts.len(),
        CAP,
        "the loop fired exactly the cap of tool-calls, then a forced Finish"
    );
    // The paid provider was hit exactly CAP times — the cap forces the Finish
    // WITHOUT one more `next_step`/provider round-trip.
    assert_eq!(
        client.peer().brain().caller().calls,
        CAP,
        "no PAID provider round-trip happened past the cap"
    );
    assert!(
        run.agent_text.contains("limit"),
        "the forced Finish names the cap: {:?}",
        run.agent_text
    );
}

/// A provider caller that ALWAYS returns another tool_use — a looping model that
/// never emits a final message. `calls` counts the paid round-trips it received.
struct LoopingCaller {
    calls: usize,
}

impl LlmHttpCaller for LoopingCaller {
    fn complete(
        &mut self,
        _endpoint: &str,
        _api_key: &str,
        _request: &Value,
    ) -> Result<Value, String> {
        self.calls += 1;
        Ok(json!({
            "content": [{
                "type": "tool_use",
                "name": "terminal",
                "input": { "command": "echo loop" }
            }]
        }))
    }
}

/// A mock provider caller — returns a scripted response stream, recording the key
/// and request bodies it received so a test can assert the key's confinement.
struct MockHttpCaller {
    responses: VecDeque<Value>,
    seen_keys: Vec<String>,
    seen_bodies: Vec<Value>,
}

impl LlmHttpCaller for MockHttpCaller {
    fn complete(
        &mut self,
        _endpoint: &str,
        api_key: &str,
        request: &Value,
    ) -> Result<Value, String> {
        self.seen_keys.push(api_key.to_string());
        self.seen_bodies.push(request.clone());
        Ok(self
            .responses
            .pop_front()
            .unwrap_or_else(|| json!({ "text": "done" })))
    }
}
