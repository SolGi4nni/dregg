//! A FAITHFUL MOCK HERMES ACP PEER — replays the real `acp_adapter` message shapes.
//!
//! The live `hermes-acp` install in this environment is broken (its venv lacks
//! the `acp` Python module), and a working one would need a model provider +
//! credentials to run an agent loop. To exercise the FULL client↔gate↔verdict
//! loop deterministically, this mock plays Hermes's half of an ACP session,
//! emitting the SAME JSON-RPC shapes `acp_adapter` does:
//!
//! * an `initialize` response with `protocolVersion` + `agentInfo`
//!   (`server.py::initialize`);
//! * a `session/new` response with a `sessionId`
//!   (`server.py::new_session` → `NewSessionResponse`);
//! * on `session/prompt`: a stream of `session/update` notifications
//!   (`agent_message_chunk`, `tool_call` events — `events.py`/`tools.py`), each
//!   dangerous tool-call preceded by a `session/request_permission` REQUEST
//!   carrying a real `ToolCallUpdate` payload
//!   (`permissions.py::_build_permission_tool_call`), then a `PromptResponse`
//!   with a `stopReason` (`server.py::prompt`).
//!
//! The mock is SCRIPTED with a list of tool-calls; it requests permission for
//! each, records the client's outcome, and only "runs" the ones the client
//! allowed. This lets a test assert the gateway both ALLOWED (with receipts) and
//! REFUSED (in-band) the right calls — the seam, end-to-end over the wire shape.

use std::collections::VecDeque;

use serde_json::{Value, json};

use crate::acp_client::{AcpError, AcpPeer, RpcMessage};

/// One scripted tool-call the mock Hermes will request permission for.
#[derive(Clone, Debug)]
pub struct ScriptedCall {
    /// The Hermes tool name (drives the ACP `kind` + the deos mandate).
    pub name: String,
    /// The tool's `rawInput` arguments.
    pub raw_input: Value,
}

impl ScriptedCall {
    pub fn new(name: &str, raw_input: Value) -> ScriptedCall {
        ScriptedCall {
            name: name.into(),
            raw_input,
        }
    }

    /// The ACP kind string Hermes's `tools.py::get_tool_kind` would assign
    /// (public so the confined stand-in agent can emit the same wire shape).
    pub fn acp_kind_str(&self) -> &'static str {
        self.acp_kind()
    }

    /// The ACP kind string Hermes's `tools.py::get_tool_kind` would assign.
    fn acp_kind(&self) -> &'static str {
        match crate::acp::ToolKind::of_tool(&self.name) {
            crate::acp::ToolKind::Read => "read",
            crate::acp::ToolKind::Edit => "edit",
            crate::acp::ToolKind::Execute => "execute",
            crate::acp::ToolKind::Fetch => "fetch",
            crate::acp::ToolKind::Search => "search",
            crate::acp::ToolKind::Other => "other",
        }
    }
}

/// The mock peer's outbound queue is built lazily as the client drives it; this
/// state machine tracks where in a session we are.
enum Phase {
    /// Awaiting `initialize`.
    Init,
    /// Awaiting `session/new`.
    NewSession,
    /// Awaiting `session/prompt`, then streaming the scripted calls.
    Prompt,
    /// The session is done (prompt answered).
    Done,
}

/// A faithful in-process Hermes ACP peer for the end-to-end loop test.
pub struct MockHermesPeer {
    phase: Phase,
    session_id: String,
    script: Vec<ScriptedCall>,
    /// Frames the mock has queued to hand the client on the next `recv`.
    outbox: VecDeque<RpcMessage>,
    /// The id the mock used for the in-flight permission request (so it can
    /// match the client's response and proceed).
    pending_permission_id: Option<i64>,
    /// The client's `session/prompt` request id, answered with the final
    /// `PromptResponse` once the script drains.
    prompt_response_id: Option<Value>,
    /// The client's outcomes per scripted call, recorded as the client responds
    /// to each permission request (for the test to assert allow/deny polarity).
    pub recorded_outcomes: Vec<(String, Value)>,
    next_id: i64,
    next_call: usize,
    tool_call_seq: usize,
    /// The opening agent message chunk (streamed on prompt). Defaults to
    /// `"working… "`; the interactive dock supplies a prompt-derived reply.
    opening: String,
    /// The closing agent message chunk (streamed once the script drains).
    closing: String,
    /// The `mcpServers` the client registered on `session/new` (captured so a test
    /// can assert deos registered the dregg confined MCP server as the model's
    /// tool source — the deep-integration wire).
    registered_mcp_servers: Value,
}

impl MockHermesPeer {
    /// A mock Hermes that will, on prompt, request permission for each scripted
    /// call in order.
    pub fn new(session_id: &str, script: Vec<ScriptedCall>) -> MockHermesPeer {
        MockHermesPeer {
            phase: Phase::Init,
            session_id: session_id.into(),
            script,
            outbox: VecDeque::new(),
            pending_permission_id: None,
            prompt_response_id: None,
            recorded_outcomes: Vec::new(),
            next_id: 1000,
            next_call: 0,
            tool_call_seq: 0,
            opening: "working… ".into(),
            closing: "done.".into(),
            registered_mcp_servers: Value::Null,
        }
    }

    /// The `mcpServers` the client registered on `session/new` (the model's tool
    /// source). `Null` until a `session/new` arrived; then the array the client
    /// sent — asserting deos registered the dregg confined MCP server.
    pub fn registered_mcp_servers(&self) -> &Value {
        &self.registered_mcp_servers
    }

    /// As [`MockHermesPeer::new`], but streaming a custom agent reply: `reply` is
    /// streamed as the OPENING `agent_message_chunk` (the agent "speaks" before it
    /// reaches for tools), and the closing chunk is omitted. The interactive dock
    /// uses this so the reply text reflects the user's actual prompt.
    pub fn with_reply(session_id: &str, script: Vec<ScriptedCall>, reply: &str) -> MockHermesPeer {
        let mut peer = MockHermesPeer::new(session_id, script);
        peer.opening = format!("{reply} ");
        peer.closing = String::new();
        peer
    }

    fn alloc_id(&mut self) -> i64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Queue the `session/update` tool_call event + the `session/request_permission`
    /// REQUEST for the next scripted call, if any. Returns whether a call was queued.
    fn queue_next_call(&mut self) -> bool {
        if self.next_call >= self.script.len() {
            return false;
        }
        let call = self.script[self.next_call].clone();
        self.next_call += 1;
        self.tool_call_seq += 1;
        let tool_call_id = format!("tc-{}", self.tool_call_seq);
        let kind = call.acp_kind();

        // (a) the streamed tool_call lifecycle event (events.py / build_tool_start).
        self.outbox.push_back(RpcMessage::notification(
            "session/update",
            json!({
                "sessionId": self.session_id,
                "update": {
                    "sessionUpdate": "tool_call",
                    "toolCallId": tool_call_id,
                    "toolName": call.name,
                    "kind": kind,
                    "status": "pending",
                    "rawInput": call.raw_input,
                }
            }),
        ));

        // (b) the request_permission REQUEST carrying a ToolCallUpdate payload
        //     (permissions.py::_build_permission_tool_call shape).
        let perm_id = self.alloc_id();
        self.pending_permission_id = Some(perm_id);
        self.outbox.push_back(RpcMessage::request(
            perm_id,
            "session/request_permission",
            json!({
                "sessionId": self.session_id,
                "toolCall": {
                    "toolCallId": tool_call_id,
                    "toolName": call.name,
                    "kind": kind,
                    "status": "pending",
                    "rawInput": call.raw_input,
                },
                "options": [
                    { "optionId": "allow_once", "kind": "allow_once", "name": "Allow once" },
                    { "optionId": "deny", "kind": "reject_once", "name": "Deny" }
                ]
            }),
        ));
        true
    }

    /// After a permission outcome arrives, queue the post-decision update (a
    /// tool_call_update marking completed/failed) and either the next call or the
    /// final PromptResponse.
    fn advance_after_permission(&mut self, allowed: bool, tool_call_id: &str) {
        // The tool_call status the editor would see next.
        let status = if allowed { "completed" } else { "failed" };
        self.outbox.push_back(RpcMessage::notification(
            "session/update",
            json!({
                "sessionId": self.session_id,
                "update": {
                    "sessionUpdate": "tool_call_update",
                    "toolCallId": tool_call_id,
                    "status": status,
                }
            }),
        ));
        if !self.queue_next_call() {
            // No more calls: stream a closing agent message (if any) + the prompt
            // response.
            if !self.closing.is_empty() {
                self.outbox.push_back(RpcMessage::notification(
                    "session/update",
                    json!({
                        "sessionId": self.session_id,
                        "update": {
                            "sessionUpdate": "agent_message_chunk",
                            "content": { "type": "text", "text": self.closing.clone() }
                        }
                    }),
                ));
            }
            self.phase = Phase::Done;
        }
    }
}

impl AcpPeer for MockHermesPeer {
    fn send(&mut self, msg: &RpcMessage) -> Result<(), AcpError> {
        // The client sent us something. If it's a response to our pending
        // permission request, record the outcome and advance the script.
        if (msg.result.is_some() || msg.error.is_some())
            && msg.id == self.pending_permission_id.map(|i| json!(i))
        {
            let result = msg.result.clone().unwrap_or(Value::Null);
            let outcome = result.get("outcome").cloned().unwrap_or(Value::Null);
            let option_id = outcome
                .get("optionId")
                .and_then(|v| v.as_str())
                .unwrap_or("deny");
            let allowed = option_id == "allow_once" || option_id == "allow_always";
            let tool_call_id = format!("tc-{}", self.tool_call_seq);
            self.recorded_outcomes.push((tool_call_id.clone(), outcome));
            self.pending_permission_id = None;
            self.advance_after_permission(allowed, &tool_call_id);
            return Ok(());
        }

        // Otherwise it's a client→peer REQUEST (initialize / session/new /
        // session/prompt). Queue the matching response (+ stream, for prompt).
        let id = msg.id.clone().unwrap_or(Value::Null);
        let method = msg.method.as_deref().unwrap_or("");
        match (&self.phase, method) {
            (Phase::Init, "initialize") => {
                self.outbox.push_back(RpcMessage::response(
                    id,
                    json!({
                        "protocolVersion": crate::acp_client::ACP_PROTOCOL_VERSION,
                        "agentInfo": { "name": "hermes-agent", "version": "mock" },
                        "agentCapabilities": { "loadSession": true },
                        "authMethods": []
                    }),
                ));
                self.phase = Phase::NewSession;
                Ok(())
            }
            (Phase::NewSession, "session/new") => {
                // Capture the model's tool source the client registered (the dregg
                // confined MCP server, when deep integration is wired).
                self.registered_mcp_servers = msg
                    .params
                    .as_ref()
                    .and_then(|p| p.get("mcpServers").cloned())
                    .unwrap_or(Value::Null);
                self.outbox.push_back(RpcMessage::response(
                    id,
                    json!({ "sessionId": self.session_id, "models": [], "modes": [] }),
                ));
                self.phase = Phase::Prompt;
                Ok(())
            }
            (_, "session/set_model") => {
                // The ACP unstable model-selection method. The live adapter
                // answers it with a benign `{}` result (and a session/update);
                // the mock mirrors that so `run_prompt_with_model` works against
                // either peer. Phase is unchanged (set_model is pre-prompt).
                self.outbox.push_back(RpcMessage::response(id, json!({})));
                Ok(())
            }
            (Phase::Prompt, "session/prompt") => {
                // Stream an opening message chunk, then begin the scripted calls.
                self.outbox.push_back(RpcMessage::notification(
                    "session/update",
                    json!({
                        "sessionId": self.session_id,
                        "update": {
                            "sessionUpdate": "agent_message_chunk",
                            "content": { "type": "text", "text": self.opening.clone() }
                        }
                    }),
                ));
                // Stash the prompt id; the PromptResponse is sent once the script
                // drains (see recv()).
                self.prompt_response_id = Some(id);
                if !self.queue_next_call() {
                    self.phase = Phase::Done;
                }
                Ok(())
            }
            _ => {
                // Unexpected; answer with an error response so the client doesn't wedge.
                self.outbox.push_back(RpcMessage::response(
                    id,
                    json!({ "error": format!("mock: unexpected {method} in this phase") }),
                ));
                Ok(())
            }
        }
    }

    fn recv(&mut self) -> Result<RpcMessage, AcpError> {
        // Hand out queued frames first.
        if let Some(msg) = self.outbox.pop_front() {
            return Ok(msg);
        }
        // Script drained and prompt outstanding → send the PromptResponse.
        if matches!(self.phase, Phase::Done)
            && let Some(id) = self.prompt_response_id.take()
        {
            return Ok(RpcMessage::response(
                id,
                json!({ "stopReason": "end_turn" }),
            ));
        }
        // Nothing left to say — the stream is closed.
        Err(AcpError::Closed)
    }
}
