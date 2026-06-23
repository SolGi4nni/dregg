//! THE LIVE ACP CLIENT ↔ HERMES SUBPROCESS — and a faithful mock peer.
//!
//! Hermes exposes itself over the **Agent Client Protocol** (ACP): JSON-RPC 2.0
//! over stdio, one JSON object per line (ndjson). deos is the ACP *client* (the
//! "editor" half): it drives `initialize` → `session/new` → `session/prompt`,
//! consumes the streamed `session/update` notifications, and — the load-bearing
//! seam — answers each `session/request_permission` REQUEST Hermes sends BACK by
//! running the tool-call through [`HermesGateway`](crate::HermesGateway) and
//! replying with the mapped `allow_once` / `deny` outcome.
//!
//! ## Live vs. mock — what runs end-to-end here, honestly
//!
//! The transport ([`AcpTransport`]) is REAL ndjson JSON-RPC and speaks to a live
//! `hermes-acp` subprocess (see [`AcpTransport::spawn_hermes`]). The live path is
//! WORKING: with a `hermes-acp` whose venv carries the `agent-client-protocol`
//! package, this client completes `initialize` → `session/new` →
//! `session/set_model` → `session/prompt` against the real Hermes ACP server, and
//! — when a model provider is reachable — Hermes issues a real
//! `session/request_permission` back, which [`AcpClient`] answers through the
//! [`HermesGateway`] (a cap-gated, receipted dregg turn). The
//! `tests/live_acp.rs` test (`--ignored`) and `cargo run -- live` drive exactly
//! this; `main.rs::run_live` reports how far the env let it get.
//!
//! The LIVE CEILING is the model provider: the Hermes agent loop needs provider
//! credentials (the install here advertises AWS Bedrock). With none, the provider
//! call fails inside Hermes before any tool-call is emitted — the
//! handshake/session still complete live, but no permission round-trip is
//! produced. With Bedrock credentials present, the full loop runs and the gateway
//! seam fires on the real `rm -rf` dangerous-command permission request.
//!
//! The default `cargo test` stays hermetic by driving the same client against a
//! [`MockHermesPeer`] that replays the REAL ACP message shapes Hermes's
//! `acp_adapter` emits (`initialize` response, `session/new` response,
//! `session/update` `tool_call` events, the `session/request_permission` request
//! with a real `ToolCallUpdate` payload, and a `PromptResponse` with a
//! `stop_reason`).
//!
//! The client half ([`AcpClient::run_prompt`]) is transport-agnostic: it drives
//! a [`AcpPeer`], so the SAME driver runs over the mock and over the live
//! subprocess. The seam (permission → gateway verdict) is exercised identically
//! in both.

use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

use crate::acp::{PermissionOutcome, ToolCallRequest};
use crate::bridge::HermesGateway;

/// The ACP protocol version deos's client advertises (mirrors
/// `acp.PROTOCOL_VERSION` Hermes's `initialize` echoes).
pub const ACP_PROTOCOL_VERSION: i64 = 1;

/// A JSON-RPC 2.0 message on the ACP wire — request, response, or notification.
/// Faithful to the ndjson framing ACP uses (one object per line).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RpcMessage {
    /// Always `"2.0"`.
    pub jsonrpc: String,
    /// Present on requests and responses; absent on notifications.
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub id: Option<Value>,
    /// Present on requests and notifications.
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub method: Option<String>,
    /// Present on requests and notifications.
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub params: Option<Value>,
    /// Present on a success response.
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub result: Option<Value>,
    /// Present on an error response.
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub error: Option<Value>,
}

impl RpcMessage {
    /// A client→peer request.
    pub fn request(id: i64, method: &str, params: Value) -> RpcMessage {
        RpcMessage {
            jsonrpc: "2.0".into(),
            id: Some(json!(id)),
            method: Some(method.into()),
            params: Some(params),
            result: None,
            error: None,
        }
    }

    /// A success response to a peer's request (`id` echoed).
    pub fn response(id: Value, result: Value) -> RpcMessage {
        RpcMessage {
            jsonrpc: "2.0".into(),
            id: Some(id),
            method: None,
            params: None,
            result: Some(result),
            error: None,
        }
    }

    /// A notification (no id).
    pub fn notification(method: &str, params: Value) -> RpcMessage {
        RpcMessage {
            jsonrpc: "2.0".into(),
            id: None,
            method: Some(method.into()),
            params: Some(params),
            result: None,
            error: None,
        }
    }

    /// Whether this is a peer→client REQUEST (has both `method` and `id`) — the
    /// shape `session/request_permission` arrives as.
    pub fn is_request(&self) -> bool {
        self.method.is_some() && self.id.is_some()
    }

    /// Whether this is a notification (has `method`, no `id`).
    pub fn is_notification(&self) -> bool {
        self.method.is_some() && self.id.is_none()
    }
}

/// A transport error (I/O, framing, or a closed peer).
#[derive(Debug)]
pub enum AcpError {
    /// The peer closed the stream (EOF) before the expected message.
    Closed,
    /// An I/O error on the transport.
    Io(std::io::Error),
    /// A malformed JSON frame.
    Parse(String),
    /// The peer answered with a JSON-RPC error.
    Peer(Value),
}

impl std::fmt::Display for AcpError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AcpError::Closed => write!(f, "ACP peer closed the stream"),
            AcpError::Io(e) => write!(f, "ACP transport I/O error: {e}"),
            AcpError::Parse(s) => write!(f, "ACP frame parse error: {s}"),
            AcpError::Peer(v) => write!(f, "ACP peer error: {v}"),
        }
    }
}

impl std::error::Error for AcpError {}

impl From<std::io::Error> for AcpError {
    fn from(e: std::io::Error) -> Self {
        AcpError::Io(e)
    }
}

/// An ACP peer the client exchanges JSON-RPC messages with — the Hermes side.
/// Implemented by both the live subprocess transport and the mock peer, so the
/// driver loop is identical over either.
pub trait AcpPeer {
    /// Send one JSON-RPC message TO the peer (client → Hermes).
    fn send(&mut self, msg: &RpcMessage) -> Result<(), AcpError>;
    /// Receive the next JSON-RPC message FROM the peer (Hermes → client),
    /// blocking until one is available or the stream closes.
    fn recv(&mut self) -> Result<RpcMessage, AcpError>;
}

/// The live ndjson JSON-RPC transport over a `hermes-acp` subprocess's stdio.
pub struct AcpTransport {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
}

impl AcpTransport {
    /// Spawn `hermes-acp` (the Hermes ACP stdio server, per
    /// `acp_registry/agent.json` distribution `uvx hermes-agent[acp] hermes-acp`,
    /// or a `hermes-acp` on `PATH`) and open the ndjson transport.
    ///
    /// This is the REAL live wiring: `hermes-acp` reaches `initialize` and a full
    /// session. The only env requirement is that its venv carries the
    /// `agent-client-protocol` package (`hermes-acp --check` prints "check OK");
    /// the agent loop additionally needs model-provider credentials to produce a
    /// tool-call (see the module docs on the live ceiling). `main.rs::run_live`
    /// and `tests/live_acp.rs` drive this path.
    pub fn spawn_hermes(program: &str, args: &[&str]) -> Result<AcpTransport, AcpError> {
        let mut child = Command::new(program)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()?;
        let stdin = child.stdin.take().ok_or(AcpError::Closed)?;
        let stdout = child.stdout.take().ok_or(AcpError::Closed)?;
        Ok(AcpTransport {
            child,
            stdin,
            stdout: BufReader::new(stdout),
        })
    }
}

impl Drop for AcpTransport {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

impl AcpPeer for AcpTransport {
    fn send(&mut self, msg: &RpcMessage) -> Result<(), AcpError> {
        let line = serde_json::to_string(msg).map_err(|e| AcpError::Parse(e.to_string()))?;
        self.stdin.write_all(line.as_bytes())?;
        self.stdin.write_all(b"\n")?;
        self.stdin.flush()?;
        Ok(())
    }

    fn recv(&mut self) -> Result<RpcMessage, AcpError> {
        let mut line = String::new();
        loop {
            line.clear();
            let n = self.stdout.read_line(&mut line)?;
            if n == 0 {
                return Err(AcpError::Closed);
            }
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }
            return serde_json::from_str(trimmed).map_err(|e| AcpError::Parse(e.to_string()));
        }
    }
}

/// The result of driving a prompt: the streamed agent text, the tool-calls seen,
/// and the gateway verdicts deos returned for each permission request.
#[derive(Clone, Debug, Default)]
pub struct PromptRun {
    /// The agent's streamed message text (concatenated `agent_message_chunk`s).
    pub agent_text: String,
    /// Every tool-call deos saw (from `session/update` `tool_call` events).
    pub tool_calls: Vec<ToolCallRequest>,
    /// The verdict deos returned for each `session/request_permission`, paired
    /// with the tool-call it answered. These are the receipted turns / refusals.
    pub verdicts: Vec<(ToolCallRequest, PermissionOutcome)>,
    /// The `stop_reason` from the final `PromptResponse`.
    pub stop_reason: String,
}

/// THE ACP CLIENT — deos's editor-half driver over an [`AcpPeer`].
///
/// Holds the [`HermesGateway`] it answers `session/request_permission` with, and
/// the request id counter for client→peer requests. Transport-agnostic: the same
/// driver runs over the live subprocess or the mock peer.
pub struct AcpClient<'rt, P: AcpPeer> {
    peer: P,
    gateway: HermesGateway<'rt>,
    next_id: i64,
    /// The presentation clock/height deos stamps each permission turn at. In a
    /// real deployment this is the dregg block height; the driver bumps it per
    /// permission so each receipted turn has a monotonic time.
    clock: i64,
}

impl<'rt, P: AcpPeer> AcpClient<'rt, P> {
    /// Open a client over `peer`, answering permission requests via `gateway`,
    /// stamping turns from `start_clock`.
    pub fn new(peer: P, gateway: HermesGateway<'rt>, start_clock: i64) -> AcpClient<'rt, P> {
        AcpClient {
            peer,
            gateway,
            next_id: 1,
            clock: start_clock,
        }
    }

    /// The gateway (post-run, for the mandate inspector).
    pub fn gateway(&self) -> &HermesGateway<'rt> {
        &self.gateway
    }

    fn alloc_id(&mut self) -> i64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Send a request and block for its matching response, servicing any
    /// interleaved peer→client REQUESTS (notably `session/request_permission`)
    /// and consuming notifications, until the response with our id arrives.
    fn request_blocking(
        &mut self,
        method: &str,
        params: Value,
        run: &mut PromptRun,
    ) -> Result<Value, AcpError> {
        let id = self.alloc_id();
        self.peer.send(&RpcMessage::request(id, method, params))?;
        loop {
            let msg = self.peer.recv()?;
            // Our response?
            if msg.result.is_some() || msg.error.is_some() {
                if msg.id == Some(json!(id)) {
                    if let Some(err) = msg.error {
                        return Err(AcpError::Peer(err));
                    }
                    return Ok(msg.result.unwrap_or(Value::Null));
                }
                // A response to a different in-flight request — ignore here.
                continue;
            }
            // A peer→client request (the permission seam) or a notification.
            if msg.is_request() {
                self.handle_peer_request(&msg, run)?;
            } else if msg.is_notification() {
                self.handle_notification(&msg, run);
            }
        }
    }

    /// Handle a peer→client REQUEST. The load-bearing one is
    /// `session/request_permission`: deos answers it with the gateway verdict.
    fn handle_peer_request(
        &mut self,
        msg: &RpcMessage,
        run: &mut PromptRun,
    ) -> Result<(), AcpError> {
        let id = msg.id.clone().expect("a request has an id");
        let method = msg.method.as_deref().unwrap_or("");
        match method {
            "session/request_permission" => {
                let params = msg.params.clone().unwrap_or(Value::Null);
                let call = parse_permission_tool_call(&params);
                // THE SEAM — run the tool-call through the gateway. Side-effect
                // rides the metered turn; verdict maps to the ACP outcome.
                self.clock += 1;
                let outcome = self.gateway.admit_call(&call, self.clock);
                run.verdicts.push((call.clone(), outcome.clone()));
                let result = permission_outcome_to_acp(&outcome);
                self.peer.send(&RpcMessage::response(id, result))?;
                Ok(())
            }
            // Any other client-side request Hermes might make (fs/read_text_file,
            // terminal/create, …): deny-by-default with a JSON-RPC-shaped result
            // so the loop never wedges. (A full client would service these.)
            other => {
                let result = json!({ "error": format!("unsupported client method: {other}") });
                self.peer.send(&RpcMessage::response(id, result))?;
                Ok(())
            }
        }
    }

    /// Consume a `session/update` notification, accumulating agent text and
    /// tool-call events into the run.
    fn handle_notification(&mut self, msg: &RpcMessage, run: &mut PromptRun) {
        if msg.method.as_deref() != Some("session/update") {
            return;
        }
        let Some(params) = &msg.params else { return };
        let update = params.get("update").unwrap_or(params);
        let kind = update
            .get("sessionUpdate")
            .or_else(|| update.get("session_update"))
            .and_then(|v| v.as_str())
            .unwrap_or("");
        match kind {
            "agent_message_chunk" => {
                if let Some(text) = update
                    .get("content")
                    .and_then(|c| c.get("text"))
                    .and_then(|t| t.as_str())
                {
                    run.agent_text.push_str(text);
                }
            }
            "tool_call" | "tool_call_update" => {
                if let Some(call) = parse_tool_call_update(params, update) {
                    run.tool_calls.push(call);
                }
            }
            _ => {}
        }
    }

    /// Drive a full prompt turn: `initialize` → `session/new` → `session/prompt`,
    /// answering every permission request via the gateway, returning the run.
    pub fn run_prompt(&mut self, cwd: &str, prompt: &str) -> Result<PromptRun, AcpError> {
        self.run_prompt_with_model(cwd, prompt, None)
    }

    /// As [`AcpClient::run_prompt`], but selecting an explicit model before the
    /// prompt via `session/set_model` (the ACP unstable model-selection method).
    ///
    /// This matters for the LIVE `hermes-acp` subprocess: the model advertised at
    /// `session/new` does not always propagate to the provider call (the live
    /// adapter sends an empty `modelId` to Bedrock otherwise — `Invalid length
    /// for parameter modelId`), so an explicit `session/set_model` is what makes
    /// the live agent loop actually reach the provider. The mock peer answers
    /// `session/set_model` as a benign no-op result, so passing a model is
    /// harmless there. Pass `None` to skip model selection (the default).
    pub fn run_prompt_with_model(
        &mut self,
        cwd: &str,
        prompt: &str,
        model_id: Option<&str>,
    ) -> Result<PromptRun, AcpError> {
        let mut run = PromptRun::default();

        // 1. initialize — advertise the client + protocol version.
        let _init = self.request_blocking(
            "initialize",
            json!({
                "protocolVersion": ACP_PROTOCOL_VERSION,
                "clientCapabilities": { "fs": { "readTextFile": false, "writeTextFile": false } },
                "clientInfo": { "name": "deos-hermes", "version": "0.1.0" }
            }),
            &mut run,
        )?;

        // 2. session/new — open a session in `cwd`.
        let new_session = self.request_blocking(
            "session/new",
            json!({ "cwd": cwd, "mcpServers": [] }),
            &mut run,
        )?;
        let session_id = new_session
            .get("sessionId")
            .or_else(|| new_session.get("session_id"))
            .and_then(|v| v.as_str())
            .unwrap_or("sess-0")
            .to_string();

        // 2b. session/set_model — pin the provider model for the live loop. Best
        //     effort: a peer that does not support it answers with a JSON-RPC
        //     error, which we tolerate (the mock answers a benign result).
        if let Some(model_id) = model_id {
            let _ = self.request_blocking(
                "session/set_model",
                json!({ "sessionId": session_id, "modelId": model_id }),
                &mut run,
            );
        }

        // 3. session/prompt — send the user's prompt; Hermes streams updates and
        //    issues permission requests, which the blocking loop services.
        let prompt_result = self.request_blocking(
            "session/prompt",
            json!({
                "sessionId": session_id,
                "prompt": [ { "type": "text", "text": prompt } ]
            }),
            &mut run,
        )?;
        run.stop_reason = prompt_result
            .get("stopReason")
            .or_else(|| prompt_result.get("stop_reason"))
            .and_then(|v| v.as_str())
            .unwrap_or("end_turn")
            .to_string();

        Ok(run)
    }
}

/// Map a deos [`PermissionOutcome`] to the ACP `RequestPermissionResponse`
/// (`{ outcome: { outcome: "selected", optionId: "allow_once" | "deny" } }`),
/// the shape `acp_adapter/permissions.py::_map_outcome_to_hermes` consumes.
pub fn permission_outcome_to_acp(outcome: &PermissionOutcome) -> Value {
    let option_id = outcome.acp_option_id();
    let mut sel = json!({ "outcome": "selected", "optionId": option_id });
    // deos's extension: carry the receipt / refusal reason so the editor surface
    // (and Hermes's trajectory) sees exactly which mandate leg decided.
    match outcome {
        PermissionOutcome::Allow {
            receipt, remaining, ..
        } => {
            sel["deosReceipt"] = json!(receipt);
            sel["deosRemaining"] = json!(remaining);
        }
        PermissionOutcome::Reject { reason, .. } => {
            sel["deosRefusal"] = json!(reason);
        }
    }
    json!({ "outcome": sel })
}

/// Parse a [`ToolCallRequest`] from a `session/request_permission` params blob
/// (which carries a `toolCall` `ToolCallUpdate` with `toolCallId`, `kind`,
/// `rawInput`, and a `title`/`content` — the
/// `acp_adapter/permissions.py::_build_permission_tool_call` shape).
pub fn parse_permission_tool_call(params: &Value) -> ToolCallRequest {
    let session_id = params
        .get("sessionId")
        .or_else(|| params.get("session_id"))
        .and_then(|v| v.as_str())
        .unwrap_or("sess-0");
    let tc = params
        .get("toolCall")
        .or_else(|| params.get("tool_call"))
        .cloned()
        .unwrap_or(Value::Null);
    let tool_call_id = tc
        .get("toolCallId")
        .or_else(|| tc.get("tool_call_id"))
        .and_then(|v| v.as_str())
        .unwrap_or("tc-0");
    let raw_input = tc
        .get("rawInput")
        .or_else(|| tc.get("raw_input"))
        .cloned()
        .unwrap_or(Value::Null);
    // Prefer an explicit tool name if present; else infer from rawInput shape
    // (the permission update for a dangerous command carries {command,…}).
    let name = tc
        .get("toolName")
        .or_else(|| tc.get("tool_name"))
        .and_then(|v| v.as_str())
        .map(|s| s.to_string())
        .unwrap_or_else(|| infer_tool_name(&tc, &raw_input));
    ToolCallRequest::new(session_id, tool_call_id, name, raw_input)
}

/// Parse a [`ToolCallRequest`] from a `session/update` `tool_call` notification.
fn parse_tool_call_update(params: &Value, update: &Value) -> Option<ToolCallRequest> {
    let session_id = params
        .get("sessionId")
        .or_else(|| params.get("session_id"))
        .and_then(|v| v.as_str())
        .unwrap_or("sess-0");
    let tool_call_id = update
        .get("toolCallId")
        .or_else(|| update.get("tool_call_id"))
        .and_then(|v| v.as_str())?;
    let raw_input = update
        .get("rawInput")
        .or_else(|| update.get("raw_input"))
        .cloned()
        .unwrap_or(Value::Null);
    let name = update
        .get("toolName")
        .or_else(|| update.get("tool_name"))
        .and_then(|v| v.as_str())
        .map(|s| s.to_string())
        .unwrap_or_else(|| infer_tool_name(update, &raw_input));
    Some(ToolCallRequest::new(session_id, tool_call_id, name, raw_input))
}

/// Best-effort tool-name inference when the ACP wire omits an explicit name
/// (the permission `ToolCallUpdate` carries `kind` + `rawInput`, not always a
/// name). Maps the kind + arg shape to a representative Hermes tool name.
fn infer_tool_name(tc: &Value, raw_input: &Value) -> String {
    let kind = tc
        .get("kind")
        .and_then(|v| v.as_str())
        .unwrap_or("other");
    if raw_input.get("command").is_some() {
        return "terminal".to_string();
    }
    if raw_input.get("path").is_some() && raw_input.get("content").is_some() {
        return "write_file".to_string();
    }
    if raw_input.get("query").is_some() {
        return "web_search".to_string();
    }
    match kind {
        "execute" => "terminal".to_string(),
        "edit" => "write_file".to_string(),
        "fetch" => "web_search".to_string(),
        "read" => "read_file".to_string(),
        "search" => "search_files".to_string(),
        _ => "unknown_tool".to_string(),
    }
}
