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
use serde_json::{Value, json};

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

/// A live delta from a driven prompt — the unit the streaming dock consumes as
/// it arrives, so the UX paints token-by-token rather than after the run.
///
/// The same loop that produces a [`PromptRun`] emits these in order: the session
/// opens, agent text chunks stream in, each tool-call appears, the gateway's
/// verdict on that call lands the instant the gate decides, and the turn stops.
#[derive(Clone, Debug)]
pub enum StreamEvent {
    /// The `session/new` handshake completed; the session id is known.
    SessionStarted { session_id: String },
    /// A streamed `agent_message_chunk` — append this text to the chat pane.
    AgentChunk { text: String },
    /// A `session/update` `tool_call` event — the agent is reaching for a tool
    /// (before the gate has decided). Surfaces the call in-flight.
    ToolCall { call: ToolCallRequest },
    /// The gateway's verdict on a `session/request_permission` — ALLOW (a
    /// receipted turn, with remaining budget) or REJECT (the leg that bit). This
    /// is the permission moment, surfaced the instant `HermesGateway` decides.
    Verdict {
        call: ToolCallRequest,
        outcome: PermissionOutcome,
    },
    /// The prompt's terminal `stop_reason`; the turn is complete.
    Stopped { stop_reason: String },
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

/// The outcome of executing a model-chosen `run_js` script against a live World
/// (the hands-on-glass side-effect of a `run_js` permission request). Carried back
/// out of [`AcpClient`] so the caller can show the receipts the brain's JS landed.
#[derive(Clone, Debug, Default)]
pub struct JsRunRecord {
    /// The ACP tool-call id the `run_js` answered (correlation back to the call).
    pub tool_call_id: String,
    /// The exact script the model chose (from the tool-call's `rawInput.script`).
    pub script: String,
    /// The script's i32 completion value, if it produced one.
    pub result: Option<i32>,
    /// How many affordance fires committed a real verified turn on the live World.
    pub fires_committed: usize,
    /// The receipt hashes the brain's JS left on the live ledger, in order.
    pub receipts: Vec<[u8; 32]>,
    /// A JS eval fault (NOT a cap-gate refusal — a refusal is an in-band `-1`).
    pub js_error: Option<String>,
}

/// A hook that executes a model-chosen `run_js` script against the LIVE World and
/// returns both the verdict deos sends back over ACP AND a record of what the JS
/// did (the receipts it landed). Set with [`AcpClient::with_run_js_hook`].
///
/// The hook owns the live `WorldSink` + the agent's `RunJsTool` + the process-global
/// `JsRuntime` (see `crate::live_js::LiveJsHands`). It is invoked from
/// [`AcpClient::handle_peer_request`] the instant a `run_js` permission request
/// arrives, so the brain's JS lands on the cockpit glass exactly when the gate
/// admits the tool-call.
pub type RunJsHook<'h> =
    Box<dyn FnMut(&ToolCallRequest, i64) -> (PermissionOutcome, JsRunRecord) + 'h>;

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
    /// An optional `run_js` execution hook. When set, a `run_js` permission request
    /// (the brain's hands on the glass) is dispatched here — the model's chosen
    /// script runs against the live World and the receipts it landed are recorded.
    /// When unset, `run_js` is gated like any other tool (the metered turn only).
    run_js_hook: Option<RunJsHook<'rt>>,
    /// The records of every `run_js` the hook executed this run (the brain's
    /// hands-on-glass tape — the scripts it chose + the receipts they landed).
    js_runs: Vec<JsRunRecord>,
    /// The `mcpServers` deos registers on `session/new` — the model's tool
    /// source. When this carries the dregg confined MCP server (and ONLY it), the
    /// model has no unconfined tool path: every tool it calls (`run_js`,
    /// `terminal`) routes to that server (the dregg sandbox). Empty by default
    /// (the historical `session/new` with no extra tool sources).
    mcp_servers: Vec<Value>,
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
            run_js_hook: None,
            js_runs: Vec::new(),
            mcp_servers: Vec::new(),
        }
    }

    /// Register the dregg confined stdio MCP server as the model's tool source on
    /// `session/new` — the DEEP-INTEGRATION wire. `command`/`args`/`env` describe
    /// the binary Hermes spawns (e.g. `deos-hermes mcp-server`); once registered,
    /// the model's tools are exactly the ones THAT server advertises (`run_js`,
    /// `terminal`), so every tool-call routes through the dregg sandbox. Builder
    /// style; call once with the dregg server (and ONLY it) for full confinement.
    ///
    /// The shape is the ACP `McpServerStdio` (`acp_adapter/server.py
    /// ::_register_session_mcp_servers` consumes `{name, command, args, env}`).
    pub fn with_dregg_mcp_server(
        mut self,
        name: &str,
        command: &str,
        args: &[&str],
        env: &[(&str, &str)],
    ) -> Self {
        self.mcp_servers.push(json!({
            "name": name,
            "command": command,
            "args": args,
            "env": env.iter().map(|(n, v)| json!({ "name": n, "value": v })).collect::<Vec<_>>(),
        }));
        self
    }

    /// The `mcpServers` deos will register on `session/new` (the model's tool
    /// source). Empty unless [`AcpClient::with_dregg_mcp_server`] registered one.
    pub fn mcp_servers(&self) -> &[Value] {
        &self.mcp_servers
    }

    /// Install a `run_js` execution hook (the brain's HANDS ON THE GLASS). With it
    /// set, a `run_js` permission request carrying the model's chosen `script` is
    /// dispatched to `hook`, which runs that JS against the LIVE World and returns
    /// the verdict + the receipts it landed. Builder-style; returns `self`.
    pub fn with_run_js_hook(mut self, hook: RunJsHook<'rt>) -> Self {
        self.run_js_hook = Some(hook);
        self
    }

    /// The records of every `run_js` the brain drove this run (script + receipts).
    pub fn js_runs(&self) -> &[JsRunRecord] {
        &self.js_runs
    }

    /// The gateway (post-run, for the mandate inspector).
    pub fn gateway(&self) -> &HermesGateway<'rt> {
        &self.gateway
    }

    /// The peer (post-run) — e.g. to read what a [`crate::MockHermesPeer`]
    /// captured (the `mcpServers` deos registered on `session/new`).
    pub fn peer(&self) -> &P {
        &self.peer
    }

    /// Consume the client, returning the (spent) gateway — for a caller that
    /// drove one prompt over a moved-in gateway and wants it back (the live dock
    /// reclaims the gateway between turns so budgets persist).
    pub fn into_gateway(self) -> HermesGateway<'rt> {
        self.gateway
    }

    fn alloc_id(&mut self) -> i64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Send a request and block for its matching response, servicing any
    /// interleaved peer→client REQUESTS (notably `session/request_permission`)
    /// and consuming notifications, until the response with our id arrives.
    /// Every delta seen along the way is fed to `sink` so a live UX can paint it
    /// as it arrives (the same deltas are accumulated into `run`).
    fn request_blocking(
        &mut self,
        method: &str,
        params: Value,
        run: &mut PromptRun,
        sink: &mut dyn FnMut(StreamEvent),
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
                self.handle_peer_request(&msg, run, sink)?;
            } else if msg.is_notification() {
                self.handle_notification(&msg, run, sink);
            }
        }
    }

    /// Handle a peer→client REQUEST. The load-bearing one is
    /// `session/request_permission`: deos answers it with the gateway verdict.
    fn handle_peer_request(
        &mut self,
        msg: &RpcMessage,
        run: &mut PromptRun,
        sink: &mut dyn FnMut(StreamEvent),
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
                // HANDS ON THE GLASS: a `run_js` call with a hook installed is
                // dispatched to the hook, which (a) runs the gateway accountability
                // turn AND (b) executes the model's chosen JS against the LIVE
                // World, landing real verified turns on the cockpit ledger. The
                // record (script + receipts) is kept for the caller to surface.
                let outcome = match self.run_js_hook.as_mut() {
                    Some(hook) if call.name == "run_js" => {
                        let now = self.clock;
                        let (outcome, record) = hook(&call, now);
                        self.js_runs.push(record);
                        outcome
                    }
                    _ => self.gateway.admit_call(&call, self.clock),
                };
                run.verdicts.push((call.clone(), outcome.clone()));
                // The permission moment — surfaced the instant the gate decides.
                sink(StreamEvent::Verdict {
                    call,
                    outcome: outcome.clone(),
                });
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
    /// tool-call events into the run AND emitting the matching live delta.
    fn handle_notification(
        &mut self,
        msg: &RpcMessage,
        run: &mut PromptRun,
        sink: &mut dyn FnMut(StreamEvent),
    ) {
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
                    sink(StreamEvent::AgentChunk {
                        text: text.to_string(),
                    });
                }
            }
            "tool_call" | "tool_call_update" => {
                if let Some(call) = parse_tool_call_update(params, update) {
                    // Only the initial `tool_call` start carries a fresh call to
                    // surface in-flight; the post-decision `tool_call_update`
                    // (status completed/failed) is a status echo we don't re-list.
                    if kind == "tool_call" {
                        sink(StreamEvent::ToolCall { call: call.clone() });
                    }
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

    /// As [`AcpClient::run_prompt`], but streaming each delta to `sink` as it
    /// arrives — the live entry the interactive dock drives. The `sink` sees the
    /// session open, every agent text chunk, every tool-call, and every gateway
    /// verdict the instant the gate decides, then the stop. The same deltas are
    /// accumulated into the returned [`PromptRun`].
    pub fn run_prompt_streaming(
        &mut self,
        cwd: &str,
        prompt: &str,
        model_id: Option<&str>,
        sink: &mut dyn FnMut(StreamEvent),
    ) -> Result<PromptRun, AcpError> {
        self.drive_prompt(cwd, prompt, model_id, sink)
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
        // The non-streaming path is the streaming path with a no-op sink.
        self.drive_prompt(cwd, prompt, model_id, &mut |_| {})
    }

    /// The one driver loop both [`AcpClient::run_prompt_with_model`] and
    /// [`AcpClient::run_prompt_streaming`] share. Every delta is both accumulated
    /// into the returned [`PromptRun`] AND handed to `sink` as it arrives.
    fn drive_prompt(
        &mut self,
        cwd: &str,
        prompt: &str,
        model_id: Option<&str>,
        sink: &mut dyn FnMut(StreamEvent),
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
            sink,
        )?;

        // 2. session/new — open a session in `cwd`, registering deos's confined
        //    MCP server(s) as the model's tool source. When the dregg server is
        //    registered (and ONLY it), the model's tools are exactly the ones it
        //    advertises (`run_js`, `terminal`) — every tool-call routes through
        //    the dregg sandbox; the model has no unconfined tool path.
        let new_session = self.request_blocking(
            "session/new",
            json!({ "cwd": cwd, "mcpServers": self.mcp_servers.clone() }),
            &mut run,
            sink,
        )?;
        let session_id = new_session
            .get("sessionId")
            .or_else(|| new_session.get("session_id"))
            .and_then(|v| v.as_str())
            .unwrap_or("sess-0")
            .to_string();
        sink(StreamEvent::SessionStarted {
            session_id: session_id.clone(),
        });

        // 2b. session/set_model — pin the provider model for the live loop. Best
        //     effort: a peer that does not support it answers with a JSON-RPC
        //     error, which we tolerate (the mock answers a benign result).
        if let Some(model_id) = model_id {
            let _ = self.request_blocking(
                "session/set_model",
                json!({ "sessionId": session_id, "modelId": model_id }),
                &mut run,
                sink,
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
            sink,
        )?;
        run.stop_reason = prompt_result
            .get("stopReason")
            .or_else(|| prompt_result.get("stop_reason"))
            .and_then(|v| v.as_str())
            .unwrap_or("end_turn")
            .to_string();
        sink(StreamEvent::Stopped {
            stop_reason: run.stop_reason.clone(),
        });

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
    Some(ToolCallRequest::new(
        session_id,
        tool_call_id,
        name,
        raw_input,
    ))
}

/// Best-effort tool-name inference when the ACP wire omits an explicit name
/// (the permission `ToolCallUpdate` carries `kind` + `rawInput`, not always a
/// name). Maps the kind + arg shape to a representative Hermes tool name.
fn infer_tool_name(tc: &Value, raw_input: &Value) -> String {
    let kind = tc.get("kind").and_then(|v| v.as_str()).unwrap_or("other");
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
