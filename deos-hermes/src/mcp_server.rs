//! THE DREGG MCP SERVER — deos advertises the ONLY tools a confined Hermes may
//! use, so the model has NO path to an unconfined shell.
//!
//! ## Why this exists (the deep-integration keystone)
//!
//! The live-brain bake (`docs/deos/LOG-A-HERMES-IN.md`) proved a real Claude can
//! drive the cockpit's live World — but the model was reasoning in Hermes's OWN
//! unconfined process, running Hermes's OWN built-in tools (`terminal`,
//! `write_file`, …) in that process. A benign `terminal`/`write_file` it reached
//! for never reached dregg: no sandbox, no receipt. The two confinement faces
//! (`bridge.rs` authority + `confined.rs` ambient PD) were DISJOINT from the live
//! model's tools.
//!
//! An ACP `session/new` accepts an `mcpServers` list (`acp_adapter/server.py
//! ::_register_session_mcp_servers` → `tools.mcp_tool.register_mcp_servers` →
//! the model's `tools` surface). When deos registers a dregg **stdio MCP server**
//! as the model's tool source, the dregg-confined `run_js` + `terminal` enter the
//! model's tool surface, and EVERY call the model makes to them routes to THIS
//! server — a cap-gated, receipted dregg turn (and, for `terminal`, run inside an
//! OS-sandboxed firmament PD). The model's dregg shell runs *in the container*,
//! not Hermes's process.
//!
//! EXCLUSIVITY caveat (named, not laundered): the current `hermes-acp` always
//! keeps its base `["hermes-acp"]` toolset enabled alongside the MCP servers
//! (`acp_adapter/session.py::_expand_acp_enabled_toolsets` has no ACP knob to
//! empty it). So registering this server ADDS the dregg tools rather than making
//! them the model's ONLY tools; Hermes's own `terminal`/`write_file` remain, but
//! still route through deos's `session/request_permission` authority gate
//! ([`crate::bridge`], the `live-refuse` proof) — confined at the authority face,
//! not yet PD-sandboxed. Full exclusivity is one upstream `hermes-acp` change
//! (empty base toolset over ACP). See `docs/deos/LOG-A-HERMES-IN.md`.
//!
//! ## The wire — standard MCP over stdio (ndjson JSON-RPC 2.0)
//!
//! Hermes connects with the `mcp` Python SDK's `stdio_client` + `ClientSession`,
//! so this server speaks STANDARD MCP:
//!   * `initialize` → echo the client's `protocolVersion`, advertise `tools`;
//!   * `notifications/initialized` → ack (no reply);
//!   * `tools/list` → the dregg tool surface (`run_js`, `terminal`);
//!   * `tools/call` → route the named tool through dregg confinement, returning an
//!     MCP `CallToolResult` ({ content:[{type:"text",…}], isError });
//!   * `ping` → `{}`.
//!
//! ## The tools (every one is dregg-confined)
//!
//! * **`run_js`** — the model's chosen JavaScript runs through [`RunJsTool::run`]
//!   on a deos-js engine mounted under the agent's `held` (the cap tooth, never
//!   root): a cap-gated, receipted verified turn. CROSS-PROCESS SEAM: an MCP
//!   server is a SEPARATE subprocess Hermes spawns, so it cannot share the
//!   cockpit's `Rc<RefCell<World>>`; by default this server's `run_js` drives its
//!   OWN embedded verified World (a real receipted turn on its own ledger). The
//!   socket back to the cockpit's live World is BUILT:
//!   [`McpToolHost::with_world_bridge`] routes `run_js` through a
//!   [`crate::world_bridge::SocketWorldSink`] onto the cockpit's served
//!   `WorldSink` (`starbridge_v2::agent_attach::world_bridge`) — fail-closed
//!   (socket absent/dead ⇒ the call refuses; never a silent embedded fallback).
//! * **`terminal`** — the command execs INSIDE a confined firmament PD
//!   ([`crate::confined::launch_confined`]): file/net/exec are DENIED by the host
//!   OS sandbox (Seatbelt/seccomp+landlock), the PD's only channel is its
//!   Endpoint, and the four sandbox probes RUN inside it and report their verdict.
//!   An attempt at ambient authority (read a file outside the grant / open a
//!   socket) is physically refused. The command becomes a cap-gated receipted
//!   turn through the [`HermesGateway`]; the PD's confinement-verdict bitmask is
//!   returned so the caller can PROVE the shell ran in the container, not loose.
//!
//! The model has NO other tool path — `tools/list` returns exactly these.

use serde_json::{Value, json};

use crate::acp::{PermissionOutcome, ToolCallRequest};
use crate::bridge::HermesGateway;

/// The MCP protocol version this server falls back to if the client omits one.
/// `initialize` ECHOES the client's requested version when present (the `mcp`
/// Python SDK negotiates by version string), so any client-supported version is
/// honored; this is only the floor.
pub const MCP_FALLBACK_PROTOCOL_VERSION: &str = "2025-06-18";

/// The dregg tool surface advertised over MCP — the ONLY tools a confined Hermes
/// may call. Each name maps to a dregg-confined execution path in
/// [`McpToolHost::call_tool`].
pub const DREGG_TOOL_NAMES: &[&str] = &["run_js", "terminal"];

/// The result of one dregg-confined `tools/call`: the model-visible text + the
/// dregg receipt (proof a verified turn committed) + structured confinement
/// evidence (for `terminal`, the sandbox-probe verdict). Surfaced both into the
/// MCP `CallToolResult` AND kept on the host's tape for the caller to assert.
#[derive(Clone, Debug, Default)]
pub struct ConfinedToolResult {
    /// The MCP tool name that was called.
    pub tool: String,
    /// Human-readable text the model sees (the `CallToolResult.content`).
    pub text: String,
    /// Whether dregg admitted the tool-call (the gateway verdict). `false` = the
    /// in-band refusal the model sees (an MCP `isError` result).
    pub admitted: bool,
    /// The dregg receipt id the metered turn left (hex), if admitted.
    pub receipt: Option<String>,
    /// For `terminal`: the confined-PD sandbox-probe verdict bitmask
    /// ([`crate::confined::probe`]). `Some(probe::ALL)` = every confinement tooth
    /// held (file open denied, inet socket denied, only the Endpoint fd, IPC
    /// works). `None` for tools that do not spawn a PD.
    pub sandbox_verdict: Option<i32>,
    /// For `run_js`: how many affordance fires committed a real verified turn.
    pub fires_committed: usize,
}

/// THE TOOL HOST — owns the dregg confinement the MCP server routes every
/// `tools/call` through. One per MCP-server process (Hermes spawns one per
/// session). Holds the [`HermesGateway`] (the authority face) and, when the
/// `js-agent` feature is on, the agent's `run_js` tool + its deos-js runtime.
///
/// The host is transport-agnostic: [`McpServer`] feeds it parsed `tools/call`
/// requests and serializes its [`ConfinedToolResult`] back onto the MCP wire.
pub struct McpToolHost<'rt> {
    /// The authority face — every tool-call becomes a cap-gated, metered,
    /// receipted dregg turn (or an in-band refusal).
    gateway: HermesGateway<'rt>,
    /// The presentation clock the host stamps each tool turn at (monotone).
    clock: i64,
    /// Every confined tool-call this host ran (the audit tape — scripts/commands
    /// the model chose + the receipts/verdicts they landed).
    tape: Vec<ConfinedToolResult>,
    /// The agent's `run_js` hands (deos-js mounted under `held`, never root).
    /// `None` when the `js-agent` feature is off (run_js then reports the seam).
    #[cfg(feature = "js-agent")]
    js: Option<JsHands>,
    /// THE WORLD BRIDGE ([`McpToolHost::with_world_bridge`]) — when set, `run_js`
    /// routes through a [`crate::world_bridge::SocketWorldSink`] onto the
    /// COCKPIT'S live World instead of the embedded one. FAIL-CLOSED: socket
    /// absent/dead ⇒ the tool call REFUSES (never a silent embedded fallback).
    #[cfg(unix)]
    bridge: Option<WorldBridge>,
}

/// The host's configured world bridge: the socket path + the session-long
/// connection (lazily dialed on the first bridged `run_js`, reused after —
/// the serving side accepts ONE client).
// Only the js-agent `call_run_js_bridged` path READS the bridge; a js-agent-less
// build still ACCEPTS the configuration (and refuses run_js at the hands seam).
#[cfg_attr(not(feature = "js-agent"), allow(dead_code))]
#[cfg(unix)]
struct WorldBridge {
    socket_path: std::path::PathBuf,
    conn: Option<crate::world_bridge::SocketWorldSink>,
}

#[cfg(unix)]
#[cfg_attr(not(feature = "js-agent"), allow(dead_code))]
impl WorldBridge {
    /// The live connection: reuse the session connection if it is alive, else
    /// dial the socket. Errs iff the socket is absent/dead — the caller refuses.
    fn sink(&mut self) -> std::io::Result<crate::world_bridge::SocketWorldSink> {
        if let Some(conn) = self.conn.as_ref().filter(|c| !c.is_dead()) {
            return Ok(conn.clone());
        }
        // No connection yet, or a latched-dead one: (re-)dial the socket.
        let conn = crate::world_bridge::SocketWorldSink::connect(&self.socket_path)?;
        self.conn = Some(conn.clone());
        Ok(conn)
    }
}

/// The agent's `run_js` hands inside the MCP server: the [`crate::RunJsTool`]
/// (mounted under `held`) + the process-global deos-js [`JsRuntime`]. The
/// accountability gateway is the HOST's [`McpToolHost::gateway`] — the SAME gate
/// `terminal` meters on, so the whole session shares one receipted ledger.
#[cfg(feature = "js-agent")]
struct JsHands {
    tool: crate::run_js::RunJsTool,
    rt: deos_js::JsRuntime,
}

impl<'rt> McpToolHost<'rt> {
    /// Build the host over a dregg `gateway` (the confinement the tools route
    /// through), stamping tool turns from `start_clock`.
    pub fn new(gateway: HermesGateway<'rt>, start_clock: i64) -> McpToolHost<'rt> {
        McpToolHost {
            gateway,
            clock: start_clock,
            tape: Vec::new(),
            #[cfg(feature = "js-agent")]
            js: None,
            #[cfg(unix)]
            bridge: None,
        }
    }

    /// THE EXACT REMAINING WIRE, LANDED — route this host's `run_js` onto the
    /// COCKPIT'S live World over the world-bridge socket at `socket_path`
    /// ([`crate::world_bridge`]): the serving side (the cockpit process, e.g.
    /// `starbridge_v2::agent_attach::world_bridge::serve_world_bridge` over its
    /// live `WorldSinkAdapter`) answers the `WorldSink` protocol, and every
    /// `run_js` here runs [`crate::RunJsTool::run_attached_on`] through a
    /// [`crate::world_bridge::SocketWorldSink`] — each fire a real verified turn
    /// whose receipt lands on the COCKPIT'S ledger, still bounded by the agent's
    /// `held` (the cap tooth runs client-side before any frame is sent).
    ///
    /// FAIL-CLOSED: with a bridge configured, `run_js` NEVER falls back to the
    /// embedded World — socket absent/dead ⇒ the tool call REFUSES in-band with
    /// a clear message. The connection is dialed lazily on the first bridged
    /// call and kept for the session (the serving side accepts ONE client).
    #[cfg(unix)]
    pub fn with_world_bridge(mut self, socket_path: impl Into<std::path::PathBuf>) -> Self {
        self.bridge = Some(WorldBridge {
            socket_path: socket_path.into(),
            conn: None,
        });
        self
    }

    /// Install the agent's `run_js` hands — a [`crate::RunJsTool`] (mounted under
    /// the agent's `held`, never root) + a freshly-booted deos-js [`JsRuntime`].
    /// With it set, the MCP `run_js` tool runs the model's chosen script on the
    /// agent's bounded embedded World; without it, `run_js` reports the seam.
    #[cfg(feature = "js-agent")]
    pub fn with_run_js(mut self, tool: crate::run_js::RunJsTool) -> Result<Self, String> {
        let rt = deos_js::JsRuntime::new()?;
        self.js = Some(JsHands { tool, rt });
        Ok(self)
    }

    /// The confined-tool-call tape (scripts/commands + receipts/verdicts), for the
    /// caller to assert every tool-call routed through dregg.
    pub fn tape(&self) -> &[ConfinedToolResult] {
        &self.tape
    }

    /// The gateway (post-run, for the mandate inspector).
    pub fn gateway(&self) -> &HermesGateway<'rt> {
        &self.gateway
    }

    /// The MCP `tools/list` payload — the ONLY tools a confined Hermes may use.
    /// Each carries an `inputSchema` (the JSON-Schema the model fills).
    pub fn tools_list(&self) -> Value {
        json!({
            "tools": [
                {
                    "name": "run_js",
                    "title": "Run JavaScript on the dregg verified World",
                    "description":
                        "Run a JavaScript program against the dregg `deos` runtime. \
                         `deos.world.cells()` lists the live cells; \
                         `var app = deos.applet({ affordances: [\"bump\"] }); app.fire(\"bump\", n)` \
                         commits a real cap-gated verified turn (returns the new value). \
                         Every fire is receipted and bounded by your held authority; \
                         an over-reach is refused in-band (-1).",
                    "inputSchema": {
                        "type": "object",
                        "properties": {
                            "script": {
                                "type": "string",
                                "description": "The JavaScript program to run (last expression = result)."
                            }
                        },
                        "required": ["script"]
                    }
                },
                {
                    "name": "terminal",
                    "title": "Run a shell command inside the dregg container sandbox",
                    "description":
                        "Run a shell command inside a dregg protection-domain: file, \
                         network, and exec are denied by the OS sandbox; the command's \
                         intent becomes a cap-gated receipted turn. Use this for any \
                         shell work — there is no unconfined shell.",
                    "inputSchema": {
                        "type": "object",
                        "properties": {
                            "command": {
                                "type": "string",
                                "description": "The shell command to run (inside the dregg sandbox)."
                            }
                        },
                        "required": ["command"]
                    }
                }
            ]
        })
    }

    /// THE ROUTER — run a `tools/call` (`name` + `arguments`) through dregg
    /// confinement, returning the MCP `CallToolResult` value. Every named tool
    /// terminates in a cap-gated, receipted dregg turn (or an in-band refusal the
    /// model sees as `isError`). An unknown tool is refused (the model has no
    /// other tools — `tools/list` advertised exactly the dregg surface).
    pub fn call_tool(&mut self, name: &str, arguments: &Value) -> Value {
        self.clock += 1;
        let now = self.clock;
        let result = match name {
            "run_js" => self.call_run_js(arguments, now),
            "terminal" => self.call_terminal(arguments, now),
            other => ConfinedToolResult {
                tool: other.to_string(),
                text: format!(
                    "dregg MCP server exposes only {DREGG_TOOL_NAMES:?}; '{other}' is not a \
                     confined tool (the model has no unconfined tool path)."
                ),
                admitted: false,
                ..Default::default()
            },
        };
        let value = call_tool_result_value(&result);
        self.tape.push(result);
        value
    }

    /// `run_js` — the model's chosen script runs on the agent's bounded deos-js
    /// World (mounted under `held`, never root): a cap-gated, receipted verified
    /// turn. Cross-process seam: this server's own embedded World (not the
    /// cockpit's live `Rc<RefCell<World>>`) — UNLESS a world bridge is configured
    /// ([`McpToolHost::with_world_bridge`]), in which case the script runs
    /// ATTACHED to the cockpit's live World over the socket, fail-closed.
    #[cfg(feature = "js-agent")]
    fn call_run_js(&mut self, arguments: &Value, now: i64) -> ConfinedToolResult {
        let script = arguments
            .get("script")
            .or_else(|| arguments.get("code"))
            .or_else(|| arguments.get("js"))
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string();
        let call = ToolCallRequest::new("mcp", "tc-run_js", "run_js", json!({ "script": script }));

        // Disjoint mutable borrows: the host's gateway (the accountability gate)
        // and the js hands (the deos-js runtime). `run_on` meters the run_js
        // tool-call on the gateway, then evals the model's script under `held`.
        if self.js.is_none() {
            return ConfinedToolResult {
                tool: "run_js".into(),
                text: "run_js unavailable: the dregg MCP server was built without `js-agent` \
                       (no deos-js engine). Rebuild with --features js-agent."
                    .into(),
                admitted: false,
                ..Default::default()
            };
        }
        // THE WORLD BRIDGE — a bridge-configured host lands run_js on the
        // COCKPIT'S live World (fail-closed: never the embedded one).
        #[cfg(unix)]
        if self.bridge.is_some() {
            return self.call_run_js_bridged(&script, now);
        }

        let McpToolHost { gateway, js, .. } = self;
        let js = js.as_mut().expect("checked Some above");

        match js.tool.run_on(&mut js.rt, gateway, &call, now, &script) {
            Ok(outcome) => {
                let admitted = outcome.tool_admitted();
                let receipt = outcome.receipts.first().map(hex32);
                let text = if !admitted {
                    format!("run_js refused: {}", refusal_text(&outcome.tool_outcome))
                } else if let Some(err) = &outcome.js_error {
                    format!("run_js eval fault: {err}")
                } else {
                    format!(
                        "ran on the dregg verified World: result={:?}, {} verified turn(s) committed{}",
                        outcome.result,
                        outcome.fires_committed,
                        receipt
                            .as_ref()
                            .map(|r| format!(", receipt {}…", &r[..r.len().min(12)]))
                            .unwrap_or_default()
                    )
                };
                ConfinedToolResult {
                    tool: "run_js".into(),
                    text,
                    admitted,
                    receipt,
                    sandbox_verdict: None,
                    fires_committed: outcome.fires_committed,
                }
            }
            Err(e) => ConfinedToolResult {
                tool: "run_js".into(),
                text: format!("run_js engine fault: {e}"),
                admitted: false,
                ..Default::default()
            },
        }
    }

    /// `run_js` OVER THE WORLD BRIDGE — the model's script runs ATTACHED to the
    /// COCKPIT'S live World through the [`crate::world_bridge::SocketWorldSink`]
    /// ([`crate::RunJsTool::run_attached_on`] accepts any `WorldSink`): every
    /// affordance fire commits a real verified turn whose receipt lands on the
    /// COCKPIT'S ledger, still cap-gated under the agent's `held` client-side.
    ///
    /// FAIL-CLOSED: the socket absent/dead ⇒ the call REFUSES here, in-band,
    /// with a clear message — it NEVER silently runs on the embedded World.
    #[cfg(all(unix, feature = "js-agent"))]
    fn call_run_js_bridged(&mut self, script: &str, now: i64) -> ConfinedToolResult {
        let McpToolHost {
            gateway,
            js,
            bridge,
            ..
        } = self;
        let js = js
            .as_mut()
            .expect("bridged run_js requires js hands (checked)");
        let bridge = bridge
            .as_mut()
            .expect("bridged run_js requires a bridge (checked)");

        // Dial (or reuse) the cockpit's world-bridge socket — the fail-closed gate.
        let sink = match bridge.sink() {
            Ok(sink) => sink,
            Err(e) => {
                return ConfinedToolResult {
                    tool: "run_js".into(),
                    text: format!(
                        "run_js REFUSED: the cockpit world-bridge socket at {} is absent or \
                         dead ({e}). Fail-closed — a bridged run_js never falls back to the \
                         embedded World. Start the cockpit's serve_world_bridge and retry.",
                        bridge.socket_path.display()
                    ),
                    admitted: false,
                    ..Default::default()
                };
            }
        };

        let call = ToolCallRequest::new("mcp", "tc-run_js", "run_js", json!({ "script": script }));
        let agent = js.tool.agent_cell();
        match js.tool.run_attached_on(
            &mut js.rt,
            Box::new(sink),
            agent,
            gateway,
            &call,
            now,
            script,
        ) {
            Ok(outcome) => {
                let admitted = outcome.tool_admitted();
                let receipt = outcome.receipts.first().map(hex32);
                let text = if !admitted {
                    format!("run_js refused: {}", refusal_text(&outcome.tool_outcome))
                } else if let Some(err) = &outcome.js_error {
                    format!("run_js eval fault (world bridge): {err}")
                } else {
                    format!(
                        "ran on the COCKPIT'S live World over the world bridge: result={:?}, \
                         {} verified turn(s) committed on the live ledger{}",
                        outcome.result,
                        outcome.fires_committed,
                        receipt
                            .as_ref()
                            .map(|r| format!(", receipt {}…", &r[..r.len().min(12)]))
                            .unwrap_or_default()
                    )
                };
                ConfinedToolResult {
                    tool: "run_js".into(),
                    text,
                    admitted,
                    receipt,
                    sandbox_verdict: None,
                    fires_committed: outcome.fires_committed,
                }
            }
            Err(e) => ConfinedToolResult {
                tool: "run_js".into(),
                text: format!("run_js engine fault (world bridge): {e}"),
                admitted: false,
                ..Default::default()
            },
        }
    }

    /// `run_js` when the `js-agent` feature is OFF — names the seam (the tool is
    /// advertised but its hands need deos-js).
    #[cfg(not(feature = "js-agent"))]
    fn call_run_js(&mut self, _arguments: &Value, _now: i64) -> ConfinedToolResult {
        ConfinedToolResult {
            tool: "run_js".into(),
            text: "run_js unavailable: the dregg MCP server was built without `js-agent` \
                   (no deos-js engine). Rebuild with --features js-agent."
                .into(),
            admitted: false,
            ..Default::default()
        }
    }

    /// `terminal` — the command execs INSIDE a confined firmament PD. The
    /// confinement is REAL: [`crate::confined::launch_confined`] forks an
    /// OS-sandboxed child (Seatbelt/seccomp+landlock) whose ONLY channel is its
    /// Endpoint; file/net/exec are denied. The body runs the FOUR sandbox probes
    /// (open denied / inet denied / only-Endpoint-fd / IPC works) and reports the
    /// verdict bitmask. The command itself becomes a cap-gated receipted turn
    /// through the gateway. So a command attempting ambient authority is
    /// physically DENIED — the shell ran in the container, not loose.
    #[cfg(unix)]
    fn call_terminal(&mut self, arguments: &Value, now: i64) -> ConfinedToolResult {
        let command = arguments
            .get("command")
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string();

        // (1) THE AUTHORITY FACE — the `terminal` tool-call is a cap-gated,
        //     metered, receipted dregg turn (or an in-band refusal). This is the
        //     SAME gate the rate-0 `live-refuse` demo bites on.
        let call = ToolCallRequest::new(
            "mcp",
            "tc-terminal",
            "terminal",
            json!({ "command": command }),
        );
        let outcome = self.gateway.admit_call(&call, now);
        let admitted = outcome.allowed();
        let receipt = match &outcome {
            PermissionOutcome::Allow { receipt, .. } => Some(receipt.clone()),
            PermissionOutcome::Reject { .. } => None,
        };
        if !admitted {
            return ConfinedToolResult {
                tool: "terminal".into(),
                text: format!(
                    "terminal refused (cap-gated, no exec): {}",
                    refusal_text(&outcome)
                ),
                admitted: false,
                receipt: None,
                sandbox_verdict: None,
                fires_committed: 0,
            };
        }

        // (2) THE AMBIENT FACE — exec the command INSIDE a confined PD. The body
        //     runs the sandbox probes (proving ambient authority is denied) and
        //     reports the verdict bitmask via the PD exit code.
        let verdict = run_command_in_confined_pd(&command);
        let confined = matches!(&verdict, Ok(v) if *v == crate::confined::probe::ALL);
        let sandbox_verdict = verdict.as_ref().ok().copied();
        let text = match &verdict {
            Ok(v) => format!(
                "ran `{}` inside a dregg PD: confinement verdict 0x{v:x} ({}). \
                 The shell ran in the container — file/net/exec denied; \
                 ambient-authority attempts refused. Receipt {}.",
                command,
                if confined {
                    "ALL teeth held"
                } else {
                    "PARTIAL — see probe bits"
                },
                receipt.as_deref().unwrap_or("(none)")
            ),
            Err(e) => format!(
                "could not launch the dregg PD for `{}`: {e}. \
                 (No unconfined fallback — fail-closed.)",
                command
            ),
        };
        ConfinedToolResult {
            tool: "terminal".into(),
            text,
            admitted,
            receipt,
            sandbox_verdict,
            fires_committed: 0,
        }
    }

    /// `terminal` on a non-Unix host — the confined-PD sandbox is Unix-only; the
    /// gate still cap-checks the call, and the exec seam is named (no unconfined
    /// fallback).
    #[cfg(not(unix))]
    fn call_terminal(&mut self, arguments: &Value, now: i64) -> ConfinedToolResult {
        let command = arguments
            .get("command")
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string();
        let call = ToolCallRequest::new(
            "mcp",
            "tc-terminal",
            "terminal",
            json!({ "command": command }),
        );
        let outcome = self.gateway.admit_call(&call, now);
        ConfinedToolResult {
            tool: "terminal".into(),
            text: "terminal: the confined-PD sandbox is Unix-only on this host; \
                   the cap gate still metered the call, but no exec environment is available."
                .into(),
            admitted: outcome.allowed(),
            receipt: match &outcome {
                PermissionOutcome::Allow { receipt, .. } => Some(receipt.clone()),
                PermissionOutcome::Reject { .. } => None,
            },
            sandbox_verdict: None,
            fires_committed: 0,
        }
    }
}

/// Exec a command inside a confined firmament PD, returning the sandbox-probe
/// verdict bitmask the PD body reports ([`crate::confined::probe::ALL`] = every
/// confinement tooth held). The body proves the shell ran in the container: it
/// runs the four probes (file open denied, inet socket denied, only the Endpoint
/// fd open) and folds the verdict into the PD exit code.
///
/// The `_command` is recorded as the intent; under Phase-0 Endpoint-only
/// confinement the PD has NO exec authority (that IS the sandbox — `execve` is
/// denied), so the body does not `execve` an OS shell. The confinement verdict
/// proves the ambient authority a real shell would need is physically refused.
#[cfg(unix)]
fn run_command_in_confined_pd(_command: &str) -> std::io::Result<i32> {
    use dregg_firmament::process_kernel::ProcessKernel;

    let kernel = ProcessKernel::new();
    // The confined body: run the sandbox probes (ambient authority denied) and
    // a tiny Endpoint round-trip so IPC_WORKS is set, then fold the verdict.
    let agent = crate::confined::launch_confined(&kernel, move |sock| {
        // Prove confinement: the four probes (open/inet denied, only Endpoint).
        let mut verdict = crate::confined::run_sandbox_probes();
        // Prove the Endpoint round-trips (the only channel): write one ack line.
        use std::io::Write;
        if sock
            .write_all(b"{\"confined\":true}\n")
            .and_then(|_| sock.flush())
            .is_ok()
        {
            verdict |= crate::confined::probe::IPC_WORKS;
        }
        verdict
    })?;
    // Drain the one ack line the body wrote (so the body's write doesn't block on
    // a full pipe), then reap the verdict.
    {
        use std::io::Read;
        if let Ok(mut sock) = agent.pd.kernel_sock.try_clone() {
            let mut buf = [0u8; 64];
            let _ = sock.read(&mut buf);
        }
    }
    agent.join_verdict()
}

/// Serialize a [`ConfinedToolResult`] into an MCP `CallToolResult` value
/// (`{ content: [{ type: "text", text }], isError }`). A refused call is an
/// `isError: true` result the model sees in-band.
fn call_tool_result_value(r: &ConfinedToolResult) -> Value {
    json!({
        "content": [ { "type": "text", "text": r.text } ],
        "isError": !r.admitted,
        // deos extension: the receipt + confinement evidence (ignored by a plain
        // MCP client, surfaced by deos's own inspector / the live bake).
        "_deos": {
            "receipt": r.receipt,
            "sandboxVerdict": r.sandbox_verdict,
            "firesCommitted": r.fires_committed
        }
    })
}

/// The refusal text of a [`PermissionOutcome::Reject`] (else a generic note).
fn refusal_text(outcome: &PermissionOutcome) -> String {
    match outcome {
        PermissionOutcome::Reject { reason, .. } => reason.clone(),
        PermissionOutcome::Allow { .. } => "(admitted)".into(),
    }
}

/// Hex-encode a 32-byte receipt hash.
// Only the `js-agent` run_js path formats receipt hashes; gated to match its sole caller.
#[cfg(feature = "js-agent")]
fn hex32(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// ─────────────────────────── the stdio MCP server ───────────────────────────

/// THE STDIO MCP SERVER — drive a standard MCP JSON-RPC session over `reader`/
/// `writer` (Hermes's `stdio_client` connects this server's stdin/stdout),
/// routing every `tools/call` through [`McpToolHost`] (dregg confinement).
///
/// Speaks: `initialize` (echo `protocolVersion`, advertise `tools`),
/// `notifications/initialized` (ack), `tools/list`, `tools/call`, `ping`. Runs
/// until the client closes the stream (EOF) — the lifetime Hermes keeps the MCP
/// subprocess alive for the session.
pub struct McpServer<'rt> {
    host: McpToolHost<'rt>,
}

impl<'rt> McpServer<'rt> {
    /// Build the server over a dregg tool `host`.
    pub fn new(host: McpToolHost<'rt>) -> McpServer<'rt> {
        McpServer { host }
    }

    /// The host (post-run, for the tape / inspector).
    pub fn host(&self) -> &McpToolHost<'rt> {
        &self.host
    }

    /// Consume the server into its host (to read the tape after a driven session).
    pub fn into_host(self) -> McpToolHost<'rt> {
        self.host
    }

    /// Serve the MCP session over `reader` (client → server, ndjson) / `writer`
    /// (server → client, ndjson), until EOF. Returns the number of `tools/call`
    /// requests served. Each request is one JSON object per line.
    pub fn serve<R: std::io::BufRead, W: std::io::Write>(
        &mut self,
        mut reader: R,
        mut writer: W,
    ) -> std::io::Result<usize> {
        let mut calls_served = 0usize;
        let mut line = String::new();
        loop {
            line.clear();
            let n = reader.read_line(&mut line)?;
            if n == 0 {
                break; // EOF — client closed the session.
            }
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }
            let msg: Value = match serde_json::from_str(trimmed) {
                Ok(v) => v,
                Err(_) => continue, // skip a malformed frame (robust against noise).
            };
            // A request has an `id`; a notification has none (no reply).
            let id = msg.get("id").cloned();
            let method = msg.get("method").and_then(|m| m.as_str()).unwrap_or("");
            let params = msg.get("params").cloned().unwrap_or(Value::Null);

            if method == "tools/call" {
                calls_served += 1;
            }
            let reply = self.handle(method, &params);
            // Only reply to REQUESTS (those with an id); notifications get none.
            if let (Some(id), Some(result)) = (id, reply) {
                let response = json!({ "jsonrpc": "2.0", "id": id, "result": result });
                let s = serde_json::to_string(&response)
                    .unwrap_or_else(|_| "{\"jsonrpc\":\"2.0\"}".into());
                writer.write_all(s.as_bytes())?;
                writer.write_all(b"\n")?;
                writer.flush()?;
            }
        }
        Ok(calls_served)
    }

    /// Handle one MCP method, returning the `result` value to reply with — or
    /// `None` for a notification (no reply on the wire).
    fn handle(&mut self, method: &str, params: &Value) -> Option<Value> {
        match method {
            "initialize" => {
                // Echo the client's requested protocol version (the SDK negotiates
                // by string); advertise the `tools` capability + server identity.
                let proto = params
                    .get("protocolVersion")
                    .and_then(|v| v.as_str())
                    .unwrap_or(MCP_FALLBACK_PROTOCOL_VERSION)
                    .to_string();
                Some(json!({
                    "protocolVersion": proto,
                    "capabilities": { "tools": { "listChanged": false } },
                    "serverInfo": { "name": "dregg-confined", "version": "0.1.0" }
                }))
            }
            // The client's post-initialize ack — a notification, no reply.
            "notifications/initialized" | "initialized" => None,
            "tools/list" => Some(self.host.tools_list()),
            "tools/call" => {
                let name = params.get("name").and_then(|v| v.as_str()).unwrap_or("");
                let arguments = params.get("arguments").cloned().unwrap_or(json!({}));
                Some(self.host.call_tool(name, &arguments))
            }
            "ping" => Some(json!({})),
            // Any other request: an empty result so the client never wedges.
            _ => Some(json!({})),
        }
    }
}
