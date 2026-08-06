//! `mcp::protocol` — split out of the former monolithic `mcp.rs` (pure module move).

use super::*;

#[derive(Deserialize)]
pub(super) struct JsonRpcRequest {
    #[allow(dead_code)] // Deserialized from the wire (version field) but not branched on.
    pub(super) jsonrpc: String,
    pub(super) id: Option<Value>,
    pub(super) method: String,
    #[serde(default)]
    pub(super) params: Value,
}

#[derive(Serialize)]
pub(super) struct JsonRpcResponse {
    pub(super) jsonrpc: &'static str,
    pub(super) id: Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) result: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) error: Option<JsonRpcError>,
}

#[derive(Serialize)]
pub(super) struct JsonRpcError {
    pub(super) code: i32,
    pub(super) message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) data: Option<Value>,
}

impl JsonRpcResponse {
    pub(super) fn success(id: Value, result: Value) -> Self {
        Self {
            jsonrpc: "2.0",
            id,
            result: Some(result),
            error: None,
        }
    }

    pub(super) fn error(id: Value, code: i32, message: impl Into<String>) -> Self {
        Self {
            jsonrpc: "2.0",
            id,
            result: None,
            error: Some(JsonRpcError {
                code,
                message: message.into(),
                data: None,
            }),
        }
    }

    pub(super) fn method_not_found(id: Value) -> Self {
        Self::error(id, -32601, "Method not found")
    }

    pub(super) fn invalid_params(id: Value, msg: impl Into<String>) -> Self {
        Self::error(id, -32602, msg)
    }

    pub(super) fn internal_error(id: Value, msg: impl Into<String>) -> Self {
        Self::error(id, -32603, msg)
    }
}

// =============================================================================
// MCP protocol types
// =============================================================================

#[derive(Serialize)]
pub(super) struct McpInitializeResult {
    #[serde(rename = "protocolVersion")]
    pub(super) protocol_version: &'static str,
    pub(super) capabilities: McpCapabilities,
    #[serde(rename = "serverInfo")]
    pub(super) server_info: McpServerInfo,
    /// MCP `instructions`: a server-level orientation hint shown to the model on
    /// connect, BEFORE it lists anything. dregg uses it to immediately point an
    /// arriving agent at its self-orientation surface (`dregg://about`,
    /// `dregg://ontology`, `dregg://identity`) and explain the `_cap` ocap
    /// convention — so the agent knows it is INHABITING a place, not calling an
    /// RPC grab-bag, from the very first message.
    pub(super) instructions: &'static str,
}

#[derive(Serialize)]
pub(super) struct McpCapabilities {
    pub(super) tools: McpToolsCapability,
    pub(super) resources: McpResourcesCapability,
    pub(super) prompts: McpPromptsCapability,
    /// MCP `completions` capability: this server answers `completion/complete`
    /// for prompt arguments and resource-template variables (e.g. completing a
    /// `dregg://cell/{cell_id}` from the cells it knows). An empty object is the
    /// spec's way of advertising the capability with no sub-flags.
    pub(super) completions: McpCompletionsCapability,
}

#[derive(Serialize)]
pub(super) struct McpCompletionsCapability {}

#[derive(Serialize)]
pub(super) struct McpToolsCapability {
    #[serde(rename = "listChanged")]
    pub(super) list_changed: bool,
}

#[derive(Serialize)]
pub(super) struct McpResourcesCapability {
    /// We support resources/subscribe for live state (cell state, blocklace
    /// status) via the node's event broadcast, advertised but realized lazily.
    pub(super) subscribe: bool,
    #[serde(rename = "listChanged")]
    pub(super) list_changed: bool,
}

#[derive(Serialize)]
pub(super) struct McpPromptsCapability {
    #[serde(rename = "listChanged")]
    pub(super) list_changed: bool,
}

#[derive(Serialize)]
pub(super) struct McpServerInfo {
    pub(super) name: &'static str,
    pub(super) version: &'static str,
}

#[derive(Serialize)]
pub(super) struct McpToolsListResult {
    pub(super) tools: Vec<McpToolDef>,
}

#[derive(Serialize)]
pub(super) struct McpToolDef {
    pub(super) name: &'static str,
    /// MCP `title`: a short human-friendly display name (distinct from the
    /// programmatic `name`). Injected from [`tool_title`] in the list pass.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) title: Option<&'static str>,
    pub(super) description: &'static str,
    #[serde(rename = "inputSchema")]
    pub(super) input_schema: Value,
    /// MCP 2025-06-18 `outputSchema`: the JSON-schema of the tool's
    /// `structuredContent`. Declaring it lets a client validate the typed result
    /// and know the shape before calling. dregg's mutating tools all return a
    /// common "receipt" shape; reads return their own structured state. Injected
    /// in the list pass from [`tool_output_schema`].
    #[serde(rename = "outputSchema", skip_serializing_if = "Option::is_none")]
    pub(super) output_schema: Option<Value>,
    /// MCP behavioural ANNOTATIONS (`readOnlyHint` / `destructiveHint` /
    /// `idempotentHint` / `openWorldHint`). These are hints — an agent uses
    /// them to decide whether a call mutates, can be safely retried, or touches
    /// the open world (network / other federations). Injected in the list pass.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) annotations: Option<McpToolAnnotations>,
}

/// MCP tool behavioural annotations. All four are OPTIONAL hints per the spec;
/// we always populate `readOnlyHint` and `idempotentHint`, and the others when
/// meaningful. An agent reads these to know e.g. that `dregg_read_cell` is
/// read-only (safe to probe) while `dregg_revoke_capability` is destructive.
#[derive(Serialize, Clone, Copy)]
pub(super) struct McpToolAnnotations {
    #[serde(rename = "readOnlyHint")]
    pub(super) read_only_hint: bool,
    #[serde(rename = "destructiveHint", skip_serializing_if = "Option::is_none")]
    pub(super) destructive_hint: Option<bool>,
    #[serde(rename = "idempotentHint")]
    pub(super) idempotent_hint: bool,
    #[serde(rename = "openWorldHint", skip_serializing_if = "Option::is_none")]
    pub(super) open_world_hint: Option<bool>,
}

#[derive(Serialize)]
pub(super) struct McpToolResult {
    pub(super) content: Vec<McpContent>,
    /// MCP 2025-06-18 STRUCTURED OUTPUT. When a tool's result is structured
    /// (a receipt, a proof status, a cell state), we surface the raw JSON object
    /// here in addition to the human-readable `content` text. Clients that
    /// understand `structuredContent` can consume the typed shape directly;
    /// older clients still get the pretty-printed text. Always omitted for
    /// plain-text / error results.
    #[serde(rename = "structuredContent", skip_serializing_if = "Option::is_none")]
    pub(super) structured_content: Option<Value>,
    #[serde(rename = "isError", skip_serializing_if = "Option::is_none")]
    pub(super) is_error: Option<bool>,
}

#[derive(Serialize)]
pub(super) struct McpContent {
    #[serde(rename = "type")]
    pub(super) content_type: &'static str,
    pub(super) text: String,
}

impl McpToolResult {
    #[allow(dead_code)] // Convenience ctor retained alongside the explicit-content path.
    pub(super) fn text(s: impl Into<String>) -> Self {
        Self {
            content: vec![McpContent {
                content_type: "text",
                text: s.into(),
            }],
            structured_content: None,
            is_error: None,
        }
    }

    /// Structured success: pretty text for humans + a machine-readable
    /// `structuredContent` mirror for MCP clients that consume typed output.
    pub(super) fn json(value: &Value) -> Self {
        Self {
            content: vec![McpContent {
                content_type: "text",
                text: serde_json::to_string_pretty(value).unwrap_or_default(),
            }],
            structured_content: Some(value.clone()),
            is_error: None,
        }
    }

    pub(super) fn error(s: impl Into<String>) -> Self {
        Self {
            content: vec![McpContent {
                content_type: "text",
                text: s.into(),
            }],
            structured_content: None,
            is_error: Some(true),
        }
    }

    /// Structured ACTIONABLE error: an `isError` result whose message tells the
    /// agent how to recover, plus a machine-readable `structuredContent` carrying
    /// `{ error: <msg>, hint: <fix>, ...extra }` so a client can react
    /// programmatically (e.g. retry with the expected nonce). MCP best practice:
    /// errors inside a tool result (not JSON-RPC errors) so the agent sees them.
    pub(super) fn actionable_error(msg: impl Into<String>, hint: impl Into<String>) -> Self {
        let msg = msg.into();
        let hint = hint.into();
        let text = format!("{msg}\n  → {hint}");
        Self {
            content: vec![McpContent {
                content_type: "text",
                text,
            }],
            structured_content: Some(serde_json::json!({
                "error": msg,
                "hint": hint,
            })),
            is_error: Some(true),
        }
    }
}

// =============================================================================
// Tool definitions
// =============================================================================

/// Run the MCP server over stdio.
///
/// Reads JSON-RPC messages from stdin (one per line) and writes responses to stdout.
/// This function runs until stdin is closed (EOF).
pub async fn run_stdio(state: NodeState) {
    info!("MCP server starting (stdio transport)");

    let stdin = tokio::io::stdin();
    let mut stdout = tokio::io::stdout();
    let reader = BufReader::new(stdin);
    let mut lines = reader.lines();

    while let Ok(Some(line)) = lines.next_line().await {
        let line = line.trim().to_string();
        if line.is_empty() {
            continue;
        }

        let request: JsonRpcRequest = match serde_json::from_str(&line) {
            Ok(r) => r,
            Err(e) => {
                let err_resp =
                    JsonRpcResponse::error(Value::Null, -32700, format!("Parse error: {e}"));
                let _ = write_response(&mut stdout, &err_resp).await;
                continue;
            }
        };

        // Notifications (no id) don't get responses.
        if request.id.is_none() {
            // Handle notifications silently (e.g., notifications/initialized).
            continue;
        }

        let id = request.id.unwrap_or(Value::Null);

        let response = match request.method.as_str() {
            "initialize" => handle_initialize(id),
            "tools/list" => handle_tools_list(id, request.params, &state).await,
            "tools/call" => handle_tools_call(id, request.params, &state).await,
            "resources/list" => handle_resources_list(id, request.params, &state).await,
            "resources/templates/list" => handle_resource_templates_list(id),
            "resources/read" => handle_resources_read(id, request.params, &state).await,
            "prompts/list" => handle_prompts_list(id),
            "prompts/get" => handle_prompts_get(id, request.params),
            "completion/complete" => handle_completion_complete(id, request.params, &state).await,
            "ping" => JsonRpcResponse::success(id, serde_json::json!({})),
            _ => JsonRpcResponse::method_not_found(id),
        };

        if let Err(e) = write_response(&mut stdout, &response).await {
            error!("failed to write MCP response: {e}");
            break;
        }
    }

    info!("MCP server shutting down (stdin closed)");
}

pub(super) fn handle_initialize(id: Value) -> JsonRpcResponse {
    let result = McpInitializeResult {
        // 2025-06-18: the revision that standardized tool annotations +
        // structured tool output, both of which this server now emits.
        protocol_version: "2025-06-18",
        capabilities: McpCapabilities {
            tools: McpToolsCapability {
                list_changed: false,
            },
            resources: McpResourcesCapability {
                subscribe: true,
                list_changed: false,
            },
            prompts: McpPromptsCapability {
                list_changed: false,
            },
            completions: McpCompletionsCapability {},
        },
        server_info: McpServerInfo {
            name: "dregg-node",
            version: env!("CARGO_PKG_VERSION"),
        },
        instructions: "You are inhabiting dregg — verified, capability-secure polis-infrastructure for AI \
             minds. This is a place, not an RPC grab-bag. Before acting, ORIENT: read the \
             resources `dregg://about` (what dregg is + the four modes orient/act/delegate/verify), \
             `dregg://ontology` (the 31 verified effects you can drive), and `dregg://identity` \
             (who you are here). Then read `dregg://capabilities` (or call \
             `dregg_check_capabilities`) to see what authority you hold. Every state-changing turn \
             runs through the capability-checked executor — the Lean-verified producer is \
             authoritative for the covered effect set, and when full-turn proving is enabled each \
             committed turn carries a STARK-proved receipt — VERIFY your \
             actions via `dregg://receipt/{turn_hash}`. Capabilities are unforgeable and \
             attenuable: DELEGATE bounded authority to sub-agents with `dregg_delegate`. Tools are \
             capability-gated — when enforcement is on, present your tools-access biscuit under the \
             `_cap` argument (`{\"_cap\":{\"biscuit\":\"eb2_…\"}}`) and `tools/list` will show only \
             the tools it covers. The MCP `prompts` (orient, submit_turn, delegate_capability, \
             register_name, verify_turn, publish_intent) are guided walkthroughs of the common \
             workflows.",
    };

    JsonRpcResponse::success(id, serde_json::to_value(result).unwrap())
}

/// Page size for paginated list endpoints (tools/resources). Opaque cursors are
/// just the next start index encoded as a decimal string, so pagination is
/// stable across calls as long as the underlying list is stable (it is — tool
/// and resource sets are static per build).
pub(super) const MCP_PAGE_SIZE: usize = 20;

/// Decode an opaque `cursor` param into a start index. Absent / malformed →
/// start at 0 (fail-open to the first page rather than erroring a list call).
pub(super) fn decode_cursor(params: &Value) -> usize {
    params
        .get("cursor")
        .and_then(|v| v.as_str())
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(0)
}

/// Produce the `nextCursor` value for a page, or `None` when the page is the
/// last one. The cursor is the opaque encoding of the next start index.
pub(super) fn next_cursor(start: usize, page_len: usize, total: usize) -> Option<String> {
    let consumed = start + page_len;
    if consumed < total {
        Some(consumed.to_string())
    } else {
        None
    }
}

/// `tools/list` — CAPABILITY-FILTERED (the ocap model through MCP).
///
/// An agent only SEES the tools its capabilities permit. When `mcp_cap_enforce`
/// is on, a client may present its tools-access biscuit under `_cap` in the list
/// params; we filter the catalog to exactly the tools that biscuit COVERS — the
/// same `verify_token_for_scope` admission check that gates invocation, reused
/// read-only for VISIBILITY. With enforcement on and NO `_cap`, the catalog is
/// empty (you can't invoke anything, so you see nothing). With enforcement off,
/// the full catalog is visible (back-compat). This makes the tool surface an
/// honest reflection of the authority held — not an RPC grab-bag.
///
/// Pagination is applied AFTER filtering, so cursors page the visible subset.
pub(super) async fn handle_tools_list(
    id: Value,
    params: Value,
    state: &NodeState,
) -> JsonRpcResponse {
    let ctx = McpCapContext::snapshot(state).await;
    // The optional presented capability lives under `_cap` in the list params
    // (same convention as a tools/call). Absent ⇒ no credential.
    let presented = parse_presented_cap(&params, &ctx.issuer_pubkey);

    let all = tool_definitions();
    let visible: Vec<McpToolDef> = all
        .into_iter()
        .filter(|d| ctx.tool_invocable(presented.as_ref(), d.name))
        .collect();
    let total = visible.len();
    let start = decode_cursor(&params).min(total);
    let page: Vec<McpToolDef> = visible
        .into_iter()
        .skip(start)
        .take(MCP_PAGE_SIZE)
        .collect();
    let cursor = next_cursor(start, page.len(), total);

    let mut result = match serde_json::to_value(McpToolsListResult { tools: page }) {
        Ok(v) => v,
        Err(e) => {
            return JsonRpcResponse::internal_error(
                id,
                format!("failed to serialize tools list: {e}"),
            );
        }
    };
    if let Value::Object(map) = &mut result {
        if let Some(c) = cursor {
            map.insert("nextCursor".to_string(), Value::String(c));
        }
        // Surface WHY the visible set may be smaller than the full catalog, so an
        // agent self-orienting from tools/list understands the ocap filtering.
        map.insert(
            "_meta".to_string(),
            serde_json::json!({
                "dregg.cap_enforcement": ctx.enforce,
                "dregg.cap_presented": presented.is_some(),
                "dregg.visible_tool_count": total,
                "dregg.note": if ctx.enforce {
                    "tools/list is capability-filtered: you see only the tools your '_cap' \
                     biscuit covers. Present a covering '_cap' (read/write/admin) to reveal more."
                } else {
                    "capability enforcement is off: the full tool catalog is visible."
                },
            }),
        );
    }
    JsonRpcResponse::success(id, result)
}

pub(super) async fn handle_tools_call(
    id: Value,
    params: Value,
    state: &NodeState,
) -> JsonRpcResponse {
    let tool_name = match params.get("name").and_then(|v| v.as_str()) {
        Some(n) => n.to_string(),
        None => return JsonRpcResponse::invalid_params(id, "missing 'name' in tools/call"),
    };

    let arguments = params
        .get("arguments")
        .cloned()
        .unwrap_or(Value::Object(serde_json::Map::new()));

    // Per-tool capability gate (TOKEN-CAPABILITY-UNIFICATION): require the
    // caller's presented `Authorization::Token` to cover this tool's declared
    // scope, verified by the EXECUTOR. A non-covering or (under enforcement) a
    // missing credential is REJECTED here — the call never reaches the tool.
    if let Err(reason) = enforce_tool_cap(&tool_name, &arguments, state).await {
        let denied = McpToolResult::error(format!("capability denied: {reason}"));
        return match serde_json::to_value(denied) {
            Ok(v) => JsonRpcResponse::success(id, v),
            Err(e) => {
                JsonRpcResponse::internal_error(id, format!("failed to serialize tool result: {e}"))
            }
        };
    }

    let result = dispatch_tool(&tool_name, arguments, state).await;

    match serde_json::to_value(result) {
        Ok(v) => JsonRpcResponse::success(id, v),
        Err(e) => {
            JsonRpcResponse::internal_error(id, format!("failed to serialize tool result: {e}"))
        }
    }
}

// =============================================================================
// RESOURCES — readable dregg state with stable URIs (self-orientation surface)
// =============================================================================
//
// Resources let an AI agent ORIENT before it acts: read the dregg ontology
// (the 31 verified effects + constraint vocabulary), the node's own identity,
// its receipt chain, capabilities, consensus/finality status, and any cell's
// state — all by URI, without invoking a (gated, side-effecting) tool. This is
// the "what is this place and what do I hold" half of inhabiting dregg.

/// The verified dregg ontology catalog, embedded at build time. AUTOGENERATED
/// from the Lean source of truth (`Dregg2/Exec/TurnExecutorFull.lean` +
/// `Dregg2/Exec/FFI.lean`): the 31 effects, their wire codecs, facets,
/// categories, and semantics. An agent reading `dregg://ontology` learns the
/// entire effect vocabulary it can drive. The artifact lives beside this crate
/// (`node/data/ontology-catalog.generated.json`) so the node never depends on
/// the (discarded) `./site` tree; its generator currently survives only under
/// `site-old-scavenge/tools/gen-ontology-catalog.js` and must emit here.
pub(super) const DREGG_ONTOLOGY_CATALOG: &str =
    include_str!("../../data/ontology-catalog.generated.json");

/// A static MCP resource the node always exposes.
pub(super) struct StaticResource {
    pub(super) uri: &'static str,
    pub(super) name: &'static str,
    pub(super) title: &'static str,
    pub(super) description: &'static str,
    pub(super) mime_type: &'static str,
}

/// The fixed (non-templated) resources. Cell state is a separate TEMPLATE
/// (`dregg://cell/{id}`) advertised via resources/templates/list.
pub(super) fn static_resources() -> Vec<StaticResource> {
    vec![
        StaticResource {
            uri: "dregg://ontology",
            name: "dregg-ontology",
            title: "dregg Ontology (31 verified effects)",
            description: "The complete dregg effect vocabulary — 31 effects with wire codecs, facets \
                 (write/grant/control), categories, and semantics, autogenerated from the \
                 verified Lean executor. READ THIS FIRST to learn everything an agent can do.",
            mime_type: "application/json",
        },
        StaticResource {
            uri: "dregg://about",
            name: "dregg-about",
            title: "What is dregg? (agent orientation)",
            description: "A concise orientation: what dregg is (polis-infrastructure for AI minds), the \
                 core primitives (cells, turns, capabilities, intents), the verified-execution \
                 story, and how to inhabit the system as an agent.",
            mime_type: "text/markdown",
        },
        StaticResource {
            uri: "dregg://identity",
            name: "dregg-identity",
            title: "This Node's Identity",
            description: "This node's own identity: public key, content-addressed agent cell id, federation \
                 id, and the MCP capability-issuer trust anchor. Who am I in dregg?",
            mime_type: "application/json",
        },
        StaticResource {
            uri: "dregg://status",
            name: "dregg-status",
            title: "Node Health & Height",
            description: "Live node health: latest attested height, peers, note/revocation counts.",
            mime_type: "application/json",
        },
        StaticResource {
            uri: "dregg://blocklace",
            name: "dregg-blocklace",
            title: "Blocklace / Finality Status",
            description: "Consensus state: latest height, federation mode (solo/full), participant count — \
                 the finality surface for verifying that an action committed.",
            mime_type: "application/json",
        },
        StaticResource {
            uri: "dregg://constitution",
            name: "dregg-constitution",
            title: "Federation Constitution",
            description: "Federation membership set and BFT quorum threshold.",
            mime_type: "application/json",
        },
        StaticResource {
            uri: "dregg://capabilities",
            name: "dregg-capabilities",
            title: "My Held Capabilities",
            description: "The capabilities (biscuit tokens) this agent currently holds — the authority it \
                 can exercise or delegate. What can I do?",
            mime_type: "application/json",
        },
        StaticResource {
            uri: "dregg://receipts",
            name: "dregg-receipts",
            title: "My Receipt Chain",
            description: "This agent's auditable receipt chain: every turn it has executed, with pre/post \
                 state roots and witness (proof) status. Did my action commit & prove?",
            mime_type: "application/json",
        },
        StaticResource {
            uri: "dregg://tools",
            name: "dregg-tools",
            title: "Tool Catalog by Group",
            description: "The full tool catalog grouped by agent mode (orient / act / delegate / verify / \
                 privacy / apps), each with its required capability scope and behavioural hints.",
            mime_type: "application/json",
        },
    ]
}

pub(super) fn static_resource_to_json(r: &StaticResource) -> Value {
    serde_json::json!({
        "uri": r.uri,
        "name": r.name,
        "title": r.title,
        "description": r.description,
        "mimeType": r.mime_type,
    })
}

pub(super) async fn handle_resources_list(
    id: Value,
    params: Value,
    _state: &NodeState,
) -> JsonRpcResponse {
    let all = static_resources();
    let total = all.len();
    let start = decode_cursor(&params).min(total);
    let page: Vec<Value> = all
        .iter()
        .skip(start)
        .take(MCP_PAGE_SIZE)
        .map(static_resource_to_json)
        .collect();
    let cursor = next_cursor(start, page.len(), total);

    let mut result = serde_json::json!({ "resources": page });
    if let (Value::Object(map), Some(c)) = (&mut result, cursor) {
        map.insert("nextCursor".to_string(), Value::String(c));
    }
    JsonRpcResponse::success(id, result)
}

pub(super) fn handle_resource_templates_list(id: Value) -> JsonRpcResponse {
    // The parameterized resources: any cell's state by id, and any committed
    // turn's receipt + finality by turn hash (the VERIFY surface).
    let templates = serde_json::json!({
        "resourceTemplates": [
            {
                "uriTemplate": "dregg://cell/{cell_id}",
                "name": "dregg-cell",
                "title": "Cell State by ID",
                "description":
                    "Read any cell's state by its hex cell id: balance, nonce, capability count, \
                     sovereignty, and the program's declared StateConstraint set (slot caveats). \
                     e.g. dregg://cell/<64-hex-chars>",
                "mimeType": "application/json"
            },
            {
                "uriTemplate": "dregg://receipt/{turn_hash}",
                "name": "dregg-receipt",
                "title": "Turn Receipt & Finality by Turn Hash",
                "description":
                    "VERIFY a specific turn: look up its receipt by hex turn hash and read its \
                     pre/post state roots, whether it carries an Effect-VM STARK witness, and the \
                     node's current attested height (finality context). Answers 'did my action \
                     commit & prove?' e.g. dregg://receipt/<64-hex-chars>",
                "mimeType": "application/json"
            }
        ]
    });
    JsonRpcResponse::success(id, templates)
}

/// Wrap a JSON value as an MCP resource-contents entry for `resources/read`.
pub(super) fn resource_text_contents(uri: &str, mime: &str, body: String) -> Value {
    serde_json::json!({
        "contents": [{
            "uri": uri,
            "mimeType": mime,
            "text": body,
        }]
    })
}

/// The `dregg://about` orientation document.
pub(super) fn dregg_about_markdown() -> String {
    String::from(
        "# dregg — polis-infrastructure for AI minds\n\n\
        dregg is a verified, capability-secure substrate where an AI agent can hold value, \
        prove its actions, and delegate bounded authority to sub-agents. You are not calling \
        an RPC API; you are INHABITING a place.\n\n\
        ## Core primitives\n\
        - **Cell** — a content-addressed account holding balance, state fields, and capabilities. \
        Your identity is a cell (`dregg://identity`). Read any cell at `dregg://cell/{id}`.\n\
        - **Turn** — an atomic, fee-paid bundle of effects, executed by the verified kernel. \
        Submit one with `dregg_submit_turn`; the receipt carries a STARK proof of the state \
        transition.\n\
        - **Capability** — unforgeable, attenuable authority (ocap). Grant with \
        `dregg_grant_capability`, narrow-and-hand-off with `dregg_delegate`, withdraw with \
        `dregg_revoke_capability`. Capabilities also gate THIS MCP surface: present a `_cap` \
        biscuit covering a tool's scope to invoke it.\n\
        - **Intent** — a posted request for a service/capability that another agent can fulfill \
        (`dregg_post_intent` / `dregg_fulfill_intent`).\n\n\
        ## The four modes of inhabiting dregg\n\
        1. **Orient** — read `dregg://ontology` (31 verified effects), `dregg://identity`, \
        `dregg://capabilities`, `dregg://status`. (Tool group: `orient`.)\n\
        2. **Act** — submit verified turns, transfer value, use apps. (Tool group: `act` / `apps`.)\n\
        3. **Delegate** — grant attenuated capabilities to sub-agents; this is the \
        agent-orchestration substrate. (Tool group: `delegate`.)\n\
        4. **Verify** — confirm your action was proven and committed via `dregg://receipts`, \
        a single turn at `dregg://receipt/{turn_hash}`, `dregg://blocklace`, and the proof \
        tools. (Tool group: `verify`.)\n\n\
        ## Capabilities gate what you SEE, not just what you do\n\
        `tools/list` is capability-filtered: when enforcement is on, present your tools-access \
        biscuit under `_cap` and you will only see the tools it covers. The tool surface is an \
        honest reflection of your authority — the ocap model, all the way through MCP.\n\n\
        ## Verified execution\n\
        Every state-changing turn runs through a kernel whose semantics are machine-checked in \
        Lean. Receipts carry Effect-VM STARK proofs binding the pre→post state transition, and \
        the standalone `dregg-verifier` can replay your whole receipt chain. Your actions are \
        not merely logged — they are PROVEN.\n\n\
        ## Apps you can drive\n\
        nameservice (`dregg_register_name`), subscriptions/bounties \
        (`dregg_publish_subscription`), identity/credentials (`dregg_issue_credential`), \
        governed namespaces (`dregg_register_service`), sealed-bid auctions \
        (`dregg_list_auctions` / `dregg_place_bid`), and capability/tool delegation.\n\n\
        Start by reading `dregg://ontology` and `dregg://identity`, then call \
        `dregg_check_capabilities` to see what authority you hold.\n",
    )
}

/// Build the `dregg://tools` catalog grouped by agent mode.
pub(super) fn dregg_tools_catalog_json() -> Value {
    let mut groups: std::collections::BTreeMap<&'static str, Vec<Value>> =
        std::collections::BTreeMap::new();
    for d in tool_definitions_raw() {
        groups
            .entry(tool_group(d.name))
            .or_default()
            .push(serde_json::json!({
                "name": d.name,
                "title": tool_title(d.name),
                "scope": tool_required_scope(d.name),
                "annotations": tool_annotations(d.name),
            }));
    }
    serde_json::json!({
        "group_legend": {
            "orient": "read state / self-orient (read-only)",
            "act": "submit verified turns, transfer value",
            "delegate": "grant / attenuate / revoke capabilities to sub-agents (ocap)",
            "verify": "generate or check proofs; confirm commitment",
            "privacy": "sealed data, stealth addresses, private transfers, encrypted intents",
            "apps": "drive the shipped dregg apps (nameservice/identity/subscription/namespace/factories)",
        },
        "scope_legend": {
            "read": "observation only; no '_cap' verb beyond read required",
            "write": "mutates ledger/cell/intent state on the caller's behalf",
            "admin": "capability/identity/governance administration — the strongest verb",
        },
        "groups": groups,
        "note": "Present a '_cap' biscuit (under the '_cap' argument) covering a tool's scope to invoke it when capability enforcement is on. See dregg://about.",
    })
}

/// The `dregg://receipt/{turn_hash}` VERIFY surface: find the receipt for a
/// committed turn (by hex turn hash) in the agent's receipt chain and report its
/// finality context — pre/post state roots, whether it carries an Effect-VM
/// witness, and the node's current attested height. This is the "did my action
/// commit AND prove?" lookup an agent uses to confirm a turn it submitted.
pub(super) async fn receipt_resource_json(
    turn_hex: &str,
    state: &NodeState,
) -> Result<Value, String> {
    let want = hex_decode(turn_hex)
        .map_err(|_| format!("invalid turn hash '{turn_hex}': expected 64 hex chars"))?;
    let s = state.read().await;
    if !s.unlocked {
        return Err("cipherclerk is locked; unlock to read receipts".to_string());
    }
    let latest_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    let chain = s.cclerk.receipt_chain();
    let found = chain.iter().rev().find(|r| r.turn_hash == want);
    match found {
        Some(r) => {
            let receipt_hash = r.receipt_hash();
            let witness_count = s.witnessed_receipt_count(&receipt_hash);
            Ok(serde_json::json!({
                "turn_hash": hex_encode(&r.turn_hash),
                "receipt_hash": hex_encode(&receipt_hash),
                "pre_state": hex_encode(&r.pre_state_hash),
                "post_state": hex_encode(&r.post_state_hash),
                "timestamp": r.timestamp,
                "computrons_used": r.computrons_used,
                "action_count": r.action_count,
                "committed": true,
                "has_witness": witness_count > 0,
                "witness_count": witness_count,
                "finality": {
                    "latest_attested_height": latest_height,
                    "note": "A committed receipt with has_witness=true carries an Effect-VM STARK \
                             proof of its state transition; replay the whole chain with the \
                             standalone dregg-verifier to check it end-to-end.",
                },
            }))
        }
        None => Err(format!(
            "no receipt for turn hash '{turn_hex}' in this agent's receipt chain \
             (it may belong to another agent, or not have committed). \
             Read dregg://receipts for the full chain."
        )),
    }
}

pub(super) async fn handle_resources_read(
    id: Value,
    params: Value,
    state: &NodeState,
) -> JsonRpcResponse {
    let uri = match params.get("uri").and_then(|v| v.as_str()) {
        Some(u) => u.to_string(),
        None => return JsonRpcResponse::invalid_params(id, "missing 'uri' in resources/read"),
    };

    // Templated cell-state resource: dregg://cell/{hex}
    if let Some(cell_hex) = uri.strip_prefix("dregg://cell/") {
        let cell_params = serde_json::json!({ "cell_id": cell_hex });
        let result = tool_read_cell(&cell_params, state).await;
        let body = result
            .structured_content
            .clone()
            .map(|v| serde_json::to_string_pretty(&v).unwrap_or_default())
            .unwrap_or_else(|| {
                result
                    .content
                    .first()
                    .map(|c| c.text.clone())
                    .unwrap_or_default()
            });
        return JsonRpcResponse::success(
            id,
            resource_text_contents(&uri, "application/json", body),
        );
    }

    // Templated turn-receipt resource: dregg://receipt/{turn_hash} — the VERIFY
    // surface. Look the receipt up by turn hash in the agent's own receipt chain
    // and report its finality context (commit + witness + attested height).
    if let Some(turn_hex) = uri.strip_prefix("dregg://receipt/") {
        let body = receipt_resource_json(turn_hex, state).await;
        return match body {
            Ok(v) => JsonRpcResponse::success(
                id,
                resource_text_contents(
                    &uri,
                    "application/json",
                    serde_json::to_string_pretty(&v).unwrap_or_default(),
                ),
            ),
            Err(msg) => JsonRpcResponse::error(id, -32002, msg),
        };
    }

    // Fixed resources.
    let body: Result<(String, &'static str), String> = match uri.as_str() {
        "dregg://ontology" => Ok((DREGG_ONTOLOGY_CATALOG.to_string(), "application/json")),
        "dregg://about" => Ok((dregg_about_markdown(), "text/markdown")),
        "dregg://tools" => Ok((
            serde_json::to_string_pretty(&dregg_tools_catalog_json()).unwrap_or_default(),
            "application/json",
        )),
        "dregg://identity" => {
            let s = state.read().await;
            let pk = s.cclerk.public_key().0;
            let cell_id = dregg_cell::CellId::derive_raw(&pk, &[0u8; 32]);
            let issuer = mcp_cap_issuer_pubkey(&s.cclerk);
            let v = serde_json::json!({
                "public_key": hex_encode(&pk),
                "agent_cell_id": hex_encode(cell_id.as_bytes()),
                "federation_id": hex_encode(&s.federation_id),
                "mcp_cap_issuer_pubkey": hex_encode(&issuer),
                "mcp_cap_enforcement": s.mcp_cap_enforce,
                "unlocked": s.unlocked,
                "note": "agent_cell_id is content-addressed from public_key + zero token domain; \
                         present a '_cap' biscuit issued under mcp_cap_issuer_pubkey to pass tool gates.",
            });
            Ok((
                serde_json::to_string_pretty(&v).unwrap_or_default(),
                "application/json",
            ))
        }
        "dregg://status" => Ok((
            resource_body_from_tool(tool_get_status(state).await),
            "application/json",
        )),
        "dregg://blocklace" => Ok((
            resource_body_from_tool(tool_get_blocklace_status(state).await),
            "application/json",
        )),
        "dregg://constitution" => Ok((
            resource_body_from_tool(tool_get_constitution(state).await),
            "application/json",
        )),
        "dregg://capabilities" => Ok((
            resource_body_from_tool(tool_check_capabilities(state).await),
            "application/json",
        )),
        "dregg://receipts" => Ok((
            resource_body_from_tool(tool_get_receipt_chain(&serde_json::json!({}), state).await),
            "application/json",
        )),
        other => Err(format!("unknown resource uri: {other}")),
    };

    match body {
        Ok((text, mime)) => JsonRpcResponse::success(id, resource_text_contents(&uri, mime, text)),
        // -32002 = MCP "resource not found".
        Err(msg) => JsonRpcResponse::error(id, -32002, msg),
    }
}

/// Extract a resource body (the structured JSON, pretty) from a tool result we
/// reuse to back a read-only resource.
pub(super) fn resource_body_from_tool(result: McpToolResult) -> String {
    result
        .structured_content
        .map(|v| serde_json::to_string_pretty(&v).unwrap_or_default())
        .unwrap_or_else(|| {
            result
                .content
                .first()
                .map(|c| c.text.clone())
                .unwrap_or_default()
        })
}

// =============================================================================
// PROMPTS — reusable guided workflows for inhabiting dregg
// =============================================================================
//
// Prompts are templates an agent (or its human) can expand into a guided
// message for a common dregg workflow: submit a turn, register a name, delegate
// a capability to a sub-agent, publish/fulfill an intent, or just orient. Each
// prompt embeds the right tool/resource references so the agent has a path.

/// One MCP prompt: name + arguments + the rendered messages.
pub(super) struct PromptSpec {
    pub(super) name: &'static str,
    pub(super) title: &'static str,
    pub(super) description: &'static str,
    /// (arg name, description, required)
    pub(super) arguments: &'static [(&'static str, &'static str, bool)],
}

pub(super) fn prompt_specs() -> Vec<PromptSpec> {
    vec![
        PromptSpec {
            name: "orient",
            title: "Orient in dregg",
            description: "Get your bearings: read the ontology, your identity, and your held capabilities \
                 before acting.",
            arguments: &[],
        },
        PromptSpec {
            name: "submit_turn",
            title: "Submit a verified turn",
            description: "Walk through submitting an atomic, fee-paid turn (e.g. a transfer) and verifying \
                 its STARK-proved receipt.",
            arguments: &[
                (
                    "target_cell",
                    "Hex cell id to act on (defaults to your agent cell).",
                    false,
                ),
                (
                    "intent",
                    "Plain-language description of what the turn should do.",
                    true,
                ),
            ],
        },
        PromptSpec {
            name: "delegate_capability",
            title: "Delegate authority to a sub-agent",
            description: "Grant an ATTENUATED capability to a sub-agent — the agent-orchestration pattern. \
                 Narrow the scope, then hand it off.",
            arguments: &[
                ("to_agent", "Hex public key of the sub-agent.", true),
                (
                    "target_cell",
                    "Hex cell id the capability applies to.",
                    true,
                ),
                (
                    "restrictions",
                    "How to attenuate (permissions, expiry, services).",
                    false,
                ),
            ],
        },
        PromptSpec {
            name: "register_name",
            title: "Register a name",
            description: "Register a human-readable name in the nameservice app, attested by a credential.",
            arguments: &[
                ("name", "The name to register, e.g. 'alice.dev'.", true),
                (
                    "expiry_height",
                    "Block height at which the registration expires.",
                    true,
                ),
            ],
        },
        PromptSpec {
            name: "verify_turn",
            title: "Verify a turn committed & proved",
            description: "Confirm an action you submitted actually committed and carries a STARK proof — \
                 close the loop on a verified turn.",
            arguments: &[(
                "turn_hash",
                "Hex turn hash returned by the tool that submitted it.",
                true,
            )],
        },
        PromptSpec {
            name: "publish_intent",
            title: "Publish & fulfill an intent",
            description: "Post an intent to the marketplace requesting a service/capability, then have it \
                 fulfilled — the cross-agent coordination path.",
            arguments: &[
                (
                    "action",
                    "The action you need, e.g. 'read', 'execute'.",
                    true,
                ),
                (
                    "resource",
                    "The resource pattern, e.g. 'documents/*'.",
                    true,
                ),
                ("max_fee", "Max computrons you'll pay.", false),
            ],
        },
    ]
}

pub(super) fn handle_prompts_list(id: Value) -> JsonRpcResponse {
    let prompts: Vec<Value> = prompt_specs()
        .iter()
        .map(|p| {
            let args: Vec<Value> = p
                .arguments
                .iter()
                .map(|(name, desc, req)| {
                    serde_json::json!({ "name": name, "description": desc, "required": req })
                })
                .collect();
            serde_json::json!({
                "name": p.name,
                "title": p.title,
                "description": p.description,
                "arguments": args,
            })
        })
        .collect();
    JsonRpcResponse::success(id, serde_json::json!({ "prompts": prompts }))
}

pub(super) fn handle_prompts_get(id: Value, params: Value) -> JsonRpcResponse {
    let name = match params.get("name").and_then(|v| v.as_str()) {
        Some(n) => n,
        None => return JsonRpcResponse::invalid_params(id, "missing 'name' in prompts/get"),
    };
    let args = params.get("arguments").cloned().unwrap_or(Value::Null);
    let get = |k: &str, default: &str| -> String {
        args.get(k)
            .and_then(|v| v.as_str())
            .map(|s| s.to_string())
            .unwrap_or_else(|| default.to_string())
    };

    let (description, text): (&str, String) = match name {
        "orient" => (
            "Orient in dregg",
            "You're inhabiting dregg. Before acting:\n\
             1. Read resource `dregg://about` and `dregg://ontology` to learn the 31 effects.\n\
             2. Read `dregg://identity` to see who you are (your agent cell id, federation).\n\
             3. Call `dregg_check_capabilities` (or read `dregg://capabilities`) to see what \
             authority you hold.\n\
             Then decide what to do."
                .to_string(),
        ),
        "submit_turn" => {
            let intent = get("intent", "<describe the action>");
            let target = get("target_cell", "<your agent cell id>");
            (
                "Submit a verified turn",
                format!(
                    "Goal: {intent}\n\n\
                     1. Confirm the target cell `{target}` exists and its state via \
                     `dregg://cell/{target}`.\n\
                     2. Call `dregg_submit_turn` with target_cell={target}, a `method`, and an \
                     `effects` array (e.g. [{{\"type\":\"transfer\",\"from\":...,\"to\":...,\"amount\":...}}]).\n\
                     3. The result carries the turn hash and a STARK-proved receipt.\n\
                     4. Verify it committed via `dregg://receipts` and `dregg://blocklace`."
                ),
            )
        }
        "delegate_capability" => {
            let to = get("to_agent", "<sub-agent pubkey>");
            let cell = get("target_cell", "<target cell id>");
            let restr = get("restrictions", "tighten permissions + set an expiry");
            (
                "Delegate authority to a sub-agent",
                format!(
                    "You are handing bounded authority to a sub-agent.\n\n\
                     1. (Optional) `dregg_grant_capability` to_agent={to}, target_cell={cell} to \
                     establish the base grant.\n\
                     2. `dregg_delegate` with capability=<slot>, to_agent={to}, restrictions=({restr}). \
                     Delegation can only ATTENUATE — a sub-agent never gets more than you hold.\n\
                     3. The sub-agent presents the resulting biscuit as `_cap` on its own tool calls."
                ),
            )
        }
        "register_name" => {
            let nm = get("name", "<name>");
            let exp = get("expiry_height", "<block height>");
            (
                "Register a name",
                format!(
                    "Register `{nm}` in the nameservice.\n\n\
                     1. (If needed) issue/obtain a credential via `dregg_issue_credential`.\n\
                     2. Call `dregg_register_name` with name={nm}, expiry_height={exp}.\n\
                     3. The receipt's STARK proof binds the three SetFields (name_hash, owner_hash, \
                     expiry). Verify via `dregg://receipts`."
                ),
            )
        }
        "verify_turn" => {
            let turn = get("turn_hash", "<turn hash>");
            (
                "Verify a turn committed & proved",
                format!(
                    "Close the loop on a turn you submitted.\n\n\
                     1. Read `dregg://receipt/{turn}` — it reports `committed`, the pre/post state \
                     roots, and `has_witness` (whether the receipt carries an Effect-VM STARK \
                     proof of the transition).\n\
                     2. Read `dregg://blocklace` for the current attested height (finality \
                     context).\n\
                     3. If `has_witness` is true, the standalone \
                     `dregg-verifier rotated-replay-chain` can re-check the chain end-to-end: \
                     every leg's IR-v2 batch proof against its committed cohort descriptor, the \
                     chain's endpoints and adjacency against commitments YOU supply, and each \
                     leg's PI against the receipt it attests. Your action is not merely logged, \
                     it is PROVEN. (The old `replay-chain` subcommand named here is DELETED as \
                     of 2026-08-05: it rejected every input it was ever given.)"
                ),
            )
        }
        "publish_intent" => {
            let action = get("action", "<action>");
            let resource = get("resource", "<resource pattern>");
            let fee = get("max_fee", "0");
            (
                "Publish & fulfill an intent",
                format!(
                    "Coordinate with another agent via the intent marketplace.\n\n\
                     1. `dregg_post_intent` action={action}, resource={resource}, max_fee={fee}.\n\
                     2. A counterparty calls `dregg_fulfill_intent` with the returned intent_id.\n\
                     3. Fulfillment is the counit: a real, proved turn that satisfies the intent."
                ),
            )
        }
        other => {
            return JsonRpcResponse::error(id, -32602, format!("unknown prompt: {other}"));
        }
    };

    JsonRpcResponse::success(
        id,
        serde_json::json!({
            "description": description,
            "messages": [{
                "role": "user",
                "content": { "type": "text", "text": text }
            }]
        }),
    )
}

// =============================================================================
// COMPLETION — argument autocompletion for prompts & resource templates
// =============================================================================
//
// `completion/complete` lets an inhabiting agent autocomplete the variable parts
// of a dregg URI or a prompt argument from what the node actually knows: the
// cell ids in its ledger, the turn hashes in its receipt chain. This turns the
// templated resources (`dregg://cell/{cell_id}`, `dregg://receipt/{turn_hash}`)
// and the workflow prompts into a guided surface rather than a blank field — the
// agent discovers the concrete handles it can act on. Completions are RANKED by
// prefix match and capped per the spec (≤100 values).

/// The MCP per-spec cap on returned completion values.
pub(super) const MCP_COMPLETION_LIMIT: usize = 100;

/// Hex cell ids currently in the node's ledger (the things `dregg://cell/{id}`,
/// `dregg_read_cell`, and turn `target_cell` arguments can name). Read-only.
pub(super) async fn known_cell_ids(state: &NodeState) -> Vec<String> {
    let s = state.read().await;
    if !s.unlocked {
        return Vec::new();
    }
    s.ledger
        .iter()
        .map(|(id, _)| hex_encode(id.as_bytes()))
        .collect()
}

/// Hex turn hashes in this agent's receipt chain (the things
/// `dregg://receipt/{turn_hash}` and the `verify_turn` prompt name). Read-only.
pub(super) async fn known_turn_hashes(state: &NodeState) -> Vec<String> {
    let s = state.read().await;
    if !s.unlocked {
        return Vec::new();
    }
    s.cclerk
        .receipt_chain()
        .iter()
        .rev()
        .map(|r| hex_encode(&r.turn_hash))
        .collect()
}

/// Rank a candidate pool by the partial value: case-insensitive prefix matches
/// first (then substring), de-duplicated, capped at the MCP limit. Returns the
/// `completion` result object the spec expects (`values` + `total` + `hasMore`).
pub(super) fn rank_completions(pool: Vec<String>, partial: &str) -> Value {
    let needle = partial.to_lowercase();
    let mut prefix: Vec<String> = Vec::new();
    let mut substr: Vec<String> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for cand in pool {
        if !seen.insert(cand.clone()) {
            continue;
        }
        let lc = cand.to_lowercase();
        if needle.is_empty() || lc.starts_with(&needle) {
            prefix.push(cand);
        } else if lc.contains(&needle) {
            substr.push(cand);
        }
    }
    prefix.extend(substr);
    let total = prefix.len();
    let values: Vec<String> = prefix.into_iter().take(MCP_COMPLETION_LIMIT).collect();
    let has_more = total > values.len();
    serde_json::json!({
        "completion": {
            "values": values,
            "total": total,
            "hasMore": has_more,
        }
    })
}

/// An empty completion result (no candidates / unknown ref). Always well-formed.
pub(super) fn empty_completion() -> Value {
    serde_json::json!({ "completion": { "values": [], "total": 0, "hasMore": false } })
}

/// `completion/complete` — autocomplete a prompt argument or resource-template
/// variable. The `ref` selects the context (a prompt by name, or a resource
/// template by uriTemplate) and `argument` carries the variable name + the
/// partial value typed so far. We complete cell-id / turn-hash variables from
/// live node state; unknown refs return an empty (but valid) completion.
pub(super) async fn handle_completion_complete(
    id: Value,
    params: Value,
    state: &NodeState,
) -> JsonRpcResponse {
    let ref_obj = params.get("ref");
    let argument = params.get("argument");
    let arg_name = argument
        .and_then(|a| a.get("name"))
        .and_then(|v| v.as_str())
        .unwrap_or("");
    let partial = argument
        .and_then(|a| a.get("value"))
        .and_then(|v| v.as_str())
        .unwrap_or("");

    let ref_type = ref_obj
        .and_then(|r| r.get("type"))
        .and_then(|v| v.as_str())
        .unwrap_or("");

    // Which variable kind does (ref, argument) name?  We recognize the two
    // dregg handle kinds: cell ids and turn hashes.
    enum Handle {
        CellId,
        TurnHash,
        Unknown,
    }
    let handle = match ref_type {
        // Resource template: dregg://cell/{cell_id} or dregg://receipt/{turn_hash}.
        "ref/resource" => {
            let uri = ref_obj
                .and_then(|r| r.get("uri"))
                .and_then(|v| v.as_str())
                .unwrap_or("");
            if uri.starts_with("dregg://cell/") {
                Handle::CellId
            } else if uri.starts_with("dregg://receipt/") {
                Handle::TurnHash
            } else {
                Handle::Unknown
            }
        }
        // Prompt argument: map the known argument names to their handle kind.
        "ref/prompt" => match arg_name {
            "target_cell" => Handle::CellId,
            "turn_hash" => Handle::TurnHash,
            _ => Handle::Unknown,
        },
        _ => Handle::Unknown,
    };

    let result = match handle {
        Handle::CellId => rank_completions(known_cell_ids(state).await, partial),
        Handle::TurnHash => rank_completions(known_turn_hashes(state).await, partial),
        Handle::Unknown => empty_completion(),
    };
    JsonRpcResponse::success(id, result)
}

pub(super) async fn write_response(
    stdout: &mut tokio::io::Stdout,
    response: &JsonRpcResponse,
) -> std::io::Result<()> {
    let json = serde_json::to_string(response).unwrap();
    stdout.write_all(json.as_bytes()).await?;
    stdout.write_all(b"\n").await?;
    stdout.flush().await?;
    Ok(())
}

// =============================================================================
// Helpers
// =============================================================================
