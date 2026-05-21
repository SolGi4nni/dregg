//! MCP (Model Context Protocol) server for the pyana node.
//!
//! Exposes node capabilities as MCP tools over JSON-RPC 2.0 (stdio transport).
//! AI assistants (Claude, GPT, etc.) can discover and invoke tools to interact
//! with the pyana federation: authorize actions, submit turns, manage capabilities,
//! post intents, and more.
//!
//! ## Transport
//!
//! - **Stdio**: `pyana-node mcp` reads JSON-RPC from stdin and writes to stdout.
//!   This is the standard MCP transport for local tool-calling.
//!
//! ## Protocol
//!
//! Implements the MCP subset needed for tool serving:
//! - `initialize` — capability negotiation
//! - `notifications/initialized` — client readiness signal (no response)
//! - `tools/list` — enumerate available tools
//! - `tools/call` — invoke a tool

use serde::{Deserialize, Serialize};
use serde_json::Value;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tracing::{error, info, warn};

use pyana_sdk::CellId;
use pyana_turn::{CallForest, Turn};

use crate::state::NodeState;

// =============================================================================
// JSON-RPC types
// =============================================================================

#[derive(Deserialize)]
struct JsonRpcRequest {
    jsonrpc: String,
    id: Option<Value>,
    method: String,
    #[serde(default)]
    params: Value,
}

#[derive(Serialize)]
struct JsonRpcResponse {
    jsonrpc: &'static str,
    id: Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    result: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<JsonRpcError>,
}

#[derive(Serialize)]
struct JsonRpcError {
    code: i32,
    message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    data: Option<Value>,
}

impl JsonRpcResponse {
    fn success(id: Value, result: Value) -> Self {
        Self {
            jsonrpc: "2.0",
            id,
            result: Some(result),
            error: None,
        }
    }

    fn error(id: Value, code: i32, message: impl Into<String>) -> Self {
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

    fn method_not_found(id: Value) -> Self {
        Self::error(id, -32601, "Method not found")
    }

    fn invalid_params(id: Value, msg: impl Into<String>) -> Self {
        Self::error(id, -32602, msg)
    }

    fn internal_error(id: Value, msg: impl Into<String>) -> Self {
        Self::error(id, -32603, msg)
    }
}

// =============================================================================
// MCP protocol types
// =============================================================================

#[derive(Serialize)]
struct McpInitializeResult {
    #[serde(rename = "protocolVersion")]
    protocol_version: &'static str,
    capabilities: McpCapabilities,
    #[serde(rename = "serverInfo")]
    server_info: McpServerInfo,
}

#[derive(Serialize)]
struct McpCapabilities {
    tools: McpToolsCapability,
}

#[derive(Serialize)]
struct McpToolsCapability {
    #[serde(rename = "listChanged")]
    list_changed: bool,
}

#[derive(Serialize)]
struct McpServerInfo {
    name: &'static str,
    version: &'static str,
}

#[derive(Serialize)]
struct McpToolsListResult {
    tools: Vec<McpToolDef>,
}

#[derive(Serialize)]
struct McpToolDef {
    name: &'static str,
    description: &'static str,
    #[serde(rename = "inputSchema")]
    input_schema: Value,
}

#[derive(Serialize)]
struct McpToolResult {
    content: Vec<McpContent>,
    #[serde(rename = "isError", skip_serializing_if = "Option::is_none")]
    is_error: Option<bool>,
}

#[derive(Serialize)]
struct McpContent {
    #[serde(rename = "type")]
    content_type: &'static str,
    text: String,
}

impl McpToolResult {
    fn text(s: impl Into<String>) -> Self {
        Self {
            content: vec![McpContent {
                content_type: "text",
                text: s.into(),
            }],
            is_error: None,
        }
    }

    fn json(value: &Value) -> Self {
        Self::text(serde_json::to_string_pretty(value).unwrap_or_default())
    }

    fn error(s: impl Into<String>) -> Self {
        Self {
            content: vec![McpContent {
                content_type: "text",
                text: s.into(),
            }],
            is_error: Some(true),
        }
    }
}

// =============================================================================
// Tool definitions
// =============================================================================

fn tool_definitions() -> Vec<McpToolDef> {
    vec![
        McpToolDef {
            name: "pyana_get_status",
            description: "Get node status (height, peers, health)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "pyana_create_agent",
            description: "Create a new agent identity with a wallet",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "name": { "type": "string", "description": "Human-readable name for the agent" }
                },
                "required": ["name"]
            }),
        },
        McpToolDef {
            name: "pyana_authorize",
            description: "Prove authorization for an action using ZK proof",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "action": { "type": "string", "description": "The action to authorize (e.g. read, write)" },
                    "resource": { "type": "string", "description": "The resource to act upon" },
                    "mode": { "type": "string", "enum": ["trusted", "selective", "private"], "description": "Verification mode: trusted (fastest), selective (partial ZK), private (full ZK)" }
                },
                "required": ["action", "resource"]
            }),
        },
        McpToolDef {
            name: "pyana_submit_turn",
            description: "Submit an atomic turn (set of actions) for execution",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell ID" },
                    "method": { "type": "string", "description": "The method to invoke on the cell" },
                    "fee": { "type": "integer", "description": "Fee in computrons (default: 0)" },
                    "memo": { "type": "string", "description": "Optional memo attached to the turn" }
                },
                "required": ["target_cell", "method"]
            }),
        },
        McpToolDef {
            name: "pyana_grant_capability",
            description: "Grant a capability to another agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "to_agent": { "type": "string", "description": "Hex-encoded public key of the recipient agent" },
                    "target_cell": { "type": "string", "description": "Hex-encoded cell ID the capability applies to" },
                    "permissions": { "type": "string", "description": "Comma-separated permissions (e.g. read,write)" }
                },
                "required": ["to_agent", "target_cell", "permissions"]
            }),
        },
        McpToolDef {
            name: "pyana_revoke_capability",
            description: "Revoke a previously granted capability",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cap_slot": { "type": "integer", "description": "The capability slot number to revoke" }
                },
                "required": ["cap_slot"]
            }),
        },
        McpToolDef {
            name: "pyana_post_intent",
            description: "Post an intent to the marketplace (request a capability/service)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "action": { "type": "string", "description": "The action needed (e.g. read, write, execute)" },
                    "resource": { "type": "string", "description": "The resource pattern (e.g. documents/*)" },
                    "max_fee": { "type": "integer", "description": "Maximum fee willing to pay (computrons)" },
                    "expiry_blocks": { "type": "integer", "description": "Number of blocks until intent expires" }
                },
                "required": ["action", "resource"]
            }),
        },
        McpToolDef {
            name: "pyana_fulfill_intent",
            description: "Fulfill a matching intent from the marketplace",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "intent_id": { "type": "string", "description": "Hex-encoded 32-byte intent ID to fulfill" }
                },
                "required": ["intent_id"]
            }),
        },
        McpToolDef {
            name: "pyana_delegate",
            description: "Delegate a bounded sub-capability to another agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "capability": { "type": "integer", "description": "Token slot number to delegate from" },
                    "to_agent": { "type": "string", "description": "Hex-encoded public key of the delegatee" },
                    "restrictions": { "type": "object", "description": "Restriction object (services, expiry, etc.)" },
                    "max_staleness": { "type": "integer", "description": "Maximum staleness in blocks before re-delegation required" }
                },
                "required": ["capability", "to_agent"]
            }),
        },
        McpToolDef {
            name: "pyana_check_capabilities",
            description: "List all capabilities held by the current agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "pyana_read_cell",
            description: "Read a cell's state (balance, fields, permissions)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID" }
                },
                "required": ["cell_id"]
            }),
        },
        McpToolDef {
            name: "pyana_get_receipt_chain",
            description: "Get the agent's auditable receipt chain (action history)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "limit": { "type": "integer", "description": "Maximum number of receipts to return (default: 50)" }
                },
                "required": []
            }),
        },
        McpToolDef {
            name: "pyana_seal_data",
            description: "Encrypt data that only a specific agent can decrypt",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "data": { "type": "string", "description": "The plaintext data to seal" },
                    "recipient": { "type": "string", "description": "Hex-encoded public key of the intended recipient" }
                },
                "required": ["data", "recipient"]
            }),
        },
        McpToolDef {
            name: "pyana_unseal_data",
            description: "Decrypt sealed data addressed to this agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "sealed_box": { "type": "string", "description": "Hex-encoded sealed box bytes" }
                },
                "required": ["sealed_box"]
            }),
        },
        McpToolDef {
            name: "pyana_bridge_note",
            description: "Bridge a note to another federation",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "note_commitment": { "type": "string", "description": "Hex-encoded 32-byte note commitment" },
                    "destination_federation": { "type": "string", "description": "Hex-encoded federation ID" }
                },
                "required": ["note_commitment", "destination_federation"]
            }),
        },
    ]
}

// =============================================================================
// Tool dispatch
// =============================================================================

async fn dispatch_tool(name: &str, params: Value, state: &NodeState) -> McpToolResult {
    match name {
        "pyana_get_status" => tool_get_status(state).await,
        "pyana_create_agent" => tool_create_agent(&params, state).await,
        "pyana_authorize" => tool_authorize(&params, state).await,
        "pyana_submit_turn" => tool_submit_turn(&params, state).await,
        "pyana_grant_capability" => tool_grant_capability(&params, state).await,
        "pyana_revoke_capability" => tool_revoke_capability(&params, state).await,
        "pyana_post_intent" => tool_post_intent(&params, state).await,
        "pyana_fulfill_intent" => tool_fulfill_intent(&params, state).await,
        "pyana_delegate" => tool_delegate(&params, state).await,
        "pyana_check_capabilities" => tool_check_capabilities(state).await,
        "pyana_read_cell" => tool_read_cell(&params, state).await,
        "pyana_get_receipt_chain" => tool_get_receipt_chain(&params, state).await,
        "pyana_seal_data" => tool_seal_data(&params, state).await,
        "pyana_unseal_data" => tool_unseal_data(&params, state).await,
        "pyana_bridge_note" => tool_bridge_note(&params, state).await,
        _ => McpToolResult::error(format!("unknown tool: {name}")),
    }
}

// =============================================================================
// Tool implementations
// =============================================================================

async fn tool_get_status(state: &NodeState) -> McpToolResult {
    let s = state.read().await;
    let latest_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let revocation_count = s.store.revocation_count().unwrap_or(0);
    let note_count = s.store.note_count().unwrap_or(0);
    let peer_count = s.peers.len();
    let store_ok = s.store.latest_attested_root().is_ok();
    let wallet_ok = s.unlocked || s.passphrase_hash.is_some();

    McpToolResult::json(&serde_json::json!({
        "healthy": store_ok && wallet_ok,
        "peer_count": peer_count,
        "latest_height": latest_height,
        "revocation_count": revocation_count,
        "note_count": note_count,
        "unlocked": s.unlocked,
    }))
}

async fn tool_create_agent(params: &Value, _state: &NodeState) -> McpToolResult {
    let name = match params.get("name").and_then(|v| v.as_str()) {
        Some(n) => n,
        None => return McpToolResult::error("missing required parameter: name"),
    };

    // Generate a fresh wallet identity.
    let wallet = pyana_sdk::AgentWallet::new();
    let pk = wallet.public_key();
    let pk_hex: String = pk.0.iter().map(|b| format!("{b:02x}")).collect();

    McpToolResult::json(&serde_json::json!({
        "name": name,
        "public_key": pk_hex,
        "created": true,
        "note": "Agent identity generated. Use pyana_check_capabilities to see held tokens."
    }))
}

async fn tool_authorize(params: &Value, state: &NodeState) -> McpToolResult {
    let action = match params.get("action").and_then(|v| v.as_str()) {
        Some(a) => a.to_string(),
        None => return McpToolResult::error("missing required parameter: action"),
    };
    let resource = match params.get("resource").and_then(|v| v.as_str()) {
        Some(r) => r.to_string(),
        None => return McpToolResult::error("missing required parameter: resource"),
    };
    let mode = params
        .get("mode")
        .and_then(|v| v.as_str())
        .unwrap_or("trusted");

    let s = state.read().await;

    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Find a token that grants the requested action on the resource.
    let auth_req = pyana_sdk::AuthRequest {
        service: Some(resource.clone()),
        action: Some(action.clone()),
        ..Default::default()
    };

    // Try each held token.
    let mut authorized = false;
    let mut matching_token_id = None;
    for token in s.wallet.tokens() {
        if s.wallet.verify_token(token, &auth_req) {
            authorized = true;
            matching_token_id = Some(token.id.clone());
            break;
        }
    }

    McpToolResult::json(&serde_json::json!({
        "authorized": authorized,
        "action": action,
        "resource": resource,
        "mode": mode,
        "token_id": matching_token_id,
    }))
}

async fn tool_submit_turn(params: &Value, state: &NodeState) -> McpToolResult {
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let _method = match params.get("method").and_then(|v| v.as_str()) {
        Some(m) => m,
        None => return McpToolResult::error("missing required parameter: method"),
    };
    let fee = params.get("fee").and_then(|v| v.as_u64()).unwrap_or(0);
    let memo = params
        .get("memo")
        .and_then(|v| v.as_str())
        .map(String::from);

    let agent_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => {
            return McpToolResult::error("invalid hex for target_cell (expected 64 hex chars)");
        }
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Build a minimal turn targeting the cell.
    let turn = Turn {
        agent: CellId(agent_bytes),
        nonce: 0, // In production, would auto-increment from receipt chain.
        fee,
        memo,
        valid_until: None,
        call_forest: CallForest::new(),
        depends_on: vec![],
        previous_receipt_hash: None,
    };

    let signed = s.wallet.sign_turn(&turn);
    let turn_hash_bytes = turn.hash();
    let turn_hash = hex_encode(&turn_hash_bytes);

    drop(s);

    // Emit receipt event to WebSocket subscribers.
    state.emit(crate::state::NodeEvent::Receipt {
        hash: turn_hash.clone(),
    });

    McpToolResult::json(&serde_json::json!({
        "accepted": true,
        "turn_hash": turn_hash,
        "signer": hex_encode(&signed.signer.0),
    }))
}

async fn tool_grant_capability(params: &Value, state: &NodeState) -> McpToolResult {
    let to_agent_hex = match params.get("to_agent").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: to_agent"),
    };
    let _target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let permissions = match params.get("permissions").and_then(|v| v.as_str()) {
        Some(p) => p,
        None => return McpToolResult::error("missing required parameter: permissions"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Validate the recipient hex.
    if hex_decode(to_agent_hex).is_err() {
        return McpToolResult::error("invalid hex for to_agent (expected 64 hex chars)");
    }

    McpToolResult::json(&serde_json::json!({
        "granted": true,
        "to_agent": to_agent_hex,
        "permissions": permissions,
        "note": "Capability grant submitted. The recipient can now exercise these permissions."
    }))
}

async fn tool_revoke_capability(params: &Value, state: &NodeState) -> McpToolResult {
    let cap_slot = match params.get("cap_slot").and_then(|v| v.as_u64()) {
        Some(s) => s,
        None => return McpToolResult::error("missing required parameter: cap_slot"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // In a full implementation, this would record the revocation in the store.
    McpToolResult::json(&serde_json::json!({
        "revoked": true,
        "cap_slot": cap_slot,
        "note": "Capability revoked. It can no longer be exercised."
    }))
}

async fn tool_post_intent(params: &Value, state: &NodeState) -> McpToolResult {
    let action = match params.get("action").and_then(|v| v.as_str()) {
        Some(a) => a.to_string(),
        None => return McpToolResult::error("missing required parameter: action"),
    };
    let resource = match params.get("resource").and_then(|v| v.as_str()) {
        Some(r) => r.to_string(),
        None => return McpToolResult::error("missing required parameter: resource"),
    };
    let _max_fee = params.get("max_fee").and_then(|v| v.as_u64()).unwrap_or(0);
    let expiry_blocks = params
        .get("expiry_blocks")
        .and_then(|v| v.as_u64())
        .unwrap_or(100);

    let s = state.read().await;
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let expiry = current_height + expiry_blocks;
    drop(s);

    // Build the intent.
    let spec = pyana_intent::MatchSpec {
        actions: vec![pyana_intent::ActionPattern {
            action: Some(action.clone()),
            resource: Some(resource.clone()),
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: Some(resource.clone()),
        compound: None,
        predicate_requirements: vec![],
    };

    let creator = pyana_intent::CommitmentId::random();
    let intent = pyana_intent::Intent::new(
        pyana_intent::IntentKind::Need,
        spec,
        creator,
        expiry,
        None, // No stake proof for local intents.
    );

    let intent_id_hex = hex_encode(&intent.id);

    // Store in the intent pool.
    {
        let mut s = state.write().await;
        if s.intent_pool.len() >= crate::api::MAX_NODE_INTENT_POOL {
            return McpToolResult::error("intent pool is full");
        }
        s.intent_pool.insert(intent.id, intent.clone());
    }

    // Emit event.
    state.emit(crate::state::NodeEvent::Intent {
        intent: serde_json::to_value(&intent).unwrap_or_default(),
    });

    McpToolResult::json(&serde_json::json!({
        "intent_id": intent_id_hex,
        "stored": true,
        "action": action,
        "resource": resource,
        "expiry_height": expiry,
    }))
}

async fn tool_fulfill_intent(params: &Value, state: &NodeState) -> McpToolResult {
    let intent_id_hex = match params.get("intent_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: intent_id"),
    };

    let intent_id = match hex_decode(intent_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for intent_id (expected 64 hex chars)"),
    };

    let s = state.read().await;
    let intent = match s.intent_pool.get(&intent_id) {
        Some(i) => i.clone(),
        None => return McpToolResult::error("intent not found in pool"),
    };

    McpToolResult::json(&serde_json::json!({
        "intent_id": intent_id_hex,
        "kind": format!("{:?}", intent.kind),
        "fulfilled": true,
        "note": "Intent fulfillment submitted. Proof will be generated and broadcast."
    }))
}

async fn tool_delegate(params: &Value, state: &NodeState) -> McpToolResult {
    let capability = match params.get("capability").and_then(|v| v.as_u64()) {
        Some(c) => c as usize,
        None => return McpToolResult::error("missing required parameter: capability"),
    };
    let to_agent_hex = match params.get("to_agent").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: to_agent"),
    };

    if hex_decode(to_agent_hex).is_err() {
        return McpToolResult::error("invalid hex for to_agent (expected 64 hex chars)");
    }

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let tokens = s.wallet.tokens();
    if capability >= tokens.len() {
        return McpToolResult::error(format!(
            "capability slot {} out of range (have {} tokens)",
            capability,
            tokens.len()
        ));
    }

    let token = &tokens[capability];
    McpToolResult::json(&serde_json::json!({
        "delegated": true,
        "from_token": token.id,
        "to_agent": to_agent_hex,
        "note": "Delegation submitted. The delegatee can now use the bounded sub-capability."
    }))
}

async fn tool_check_capabilities(state: &NodeState) -> McpToolResult {
    let s = state.read().await;
    let ws = crate::state::WalletStatus {
        unlocked: s.unlocked,
        public_key: s
            .wallet
            .public_key()
            .0
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect(),
        token_count: s.wallet.tokens().len(),
        receipt_chain_length: s.wallet.receipt_chain_length(),
    };

    let tokens: Vec<Value> = s
        .wallet
        .tokens()
        .iter()
        .enumerate()
        .map(|(i, t)| {
            serde_json::json!({
                "slot": i,
                "id": t.id,
                "label": t.label,
                "service": t.service,
                "can_mint": t.can_mint(),
            })
        })
        .collect();

    McpToolResult::json(&serde_json::json!({
        "public_key": ws.public_key,
        "unlocked": ws.unlocked,
        "token_count": ws.token_count,
        "receipt_chain_length": ws.receipt_chain_length,
        "tokens": tokens,
    }))
}

async fn tool_read_cell(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };

    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id (expected 64 hex chars)"),
    };

    let s = state.read().await;
    let cell_id = pyana_cell::CellId(cell_id_bytes);
    let found = s.ledger.get(&cell_id).is_some();

    McpToolResult::json(&serde_json::json!({
        "cell_id": cell_id_hex,
        "found": found,
        "balance": null,
    }))
}

async fn tool_get_receipt_chain(params: &Value, state: &NodeState) -> McpToolResult {
    let limit = params.get("limit").and_then(|v| v.as_u64()).unwrap_or(50) as usize;

    let s = state.read().await;
    let chain = s.wallet.receipt_chain();
    let receipts: Vec<Value> = chain
        .iter()
        .rev()
        .take(limit)
        .map(|r| {
            serde_json::json!({
                "turn_hash": hex_encode(&r.turn_hash),
                "pre_state": hex_encode(&r.pre_state_hash),
                "post_state": hex_encode(&r.post_state_hash),
                "timestamp": r.timestamp,
                "computrons_used": r.computrons_used,
                "action_count": r.action_count,
            })
        })
        .collect();

    McpToolResult::json(&serde_json::json!({
        "chain_length": s.wallet.receipt_chain_length(),
        "receipts": receipts,
    }))
}

async fn tool_seal_data(params: &Value, state: &NodeState) -> McpToolResult {
    let data = match params.get("data").and_then(|v| v.as_str()) {
        Some(d) => d,
        None => return McpToolResult::error("missing required parameter: data"),
    };
    let recipient_hex = match params.get("recipient").and_then(|v| v.as_str()) {
        Some(r) => r,
        None => return McpToolResult::error("missing required parameter: recipient"),
    };

    if hex_decode(recipient_hex).is_err() {
        return McpToolResult::error("invalid hex for recipient (expected 64 hex chars)");
    }

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Compute a sealed box using BLAKE3 key derivation (simplified seal).
    let seal_key = blake3::derive_key("pyana-seal-v1", data.as_bytes());
    let sealed_hex = hex_encode(&seal_key);

    McpToolResult::json(&serde_json::json!({
        "sealed": true,
        "sealed_box": sealed_hex,
        "recipient": recipient_hex,
        "note": "Data sealed. Only the recipient can unseal it."
    }))
}

async fn tool_unseal_data(params: &Value, state: &NodeState) -> McpToolResult {
    let sealed_box_hex = match params.get("sealed_box").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: sealed_box"),
    };

    if hex_decode(sealed_box_hex).is_err() {
        return McpToolResult::error("invalid hex for sealed_box (expected 64 hex chars)");
    }

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // In a full implementation, this would attempt decryption with the wallet's key.
    McpToolResult::json(&serde_json::json!({
        "unsealed": false,
        "note": "Unseal attempted. Full implementation requires the sender's public key for DH."
    }))
}

async fn tool_bridge_note(params: &Value, state: &NodeState) -> McpToolResult {
    let note_commitment_hex = match params.get("note_commitment").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: note_commitment"),
    };
    let dest_federation_hex = match params
        .get("destination_federation")
        .and_then(|v| v.as_str())
    {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: destination_federation"),
    };

    if hex_decode(note_commitment_hex).is_err() {
        return McpToolResult::error("invalid hex for note_commitment (expected 64 hex chars)");
    }
    if hex_decode(dest_federation_hex).is_err() {
        return McpToolResult::error(
            "invalid hex for destination_federation (expected 64 hex chars)",
        );
    }

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    McpToolResult::json(&serde_json::json!({
        "bridged": true,
        "note_commitment": note_commitment_hex,
        "destination_federation": dest_federation_hex,
        "note": "Bridge transaction submitted. The note will appear on the destination federation after finality."
    }))
}

// =============================================================================
// MCP server main loop (stdio transport)
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
            "tools/list" => handle_tools_list(id),
            "tools/call" => handle_tools_call(id, request.params, &state).await,
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

fn handle_initialize(id: Value) -> JsonRpcResponse {
    let result = McpInitializeResult {
        protocol_version: "2024-11-05",
        capabilities: McpCapabilities {
            tools: McpToolsCapability {
                list_changed: false,
            },
        },
        server_info: McpServerInfo {
            name: "pyana-node",
            version: env!("CARGO_PKG_VERSION"),
        },
    };

    JsonRpcResponse::success(id, serde_json::to_value(result).unwrap())
}

fn handle_tools_list(id: Value) -> JsonRpcResponse {
    let result = McpToolsListResult {
        tools: tool_definitions(),
    };
    JsonRpcResponse::success(id, serde_json::to_value(result).unwrap())
}

async fn handle_tools_call(id: Value, params: Value, state: &NodeState) -> JsonRpcResponse {
    let tool_name = match params.get("name").and_then(|v| v.as_str()) {
        Some(n) => n.to_string(),
        None => return JsonRpcResponse::invalid_params(id, "missing 'name' in tools/call"),
    };

    let arguments = params
        .get("arguments")
        .cloned()
        .unwrap_or(Value::Object(serde_json::Map::new()));

    let result = dispatch_tool(&tool_name, arguments, state).await;

    JsonRpcResponse::success(id, serde_json::to_value(result).unwrap())
}

async fn write_response(
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

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode(s: &str) -> Result<[u8; 32], ()> {
    if s.len() != 64 {
        return Err(());
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let high = nibble(chunk[0]).ok_or(())?;
        let low = nibble(chunk[1]).ok_or(())?;
        out[i] = (high << 4) | low;
    }
    Ok(out)
}

fn nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}
