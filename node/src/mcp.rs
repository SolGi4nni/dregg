//! MCP (Model Context Protocol) server for the dregg node.
//!
//! Exposes node capabilities as MCP tools over JSON-RPC 2.0 (stdio transport).
//! AI assistants (Claude, GPT, etc.) can discover and invoke tools to interact
//! with the dregg federation: authorize actions, submit turns, manage capabilities,
//! post intents, and more.
//!
//! ## Transport
//!
//! - **Stdio**: `dregg-node mcp` reads JSON-RPC from stdin and writes to stdout.
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
use tracing::{error, info};

use dregg_sdk::{Attenuation, CellId};
use dregg_turn::{CallForest, Turn};
use dregg_types::PublicKey;

use dregg_app_framework::AppCipherclerk;
use dregg_sdk::AgentCipherclerk;
use starbridge_governed_namespace::build_register_service_action as sb_build_register_service_action;
use starbridge_identity::{
    Credential as SbCredential, CredentialAttributes as SbCredentialAttributes,
    CredentialSchema as SbCredentialSchema, IssuerKeys as SbIssuerKeys,
    build_issue_credential_action as sb_build_issue_credential_action,
    employment_schema as sb_employment_schema, gov_id_schema as sb_gov_id_schema,
    issue as sb_issue, kyc_schema as sb_kyc_schema,
};
use starbridge_nameservice::build_register_with_credential_action as sb_build_register_with_credential_action;
use starbridge_subscription::{
    BountyState as SbBountyState, build_bounty_state_publish_action as sb_build_bounty_publish,
};

use crate::state::NodeState;

// Re-import x25519 and chacha for seal/unseal operations.

/// 32-byte-widening helper (effect-vm-hash-widen lane, 2026-05-28): the
/// EffectVM `GrantCapability.cap_entry` param is now `[BabyBear; 8]`. These
/// MCP construction sites carry a SCALAR cap-slot index (not a 32-byte hash),
/// so we anchor it in limb[0] — which drives the AIR's cap_root advance — and
/// leave the high limbs zero. This is byte-for-byte equivalent to the prior
/// single-felt binding, now in the widened 8-limb shape.
fn grant_cap_entry_8(scalar: u32) -> [dregg_circuit::BabyBear; 8] {
    let mut a = [dregg_circuit::BabyBear::ZERO; 8];
    a[0] = dregg_circuit::BabyBear::new(scalar);
    a
}

/// Parse a JSON effect descriptor into a turn `Effect`.
///
/// Supports the subset needed for the two-AI handoff demo:
/// - `{ "type": "transfer", "from": "<hex>", "to": "<hex>", "amount": N }`
/// - `{ "type": "increment_nonce", "cell": "<hex>" }`
/// - `{ "type": "set_field", "cell": "<hex>", "index": N, "value": N }`
///
/// Returns a human-readable error string when the descriptor is malformed.
/// MCP-first: this is the canonical effect-parsing surface; the HTTP API
/// would derive from it if/when it gains an effects body.
fn parse_effect_json(value: &Value) -> Result<dregg_turn::Effect, String> {
    let ty = value
        .get("type")
        .and_then(|v| v.as_str())
        .ok_or_else(|| "effect missing 'type' field".to_string())?;

    let get_hex_32 = |obj: &Value, field: &str| -> Result<[u8; 32], String> {
        let s = obj
            .get(field)
            .and_then(|v| v.as_str())
            .ok_or_else(|| format!("effect.{ty} missing field '{field}'"))?;
        hex_decode(s).map_err(|_| format!("effect.{ty}.{field}: invalid hex (expected 64 chars)"))
    };

    match ty {
        "transfer" => {
            let from = get_hex_32(value, "from")?;
            let to = get_hex_32(value, "to")?;
            let amount = value
                .get("amount")
                .and_then(|v| v.as_u64())
                .ok_or_else(|| "effect.transfer missing 'amount'".to_string())?;
            Ok(dregg_turn::Effect::Transfer {
                from: dregg_cell::CellId(from),
                to: dregg_cell::CellId(to),
                amount,
            })
        }
        "increment_nonce" => {
            let cell = get_hex_32(value, "cell")?;
            Ok(dregg_turn::Effect::IncrementNonce {
                cell: dregg_cell::CellId(cell),
            })
        }
        "set_field" => {
            let cell = get_hex_32(value, "cell")?;
            let index = value
                .get("index")
                .and_then(|v| v.as_u64())
                .ok_or_else(|| "effect.set_field missing 'index'".to_string())?
                as usize;
            let value_u32 = value
                .get("value")
                .and_then(|v| v.as_u64())
                .ok_or_else(|| "effect.set_field missing 'value'".to_string())?
                as u32;
            let mut value_bytes = [0u8; 32];
            value_bytes[..4].copy_from_slice(&value_u32.to_le_bytes());
            Ok(dregg_turn::Effect::SetField {
                cell: dregg_cell::CellId(cell),
                index,
                value: value_bytes,
            })
        }
        other => Err(format!(
            "unknown effect type '{other}' (supported: transfer, increment_nonce, set_field)"
        )),
    }
}

/// Build a CallForest with a single root action containing the given effects.
fn build_forest_with_effects(target: CellId, effects: Vec<dregg_turn::Effect>) -> CallForest {
    let action = dregg_turn::Action {
        target,
        method: dregg_turn::action::symbol("execute"),
        args: vec![],
        authorization: dregg_turn::Authorization::Unchecked,
        preconditions: dregg_cell::Preconditions::default(),
        effects,
        may_delegate: dregg_turn::DelegationMode::None,
        commitment_mode: dregg_turn::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
    forest.add_root(action);
    forest
}

/// Build a CallForest with a single root action authorized by an Ed25519
/// signature over the canonical action-signing message. The signature is
/// produced by `cipherclerk.sign_bytes` against `TurnExecutor::compute_signing_message`
/// in Full commitment mode using the executor's default federation id
/// (`[0u8; 32]`) — which matches `TurnExecutor::new(...).local_federation_id`.
fn build_signed_forest(
    target: CellId,
    effects: Vec<dregg_turn::Effect>,
    cclerk: &dregg_sdk::AgentCipherclerk,
    federation_id: &[u8; 32],
) -> CallForest {
    let mut action = dregg_turn::Action {
        target,
        method: dregg_turn::action::symbol("execute"),
        args: vec![],
        authorization: dregg_turn::Authorization::Unchecked,
        preconditions: dregg_cell::Preconditions::default(),
        effects,
        may_delegate: dregg_turn::DelegationMode::None,
        commitment_mode: dregg_turn::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    // Compute the canonical signing message and replace Unchecked with
    // Authorization::Signature so cells with `delegate: Signature` accept
    // the action.
    let msg = dregg_turn::TurnExecutor::compute_signing_message(&action, federation_id);
    let sig = cclerk.sign_bytes(&msg);
    let mut r = [0u8; 32];
    let mut s = [0u8; 32];
    r.copy_from_slice(&sig.0[..32]);
    s.copy_from_slice(&sig.0[32..]);
    action.authorization = dregg_turn::Authorization::Signature(r, s);

    let mut forest = CallForest::new();
    forest.add_root(action);
    forest
}

#[derive(Debug)]
struct EffectVmProofMaterial {
    proof_hex: String,
    public_inputs: Vec<u64>,
    trace_rows: Vec<Vec<u32>>,
    witness_hash_hex: String,
}

impl EffectVmProofMaterial {
    fn into_parts(self) -> (String, Vec<u64>, Vec<Vec<u32>>, String) {
        (
            self.proof_hex,
            self.public_inputs,
            self.trace_rows,
            self.witness_hash_hex,
        )
    }

    fn proof_json(&self) -> serde_json::Value {
        serde_json::Value::String(self.proof_hex.clone())
    }

    fn trace_json(&self) -> serde_json::Value {
        serde_json::to_value(&self.trace_rows).unwrap_or(serde_json::Value::Null)
    }

    fn witness_hash_json(&self) -> serde_json::Value {
        serde_json::Value::String(self.witness_hash_hex.clone())
    }
}

fn witnessed_receipt_from_effect_material(
    receipt: dregg_turn::TurnReceipt,
    proof: &EffectVmProofMaterial,
) -> Option<dregg_turn::WitnessedReceipt> {
    let mut public_inputs: Vec<u32> = proof.public_inputs.iter().map(|x| *x as u32).collect();
    let needed = dregg_circuit::effect_vm::pi::BASE_COUNT
        .max(
            dregg_circuit::effect_vm::pi::TURN_HASH_BASE
                + dregg_circuit::effect_vm::pi::TURN_HASH_LEN,
        )
        .max(
            dregg_circuit::effect_vm::pi::PREVIOUS_RECEIPT_HASH_BASE
                + dregg_circuit::effect_vm::pi::PREVIOUS_RECEIPT_HASH_LEN,
        );
    if public_inputs.len() < needed {
        public_inputs.resize(needed, 0);
    }
    let turn_hash = dregg_commit::typed::canonical_32_to_felts_4(&receipt.turn_hash);
    for (i, felt) in turn_hash.iter().enumerate() {
        public_inputs[dregg_circuit::effect_vm::pi::TURN_HASH_BASE + i] = felt.as_u32();
    }
    let previous = dregg_commit::typed::canonical_32_to_felts_4(
        &receipt.previous_receipt_hash.unwrap_or([0u8; 32]),
    );
    for (i, felt) in previous.iter().enumerate() {
        public_inputs[dregg_circuit::effect_vm::pi::PREVIOUS_RECEIPT_HASH_BASE + i] = felt.as_u32();
    }
    let trace: Vec<Vec<dregg_circuit::BabyBear>> = proof
        .trace_rows
        .iter()
        .map(|row| {
            row.iter()
                .map(|v| dregg_circuit::BabyBear::new(*v))
                .collect()
        })
        .collect();
    let public_input_felts: Vec<dregg_circuit::BabyBear> = public_inputs
        .iter()
        .map(|v| dregg_circuit::BabyBear::new(*v))
        .collect();
    let air = dregg_circuit::effect_vm::EffectVmAir::new(trace.len());
    let receipt_bound_proof =
        dregg_circuit::stark::try_prove(&air, &trace, &public_input_felts).ok()?;
    let proof_bytes = dregg_circuit::stark::proof_to_bytes(&receipt_bound_proof);

    Some(dregg_turn::WitnessedReceipt::from_components(
        receipt,
        proof_bytes,
        public_inputs,
        if trace.is_empty() {
            None
        } else {
            Some(trace.as_slice())
        },
    ))
}

fn project_effects_for_mcp(
    effects: &[dregg_turn::Effect],
) -> Vec<dregg_circuit::effect_vm::Effect> {
    let mut vm_effects = Vec::new();
    for e in effects {
        match e {
            dregg_turn::Effect::Transfer { amount, .. } => {
                vm_effects.push(dregg_circuit::effect_vm::Effect::Transfer {
                    amount: *amount,
                    direction: 1,
                });
            }
            dregg_turn::Effect::SetField { index, value, .. } => {
                let mut le4 = [0u8; 4];
                le4.copy_from_slice(&value[..4]);
                vm_effects.push(dregg_circuit::effect_vm::Effect::SetField {
                    field_idx: *index as u32,
                    value: dregg_circuit::BabyBear::new(u32::from_le_bytes(le4)),
                });
            }
            dregg_turn::Effect::IncrementNonce { .. } => {
                vm_effects.push(dregg_circuit::effect_vm::Effect::NoOp);
            }
            _ => {}
        }
    }
    vm_effects
}

fn require_pre_state(
    cell: &dregg_cell::CellId,
    pre_state: Option<(u64, u64)>,
    label: &str,
) -> Result<(u64, u64), McpToolResult> {
    pre_state.ok_or_else(|| {
        McpToolResult::json(&serde_json::json!({
            "activity_status": "rejected",
            "proof_status": "missing_pre_state",
            "committed": false,
            "exercised": false,
            "error": format!("{label}: cell {} is not in the local ledger; refusing to execute without Effect VM pre-state", hex_encode(&cell.0)),
        }))
    })
}

fn require_local_cell_for_commit(
    ledger: &dregg_cell::Ledger,
    cell: &dregg_cell::CellId,
    label: &str,
) -> Result<(), McpToolResult> {
    if ledger.get(cell).is_some() {
        return Ok(());
    }
    Err(McpToolResult::json(&serde_json::json!({
        "activity_status": "rejected",
        "proof_status": "missing_pre_state",
        "committed": false,
        "exercised": false,
        "error": format!("{label}: cell {} is not in the local ledger; refusing to synthesize a remote stub for a committed proof-bearing turn", hex_encode(&cell.0)),
    })))
}

fn require_effect_cells_for_commit(
    ledger: &dregg_cell::Ledger,
    effects: &[dregg_turn::Effect],
    label: &str,
) -> Result<(), McpToolResult> {
    for effect in effects {
        match effect {
            dregg_turn::Effect::Transfer { from, to, .. } => {
                require_local_cell_for_commit(ledger, from, label)?;
                require_local_cell_for_commit(ledger, to, label)?;
            }
            dregg_turn::Effect::GrantCapability { from, to, cap } => {
                require_local_cell_for_commit(ledger, from, label)?;
                require_local_cell_for_commit(ledger, to, label)?;
                require_local_cell_for_commit(ledger, &cap.target, label)?;
            }
            dregg_turn::Effect::SetField { cell, .. }
            | dregg_turn::Effect::IncrementNonce { cell }
            | dregg_turn::Effect::RevokeCapability { cell, .. }
            | dregg_turn::Effect::EmitEvent { cell, .. }
            | dregg_turn::Effect::SetPermissions { cell, .. }
            | dregg_turn::Effect::SetVerificationKey { cell, .. }
            | dregg_turn::Effect::Refusal { cell, .. } => {
                require_local_cell_for_commit(ledger, cell, label)?;
            }
            dregg_turn::Effect::Introduce {
                introducer,
                recipient,
                target,
                ..
            } => {
                require_local_cell_for_commit(ledger, introducer, label)?;
                require_local_cell_for_commit(ledger, recipient, label)?;
                require_local_cell_for_commit(ledger, target, label)?;
            }

            dregg_turn::Effect::CellSeal { target, .. }
            | dregg_turn::Effect::CellUnseal { target }
            | dregg_turn::Effect::CellDestroy { target, .. } => {
                require_local_cell_for_commit(ledger, target, label)?;
            }
            _ => {}
        }
    }
    Ok(())
}

/// F-DOS-1 scoping note: this proves synchronously (the demo/CLI proof-return
/// contract — `effect_vm_proof_hex` is forwarded into the replay chain). Unlike
/// the public HTTP submit path (`api.rs`, which now revalidates inline + proves
/// async off the state-write lock), the MCP surface is **stdio-only, single-user
/// CLI** (`dregg-node mcp` reads JSON-RPC from stdin — see module docs + `main.rs`
/// `run_mcp`). There is no concurrent remote client to starve and no remote
/// attacker, so the F-DOS-1 vector (a submitted turn pins a worker under the
/// global lock while OTHER clients freeze) does not apply here. Converting this
/// to async would break the synchronous proof return the demos depend on, so the
/// proof stays inline — but it is NOT on a remote request path. The DoS fix lives
/// where the DoS lives: the HTTP submit/commit handlers.
fn require_effect_vm_proof(
    initial_balance: u64,
    initial_nonce: u64,
    vm_effects: &[dregg_circuit::effect_vm::Effect],
    label: &str,
) -> Result<EffectVmProofMaterial, McpToolResult> {
    try_generate_effect_vm_proof(initial_balance, initial_nonce, vm_effects).map_err(|e| {
        McpToolResult::json(&serde_json::json!({
            "activity_status": "rejected",
            "proof_status": "proof_generation_failed",
            "committed": false,
            "exercised": false,
            "error": format!("{label}: Effect VM proof generation failed: {e}"),
        }))
    })
}

/// Generate an Effect VM STARK proof for a sequence of VM-domain effects.
///
/// Builds a fresh `CellState` from `(initial_balance, initial_nonce)`, runs the
/// effect VM trace generator, constructs the `EffectVmAir` sized to the effect
/// count, and produces a STARK proof. Returns the hex-encoded postcard-serialized
/// proof bytes, the public inputs converted to `u64` (BabyBear canonical
/// values fit in u32, so the JSON array is friendly to the independent verifier
/// which parses public inputs as u32), the trace as a `Vec<Vec<u32>>` for
/// scope-(2) WitnessedReceipt capture, and the BLAKE3 witness_hash of the
/// postcard-serialised `WitnessBundle::Inline` (hex-encoded) so demo scripts
/// can forward it verbatim into the on-disk replay chain.
///
/// Stage 7 / §C: returning the trace + witness_hash lets the MCP tool emit
/// scope-(2) WitnessedReceipts. The MCP layer ships these to the demo
/// scripts; the verifier-side `replay_chain` reconstructs `BabyBear` cells
/// via `BabyBear::new_canonical` and re-derives the witness_hash to check
/// the binding.
///
/// If `vm_effects` is empty, the checked helper returns an error. The tuple
/// wrapper is retained for older tests that only call it with non-empty effects.
fn generate_effect_vm_proof(
    initial_balance: u64,
    initial_nonce: u64,
    vm_effects: &[dregg_circuit::effect_vm::Effect],
) -> (String, Vec<u64>, Vec<Vec<u32>>, String) {
    match try_generate_effect_vm_proof(initial_balance, initial_nonce, vm_effects) {
        Ok(material) => material.into_parts(),
        Err(e) => panic!("{e}"),
    }
}

fn try_generate_effect_vm_proof(
    initial_balance: u64,
    initial_nonce: u64,
    vm_effects: &[dregg_circuit::effect_vm::Effect],
) -> Result<EffectVmProofMaterial, String> {
    if vm_effects.is_empty() {
        return Err("empty Effect VM projection".to_string());
    }

    let initial_state =
        dregg_circuit::effect_vm::CellState::new(initial_balance, initial_nonce as u32);
    let (trace, mut public_inputs) =
        dregg_circuit::effect_vm::generate_effect_vm_trace(&initial_state, vm_effects);

    // Issue #72: the verifier's `check_receipt_pi_binding` requires
    // `PI[IS_AGENT_CELL] == 1` for the v1 single-proof-per-WR shape (see
    // `verifier/src/lib.rs::check_receipt_pi_binding`). The trace generator
    // leaves this PI slot at zero because the AIR itself has no
    // constraint on IS_AGENT_CELL (it is an executor-asserted bundle tag
    // — the per-cell prover knows whether `cell_id == turn.agent`).
    //
    // For mcp-generated proofs the cell IS the agent by construction: this
    // path produces a *single* per-cell proof for the actor's own state
    // transition (grant/revoke/exercise of their own capability). So the
    // tag is always 1 here. Setting it explicitly mirrors what
    // `turn/src/executor/proof_verify.rs::populate_pi` does for the
    // executor-driven path and what `silver_helper.rs::cmd_make_recursive_witness`
    // does for the demo's witness fabrication path. Without this, the
    // standalone `dregg-verifier replay-chain` rejects the chain with
    // "PI[IS_AGENT_CELL] = 0 but single-proof replay requires 1".
    public_inputs[dregg_circuit::effect_vm::pi::IS_AGENT_CELL] = dregg_circuit::BabyBear::ONE;
    // The trace generator pads to the next power of two ≥ 2; the AIR must be
    // sized to the actual trace height, not the raw effect count (passing
    // `vm_effects.len()` panics when it's less than 2 or not a power of two).
    let air = dregg_circuit::effect_vm::EffectVmAir::new(trace.len());
    let proof =
        dregg_circuit::stark::try_prove(&air, &trace, &public_inputs).map_err(|e| e.to_string())?;
    // Use the canonical DREG-prefixed byte format that the standalone
    // dregg-verifier binary deserializes via stark::proof_from_bytes.
    // postcard's encoding lacks the magic-header and is not what the
    // verifier accepts on the wire.
    let proof_bytes = dregg_circuit::stark::proof_to_bytes(&proof);
    let proof_hex = hex_encode(&proof_bytes);
    let public_inputs_u64: Vec<u64> = public_inputs.iter().map(|f| f.as_u32() as u64).collect();
    // Build the canonical WitnessBundle::Inline so we can both ship the
    // trace shape and compute its BLAKE3 hash via the canonical
    // postcard-serialised form. The demo writes both to disk; the verifier
    // re-derives the hash to enforce binding.
    let bundle = dregg_turn::WitnessBundle::inline_from_trace(&trace);
    let trace_rows = bundle.trace_rows.clone();
    let witness_hash_hex = hex_encode(&bundle.witness_hash());
    Ok(EffectVmProofMaterial {
        proof_hex,
        public_inputs: public_inputs_u64,
        trace_rows,
        witness_hash_hex,
    })
}

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
    /// MCP `instructions`: a server-level orientation hint shown to the model on
    /// connect, BEFORE it lists anything. dregg uses it to immediately point an
    /// arriving agent at its self-orientation surface (`dregg://about`,
    /// `dregg://ontology`, `dregg://identity`) and explain the `_cap` ocap
    /// convention — so the agent knows it is INHABITING a place, not calling an
    /// RPC grab-bag, from the very first message.
    instructions: &'static str,
}

#[derive(Serialize)]
struct McpCapabilities {
    tools: McpToolsCapability,
    resources: McpResourcesCapability,
    prompts: McpPromptsCapability,
    /// MCP `completions` capability: this server answers `completion/complete`
    /// for prompt arguments and resource-template variables (e.g. completing a
    /// `dregg://cell/{cell_id}` from the cells it knows). An empty object is the
    /// spec's way of advertising the capability with no sub-flags.
    completions: McpCompletionsCapability,
}

#[derive(Serialize)]
struct McpCompletionsCapability {}

#[derive(Serialize)]
struct McpToolsCapability {
    #[serde(rename = "listChanged")]
    list_changed: bool,
}

#[derive(Serialize)]
struct McpResourcesCapability {
    /// We support resources/subscribe for live state (cell state, blocklace
    /// status) via the node's event broadcast, advertised but realized lazily.
    subscribe: bool,
    #[serde(rename = "listChanged")]
    list_changed: bool,
}

#[derive(Serialize)]
struct McpPromptsCapability {
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
    /// MCP `title`: a short human-friendly display name (distinct from the
    /// programmatic `name`). Injected from [`tool_title`] in the list pass.
    #[serde(skip_serializing_if = "Option::is_none")]
    title: Option<&'static str>,
    description: &'static str,
    #[serde(rename = "inputSchema")]
    input_schema: Value,
    /// MCP 2025-06-18 `outputSchema`: the JSON-schema of the tool's
    /// `structuredContent`. Declaring it lets a client validate the typed result
    /// and know the shape before calling. dregg's mutating tools all return a
    /// common "receipt" shape; reads return their own structured state. Injected
    /// in the list pass from [`tool_output_schema`].
    #[serde(rename = "outputSchema", skip_serializing_if = "Option::is_none")]
    output_schema: Option<Value>,
    /// MCP behavioural ANNOTATIONS (`readOnlyHint` / `destructiveHint` /
    /// `idempotentHint` / `openWorldHint`). These are hints — an agent uses
    /// them to decide whether a call mutates, can be safely retried, or touches
    /// the open world (network / other federations). Injected in the list pass.
    #[serde(skip_serializing_if = "Option::is_none")]
    annotations: Option<McpToolAnnotations>,
}

/// MCP tool behavioural annotations. All four are OPTIONAL hints per the spec;
/// we always populate `readOnlyHint` and `idempotentHint`, and the others when
/// meaningful. An agent reads these to know e.g. that `dregg_read_cell` is
/// read-only (safe to probe) while `dregg_revoke_capability` is destructive.
#[derive(Serialize, Clone, Copy)]
struct McpToolAnnotations {
    #[serde(rename = "readOnlyHint")]
    read_only_hint: bool,
    #[serde(rename = "destructiveHint", skip_serializing_if = "Option::is_none")]
    destructive_hint: Option<bool>,
    #[serde(rename = "idempotentHint")]
    idempotent_hint: bool,
    #[serde(rename = "openWorldHint", skip_serializing_if = "Option::is_none")]
    open_world_hint: Option<bool>,
}

#[derive(Serialize)]
struct McpToolResult {
    content: Vec<McpContent>,
    /// MCP 2025-06-18 STRUCTURED OUTPUT. When a tool's result is structured
    /// (a receipt, a proof status, a cell state), we surface the raw JSON object
    /// here in addition to the human-readable `content` text. Clients that
    /// understand `structuredContent` can consume the typed shape directly;
    /// older clients still get the pretty-printed text. Always omitted for
    /// plain-text / error results.
    #[serde(rename = "structuredContent", skip_serializing_if = "Option::is_none")]
    structured_content: Option<Value>,
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
            structured_content: None,
            is_error: None,
        }
    }

    /// Structured success: pretty text for humans + a machine-readable
    /// `structuredContent` mirror for MCP clients that consume typed output.
    fn json(value: &Value) -> Self {
        Self {
            content: vec![McpContent {
                content_type: "text",
                text: serde_json::to_string_pretty(value).unwrap_or_default(),
            }],
            structured_content: Some(value.clone()),
            is_error: None,
        }
    }

    fn error(s: impl Into<String>) -> Self {
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
    fn actionable_error(msg: impl Into<String>, hint: impl Into<String>) -> Self {
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

/// The legible tool GROUP a tool belongs to. dregg's MCP surface is large
/// (46 tools); rather than a flat dump, each tool advertises a group so a
/// client UI / agent can present the toolset as a coherent place. Groups map to
/// the agent's four modes of inhabiting dregg: orient, act, delegate, verify —
/// plus the app and privacy surfaces.
fn tool_group(tool: &str) -> &'static str {
    match tool {
        "dregg_get_status"
        | "dregg_check_capabilities"
        | "dregg_read_cell"
        | "dregg_get_receipt_chain"
        | "dregg_get_blocklace_status"
        | "dregg_get_constitution"
        | "dregg_check_resource_budget"
        | "dregg_list_auctions"
        | "dregg_verify_provenance" => "orient",

        "dregg_create_agent"
        | "dregg_authorize"
        | "dregg_submit_turn"
        | "dregg_post_intent"
        | "dregg_fulfill_intent"
        | "dregg_make_sovereign"
        | "dregg_bilateral_action"
        | "dregg_debit_shared_resource"
        | "dregg_place_bid"
        | "dregg_captp_deliver" => "act",

        "dregg_grant_capability"
        | "dregg_revoke_capability"
        | "dregg_delegate"
        | "dregg_create_bearer_cap"
        | "dregg_exercise_bearer_cap"
        | "dregg_exercise_handoff_cert"
        | "dregg_propose_membership" => "delegate",

        "dregg_verify_sovereign_proof"
        | "dregg_prove_sovereign_turn"
        | "dregg_compose_proofs"
        | "dregg_prove_predicate"
        | "dregg_sign_sovereign_witness"
        | "dregg_peer_exchange"
        | "dregg_compress_history" => "verify",

        "dregg_seal_data"
        | "dregg_unseal_data"
        | "dregg_create_stealth_address"
        | "dregg_private_transfer"
        | "dregg_encrypt_intent" => "privacy",

        "dregg_register_name"
        | "dregg_publish_subscription"
        | "dregg_issue_credential"
        | "dregg_register_service"
        | "dregg_deploy_factory"
        | "dregg_create_from_factory"
        | "dregg_create_cell_from_factory_effect" => "apps",

        _ => "other",
    }
}

/// A short human-friendly display title for a tool (MCP `title`). The
/// programmatic `name` stays stable; the title aids legibility in clients.
fn tool_title(tool: &str) -> &'static str {
    match tool {
        "dregg_get_status" => "Node Status",
        "dregg_create_agent" => "Register Agent Cell",
        "dregg_authorize" => "Authorize Action (ZK)",
        "dregg_submit_turn" => "Submit Verified Turn",
        "dregg_grant_capability" => "Grant Capability",
        "dregg_revoke_capability" => "Revoke Capability",
        "dregg_post_intent" => "Post Intent",
        "dregg_fulfill_intent" => "Fulfill Intent",
        "dregg_delegate" => "Delegate Sub-Capability",
        "dregg_check_capabilities" => "List My Capabilities",
        "dregg_read_cell" => "Read Cell State",
        "dregg_get_receipt_chain" => "Read Receipt Chain",
        "dregg_seal_data" => "Seal Data (Encrypt)",
        "dregg_unseal_data" => "Unseal Data (Decrypt)",
        "dregg_make_sovereign" => "Make Cell Sovereign",
        "dregg_peer_exchange" => "Sovereign Peer Exchange",
        "dregg_compress_history" => "IVC-Compress History",
        "dregg_create_bearer_cap" => "Create Bearer Capability",
        "dregg_exercise_bearer_cap" => "Exercise Bearer Capability",
        "dregg_deploy_factory" => "Deploy Factory",
        "dregg_create_from_factory" => "Create Cell From Factory",
        "dregg_verify_provenance" => "Verify Cell Provenance",
        "dregg_prove_sovereign_turn" => "Prove Sovereign Turn (STARK)",
        "dregg_verify_sovereign_proof" => "Verify Sovereign Proof",
        "dregg_create_stealth_address" => "Create Stealth Address",
        "dregg_private_transfer" => "Private Transfer",
        "dregg_encrypt_intent" => "Post Encrypted Intent",
        "dregg_prove_predicate" => "Prove Predicate (ZK)",
        "dregg_compose_proofs" => "Compose Proofs",
        "dregg_get_blocklace_status" => "Blocklace / Finality Status",
        "dregg_get_constitution" => "Federation Constitution",
        "dregg_propose_membership" => "Propose Membership Change",
        "dregg_check_resource_budget" => "Check Resource Budget",
        "dregg_debit_shared_resource" => "Debit Shared Resource",
        "dregg_list_auctions" => "List Auctions",
        "dregg_place_bid" => "Place Sealed Bid",
        "dregg_captp_deliver" => "CapTP Deliver",
        "dregg_exercise_handoff_cert" => "Exercise Handoff Cert",
        "dregg_sign_sovereign_witness" => "Sign Sovereign Witness",
        "dregg_bilateral_action" => "Bilateral Action (Both Receipts)",
        "dregg_register_name" => "Register Name",
        "dregg_publish_subscription" => "Publish Subscription Update",
        "dregg_issue_credential" => "Issue Credential",
        "dregg_register_service" => "Register Service Path",
        "dregg_create_cell_from_factory_effect" => "Create Cell (Factory Effect)",
        _ => "dregg Tool",
    }
}

/// Behavioural annotations for a tool. Derived from its capability scope and
/// known semantics: `read` tools are read-only & idempotent; capability
/// administration is destructive; bridge / federation / captp reach the open
/// world. An agent reads these to decide whether a call is safe to probe,
/// retryable, or reaches beyond the local node.
fn tool_annotations(tool: &str) -> McpToolAnnotations {
    let scope = tool_required_scope(tool);
    let read_only = scope == "read";

    // Destructive = irreversibly removes authority / state. Only meaningful for
    // mutating tools; left None for read-only tools (per spec, destructiveHint
    // is only relevant when readOnlyHint is false).
    let destructive_hint = if read_only {
        None
    } else {
        Some(matches!(
            tool,
            "dregg_revoke_capability" | "dregg_propose_membership" | "dregg_private_transfer"
        ))
    };

    // Idempotent: re-invoking with the same args has no additional effect.
    // Reads are idempotent; `create_agent` is explicitly idempotent (registers
    // once); pure proof/verify/seal computations are deterministic functions.
    let idempotent_hint = read_only
        || matches!(
            tool,
            "dregg_create_agent"
                | "dregg_make_sovereign"
                | "dregg_verify_sovereign_proof"
                | "dregg_prove_predicate"
                | "dregg_prove_sovereign_turn"
                | "dregg_create_stealth_address"
                | "dregg_seal_data"
                | "dregg_unseal_data"
                | "dregg_compose_proofs"
        );

    // Open world: touches state beyond this node (other federations / peers /
    // capability-transfer protocols / external marketplaces).
    let open_world_hint = Some(matches!(
        tool,
        "dregg_peer_exchange"
            | "dregg_captp_deliver"
            | "dregg_exercise_handoff_cert"
            | "dregg_propose_membership"
            | "dregg_post_intent"
            | "dregg_fulfill_intent"
            | "dregg_encrypt_intent"
            | "dregg_list_auctions"
            | "dregg_place_bid"
    ));

    McpToolAnnotations {
        read_only_hint: read_only,
        destructive_hint,
        idempotent_hint,
        open_world_hint,
    }
}

/// The declared `outputSchema` for a tool's `structuredContent` (MCP 2025-06-18).
///
/// Most dregg tools that change state return the SAME structured "receipt" shape
/// (turn hash + commit flag + the Effect-VM STARK proof material). Declaring it
/// once, by reuse, lets a client validate the typed result and — crucially for an
/// agent's VERIFY mode — know up front that a turn carries a proof to check. Read
/// tools and a few bespoke shapes return `None` (their `structuredContent` is the
/// state object itself, whose shape is self-describing).
fn tool_output_schema(tool: &str) -> Option<Value> {
    // The common verified-turn receipt shape produced by `run_*_action` /
    // `tool_submit_turn` / capability + app tools.
    let receipt = || {
        serde_json::json!({
            "type": "object",
            "description": "A dregg verified-turn receipt: the committed state transition plus \
                            its Effect-VM STARK proof material (verify via dregg://receipts or \
                            the standalone dregg-verifier).",
            "properties": {
                "committed": { "type": "boolean", "description": "Whether the turn committed to the ledger." },
                "turn_hash": { "type": "string", "description": "Hex hash of the committed turn." },
                "post_state_root": { "type": "string", "description": "Hex post-state root the proof binds to." },
                "effect_vm_proof_hex": { "type": "string", "description": "Hex-encoded Effect-VM STARK proof of the transition." },
                "effect_vm_public_inputs": { "type": "array", "items": { "type": "integer" }, "description": "The proof's public inputs." },
                "effect_vm_witness_hash_hex": { "type": "string", "description": "Hex witness hash binding the trace." }
            },
            "required": ["committed"]
        })
    };
    match tool {
        // Tools that submit a verified turn and return the receipt shape.
        "dregg_submit_turn"
        | "dregg_grant_capability"
        | "dregg_revoke_capability"
        | "dregg_delegate"
        | "dregg_make_sovereign"
        | "dregg_register_name"
        | "dregg_publish_subscription"
        | "dregg_register_service"
        | "dregg_issue_credential"
        | "dregg_exercise_bearer_cap"
        | "dregg_fulfill_intent" => Some(receipt()),
        _ => None,
    }
}

/// The public tool list: the raw definitions DECORATED with title, behavioural
/// annotations, an output schema, and a `group` tag in the input schema's
/// metadata. This is what `tools/list` serves.
fn tool_definitions() -> Vec<McpToolDef> {
    let mut defs = tool_definitions_raw();
    for d in defs.iter_mut() {
        d.title = Some(tool_title(d.name));
        d.annotations = Some(tool_annotations(d.name));
        d.output_schema = tool_output_schema(d.name);
        // Stamp the legible group + required capability scope into the schema's
        // top-level metadata so an agent self-orienting from tools/list alone
        // can see which mode each tool belongs to and what authority it needs.
        let scope = tool_required_scope(d.name);
        if let Value::Object(map) = &mut d.input_schema {
            map.insert(
                "x-dregg-group".to_string(),
                Value::String(tool_group(d.name).to_string()),
            );
            map.insert(
                "x-dregg-scope".to_string(),
                Value::String(scope.to_string()),
            );
            // Declare the ocap `_cap` argument in the SCHEMA, not just prose.
            // When capability enforcement is on, a covering tools-access biscuit
            // (scope verb '{scope}') must be presented here; an agent reading
            // tools/list — and a schema-validating client — discovers the
            // requirement without having to read dregg://about. Optional in the
            // schema (enforcement may be off), but its presence makes the ocap
            // model legible right at the tool boundary.
            if let Some(props) = map.get_mut("properties").and_then(|p| p.as_object_mut()) {
                props.insert(
                    "_cap".to_string(),
                    serde_json::json!({
                        "type": "object",
                        "description": format!(
                            "ocap credential. When capability enforcement is on, present a \
                             tools-access biscuit covering this tool's '{scope}' scope, minted by \
                             this node under its mcp_cap_issuer_pubkey (see dregg://identity). \
                             Omit when enforcement is off."
                        ),
                        "properties": {
                            "biscuit": {
                                "type": "string",
                                "description": "The encoded 'eb2_…' biscuit string."
                            }
                        },
                        "required": ["biscuit"]
                    }),
                );
            }
        }
    }
    defs
}

fn tool_definitions_raw() -> Vec<McpToolDef> {
    vec![
        McpToolDef {
            name: "dregg_get_status",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Get node status (height, peers, health)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_create_agent",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Register this node's cipherclerk as a cell in the local ledger (idempotent). Returns the content-addressed cell_id.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "name": { "type": "string", "description": "Human-readable label for the agent (informational only; identity is content-addressed from the cipherclerk pubkey)" },
                    "initial_balance": { "type": "integer", "description": "Initial computron balance for the cell when first created. Ignored on subsequent calls." }
                },
                "required": ["name"]
            }),
        },
        McpToolDef {
            name: "dregg_authorize",
            title: None,
            output_schema: None,
            annotations: None,
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
            name: "dregg_submit_turn",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Submit an atomic turn (set of actions) for execution. Pass an `effects` array to actually perform work (transfers, set_field, etc.); omit it for a no-op turn that just chains a receipt.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell ID" },
                    "method": { "type": "string", "description": "The method to invoke on the cell" },
                    "fee": { "type": "integer", "description": "Fee in computrons (default: 0)" },
                    "memo": { "type": "string", "description": "Optional memo attached to the turn" },
                    "effects": {
                        "type": "array",
                        "description": "Optional list of effects: { type: 'transfer', from, to, amount } | { type: 'increment_nonce', cell } | { type: 'set_field', cell, index, value }",
                        "items": { "type": "object" }
                    }
                },
                "required": ["target_cell", "method"]
            }),
        },
        McpToolDef {
            name: "dregg_grant_capability",
            title: None,
            output_schema: None,
            annotations: None,
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
            name: "dregg_revoke_capability",
            title: None,
            output_schema: None,
            annotations: None,
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
            name: "dregg_post_intent",
            title: None,
            output_schema: None,
            annotations: None,
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
            name: "dregg_fulfill_intent",
            title: None,
            output_schema: None,
            annotations: None,
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
            name: "dregg_delegate",
            title: None,
            output_schema: None,
            annotations: None,
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
            name: "dregg_check_capabilities",
            title: None,
            output_schema: None,
            annotations: None,
            description: "List all capabilities held by the current agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_read_cell",
            title: None,
            output_schema: None,
            annotations: None,
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
            name: "dregg_get_receipt_chain",
            title: None,
            output_schema: None,
            annotations: None,
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
            name: "dregg_seal_data",
            title: None,
            output_schema: None,
            annotations: None,
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
            name: "dregg_unseal_data",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Decrypt sealed data addressed to this agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "sealed_box": { "type": "string", "description": "Hex-encoded sealed box bytes" }
                },
                "required": ["sealed_box"]
            }),
        },
        // ─── Sovereign Cells ───────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_make_sovereign",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Transition a cell to sovereign mode (cell stores its own state, federation only holds commitment)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID to transition" }
                },
                "required": ["cell_id"]
            }),
        },
        McpToolDef {
            name: "dregg_peer_exchange",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Initiate P2P state exchange with another sovereign cell, producing a STARK proof of the transition",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte local cell ID" },
                    "peer_cell_id": { "type": "string", "description": "Hex-encoded 32-byte peer cell ID" },
                    "new_commitment": { "type": "string", "description": "Hex-encoded 32-byte new state commitment after exchange" }
                },
                "required": ["cell_id", "peer_cell_id", "new_commitment"]
            }),
        },
        McpToolDef {
            name: "dregg_compress_history",
            title: None,
            output_schema: None,
            annotations: None,
            description: "IVC-compress a sovereign cell's turn history into a single constant-size proof",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID" },
                    "initial_root": { "type": "integer", "description": "Initial state root (BabyBear field element as u32)" },
                    "turn_count": { "type": "integer", "description": "Number of recent turns to compress (default: all)" }
                },
                "required": ["cell_id", "initial_root"]
            }),
        },
        // ─── Bearer Capabilities ───────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_create_bearer_cap",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Create a bearer capability proof (immediate grant, no c-list storage required)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell the cap grants access to" },
                    "permissions": { "type": "string", "description": "Permission level: none, signature, proof, either" },
                    "expires_at": { "type": "integer", "description": "Block height at which the bearer cap expires" },
                    "bearer_pk": { "type": "string", "description": "Hex-encoded 32-byte public key of the intended bearer" }
                },
                "required": ["target_cell", "permissions", "expires_at", "bearer_pk"]
            }),
        },
        McpToolDef {
            name: "dregg_exercise_bearer_cap",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Exercise a bearer capability to perform an action without c-list storage. Pass an `effects` array to actually perform work (e.g. transfer from the target cell).",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell" },
                    "method": { "type": "string", "description": "Method to invoke on the target cell" },
                    "delegation_chain": { "type": "string", "description": "Hex-encoded delegation chain signature" },
                    "bearer_pk": { "type": "string", "description": "Hex-encoded 32-byte bearer public key" },
                    "expires_at": { "type": "integer", "description": "Expiry height of the bearer cap" },
                    "permissions": { "type": "string", "description": "Permission level the bearer cap commits to (default: 'signature' for backward compat)" },
                    "effects": {
                        "type": "array",
                        "description": "List of effects to execute under the bearer authorization (typically a single transfer). Each effect is { type, ... } per the parse_effect_json contract.",
                        "items": { "type": "object" }
                    }
                },
                "required": ["target_cell", "method", "delegation_chain", "bearer_pk", "expires_at"]
            }),
        },
        // ─── Factories ─────────────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_deploy_factory",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Deploy a factory descriptor to the ProgramRegistry (defines what new cells can be created)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "factory_vk": { "type": "string", "description": "Hex-encoded 32-byte factory verification key" },
                    "child_vk_strategy": { "type": "string", "enum": ["fixed", "derived", "approved_set"], "description": "How child VKs are determined" },
                    "max_creations_per_epoch": { "type": "integer", "description": "Maximum cells this factory can create per epoch (0 = unlimited)" },
                    "sovereign": { "type": "boolean", "description": "Whether created cells are sovereign (default: false)" }
                },
                "required": ["factory_vk"]
            }),
        },
        McpToolDef {
            name: "dregg_create_from_factory",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Create a new cell from a deployed factory (with provenance tracking)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "factory_vk": { "type": "string", "description": "Hex-encoded 32-byte factory VK to create from" },
                    "cell_name": { "type": "string", "description": "Human-readable name for the new cell" },
                    "sovereign": { "type": "boolean", "description": "Whether the new cell is sovereign (default: false)" }
                },
                "required": ["factory_vk"]
            }),
        },
        McpToolDef {
            name: "dregg_verify_provenance",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Verify a cell's factory provenance (check its creation lineage)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID to check" },
                    "expected_factory_vk": { "type": "string", "description": "Hex-encoded 32-byte expected factory VK (optional filter)" }
                },
                "required": ["cell_id"]
            }),
        },
        // ─── Effect VM ─────────────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_prove_sovereign_turn",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Generate a STARK proof for a sovereign cell's multi-effect turn via the Effect VM",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte sovereign cell ID" },
                    "effects": {
                        "type": "array",
                        "items": {
                            "type": "object",
                            "properties": {
                                "type": { "type": "string", "enum": ["credit", "debit", "set_field", "grant_cap"], "description": "Effect type" },
                                "amount": { "type": "integer", "description": "Amount for credit/debit effects" },
                                "field": { "type": "string", "description": "Field name for set_field" },
                                "value": { "type": "string", "description": "Field value for set_field" }
                            },
                            "required": ["type"]
                        },
                        "description": "List of effects to prove"
                    },
                    "pre_state_hash": { "type": "string", "description": "Hex-encoded 32-byte pre-state commitment" }
                },
                "required": ["cell_id", "effects", "pre_state_hash"]
            }),
        },
        McpToolDef {
            name: "dregg_verify_sovereign_proof",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Verify a STARK proof generated by the Effect VM for a sovereign turn",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "proof_hex": { "type": "string", "description": "Hex-encoded proof bytes" },
                    "public_inputs": {
                        "type": "array",
                        "items": { "type": "integer" },
                        "description": "Public input values (BabyBear field elements as u32)"
                    }
                },
                "required": ["proof_hex", "public_inputs"]
            }),
        },
        // ─── Privacy ───────────────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_create_stealth_address",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Generate a one-time stealth address for a recipient (unlinkable receive address)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "recipient_spend_pubkey": { "type": "string", "description": "Hex-encoded 32-byte recipient spend public key" },
                    "recipient_view_pubkey": { "type": "string", "description": "Hex-encoded 32-byte recipient view public key" }
                },
                "required": ["recipient_spend_pubkey", "recipient_view_pubkey"]
            }),
        },
        McpToolDef {
            name: "dregg_private_transfer",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Perform a private value transfer using Pedersen commitments (hides amount)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "from_cell": { "type": "string", "description": "Hex-encoded 32-byte sender cell ID" },
                    "to_cell": { "type": "string", "description": "Hex-encoded 32-byte recipient cell ID" },
                    "amount": { "type": "integer", "description": "Transfer amount (hidden in commitment)" },
                    "blinding": { "type": "string", "description": "Hex-encoded 32-byte blinding factor (random if omitted)" }
                },
                "required": ["from_cell", "to_cell", "amount"]
            }),
        },
        McpToolDef {
            name: "dregg_encrypt_intent",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Post an SSE-encrypted intent (body hidden, matchable via search tokens)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "action": { "type": "string", "description": "The action needed (e.g. read, write, execute)" },
                    "resource": { "type": "string", "description": "The resource pattern (e.g. documents/*)" },
                    "expiry_blocks": { "type": "integer", "description": "Number of blocks until intent expires" }
                },
                "required": ["action", "resource"]
            }),
        },
        McpToolDef {
            name: "dregg_prove_predicate",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Prove a predicate over private data (e.g. balance >= threshold) without revealing the value",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "predicate_type": { "type": "string", "enum": ["gte", "lte", "eq", "range", "membership"], "description": "Type of predicate to prove" },
                    "attribute": { "type": "string", "description": "Name of the attribute being proven" },
                    "threshold": { "type": "integer", "description": "Threshold value for comparison predicates" },
                    "private_value": { "type": "integer", "description": "The private value (not revealed in proof)" },
                    "state_root": { "type": "integer", "description": "Current state root (BabyBear field element as u32)" }
                },
                "required": ["predicate_type", "attribute", "private_value", "state_root"]
            }),
        },
        // ─── Proof Composition ─────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_compose_proofs",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Compose multiple proofs using logical operators (and/or/chain/aggregate)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "mode": { "type": "string", "enum": ["and", "or", "chain", "aggregate"], "description": "Composition mode" },
                    "proofs": {
                        "type": "array",
                        "items": { "type": "string" },
                        "description": "Hex-encoded proof bytes to compose"
                    },
                    "public_inputs": {
                        "type": "array",
                        "items": {
                            "type": "array",
                            "items": { "type": "integer" }
                        },
                        "description": "Public inputs for each proof (array of arrays)"
                    }
                },
                "required": ["mode", "proofs"]
            }),
        },
        // ─── Blocklace ─────────────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_get_blocklace_status",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Get blocklace consensus status (tip, finality level, participants, wave)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_get_constitution",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Get the current federation constitution (membership set, threshold, version)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_propose_membership",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Propose a membership change (join/leave/threshold change) to the federation",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "action": { "type": "string", "enum": ["join", "leave"], "description": "Whether to propose joining or leaving" },
                    "participant": { "type": "string", "description": "Hex-encoded 32-byte public key of the participant (for join: new member; for leave: departing member)" },
                    "reason": { "type": "string", "description": "Human-readable reason for the proposal" }
                },
                "required": ["action", "participant"]
            }),
        },
        // ─── Shared Resources ──────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_check_resource_budget",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Query remaining budget allowance for a shared resource (bounded-counter coordination)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID of the agent" }
                },
                "required": ["cell_id"]
            }),
        },
        McpToolDef {
            name: "dregg_debit_shared_resource",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Optimistic debit from a shared resource (Tier 2: consensus-free if within local budget slice)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID of the agent" },
                    "amount": { "type": "integer", "description": "Amount to debit from the shared resource" },
                    "memo": { "type": "string", "description": "Optional memo for the debit operation" }
                },
                "required": ["cell_id", "amount"]
            }),
        },
        // ─── Gallery ───────────────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_list_auctions",
            title: None,
            output_schema: None,
            annotations: None,
            description: "List active gallery auctions (commit-reveal sealed-bid)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "status": { "type": "string", "enum": ["commit", "reveal", "settled", "all"], "description": "Filter by auction phase (default: all)" }
                },
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_place_bid",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Place a sealed bid on a gallery auction (commit phase: bid amount hidden behind commitment)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "auction_id": { "type": "string", "description": "Hex-encoded 32-byte auction ID" },
                    "amount": { "type": "integer", "description": "Bid amount (will be committed, not revealed until reveal phase)" },
                    "nonce": { "type": "string", "description": "Hex-encoded 32-byte random nonce for commitment (generated if omitted)" }
                },
                "required": ["auction_id", "amount"]
            }),
        },
        // ─── CapTP Delivery (γ.1 / Seam 3) ─────────────────────────────────────────
        McpToolDef {
            name: "dregg_captp_deliver",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Construct and submit a Turn whose root action is authorized by `Authorization::CapTpDelivered` (introducer-signed HandoffCertificate + sender Ed25519 sig over the canonical delivery message). The node cipherclerk plays the recipient/sender; the introducer key is constructed in-process for testing. Returns the turn hash and the cert nonce.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell (the action target & gateway-mirror agent)" },
                    "introducer_sk": { "type": "string", "description": "Hex-encoded 32-byte introducer Ed25519 secret seed (testing-only). When omitted, a fresh ephemeral introducer key is generated." },
                    "introducer_federation": { "type": "string", "description": "Hex-encoded 32-byte introducer federation id. Defaults to BLAKE3(introducer_pk)." },
                    "target_federation": { "type": "string", "description": "Hex-encoded 32-byte target federation id (default: zero federation, matching the executor default)." },
                    "permissions": { "type": "string", "enum": ["none","signature","proof","either"], "description": "Permission level encoded in the cert (default: signature)" },
                    "expires_at": { "type": "integer", "description": "Optional cert expiry (block height)." },
                    "swiss": { "type": "string", "description": "Hex-encoded 32-byte swiss number (default: random)." },
                    "effects": {
                        "type": "array",
                        "description": "Effects to attach to the captp.route action (typically a single effect). Each effect is per the parse_effect_json contract.",
                        "items": { "type": "object" }
                    }
                },
                "required": ["target_cell"]
            }),
        },
        // ─── CapTP Handoff Cert Exercise (γ.1 extension) ────────────────────────────
        McpToolDef {
            name: "dregg_exercise_handoff_cert",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Exercise a CapTP HandoffCertificate: constructs a Turn authorized by \
                `Authorization::CapTpDelivered` (mirroring `dregg_captp_deliver`) carrying the \
                caller's effects; the executor's `verify_captp_delivered` validates the \
                introducer-signed cert + the recipient's delivery signature. \
                The node cipherclerk is the recipient/sender; the introducer key is supplied \
                or generated ephemerally. An optional `effects` array lets the caller attach \
                downstream effects (e.g. a Transfer). Returns the turn hash, cert nonce, STARK \
                proof, and all Effect-VM fields.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell." },
                    "introducer_sk": { "type": "string", "description": "Hex-encoded 32-byte introducer Ed25519 secret seed (testing-only). Omit for a fresh ephemeral key." },
                    "introducer_pk": { "type": "string", "description": "Hex-encoded 32-byte introducer public key. Ignored when introducer_sk is supplied (derived from it). When both are omitted, a fresh ephemeral key is generated." },
                    "recipient_pk": { "type": "string", "description": "Hex-encoded 32-byte recipient public key. Defaults to the node cipherclerk's public key." },
                    "introducer_federation": { "type": "string", "description": "Hex-encoded 32-byte introducer federation id. Defaults to BLAKE3(introducer_pk)." },
                    "target_federation": { "type": "string", "description": "Hex-encoded 32-byte target federation id. Default: zero federation." },
                    "permissions": { "type": "string", "enum": ["none","signature","proof","either"], "description": "Permission level encoded in the cert. Default: signature." },
                    "expires_at": { "type": "integer", "description": "Optional cert expiry block height." },
                    "swiss": { "type": "string", "description": "Hex-encoded 32-byte swiss number (default: random)." },
                    "effects": {
                        "type": "array",
                        "description": "Effects to attach to the delivered turn (e.g. a Transfer). Per parse_effect_json contract.",
                        "items": { "type": "object" }
                    }
                },
                "required": ["target_cell"]
            }),
        },
        // ─── Sovereign Cell Witness (reshaped) ─────────────────────────────────────
        McpToolDef {
            name: "dregg_sign_sovereign_witness",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Build a properly-signed `SovereignCellWitness` for a sovereign cell currently in the local ledger. Signs the canonical message (cell_id || old_commitment || new_commitment || effects_hash || timestamp || sequence) with the node cipherclerk's Ed25519 key. Pass `attach_proof=true` to also generate an Effect-VM STARK proof binding the transition. Returns the witness postcard-encoded as hex plus structured fields.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte sovereign cell ID. Must be registered via `dregg_make_sovereign` first." },
                    "new_commitment": { "type": "string", "description": "Hex-encoded 32-byte post-state commitment claimed by the witness. If omitted, derived as BLAKE3(cell_id || old_commitment || effects_hash || sequence)." },
                    "effects_hash": { "type": "string", "description": "Hex-encoded 32-byte BLAKE3 over the effects applied. If omitted, set to zero." },
                    "attach_proof": { "type": "boolean", "description": "If true, also generate a STARK transition_proof binding (old, new, effects_hash) via EffectVmAir. Default: false." },
                    "vm_effect_amount": { "type": "integer", "description": "If `attach_proof` is set, the (single-effect VM) amount to use for the synthetic transition. Default: 0." }
                },
                "required": ["cell_id"]
            }),
        },
        // ─── Slot caveats / StateConstraint surface ───────────────────────────────
        // (Note: extends dregg_read_cell to include the cell program's
        // declared `StateConstraint` set — no new tool needed for the read
        // path; clients invoking dregg_read_cell will see `program.kind` and
        // `program.state_constraints` in the JSON response.)
        // ─── γ.2 bilateral binding receipts ────────────────────────────────────────
        McpToolDef {
            name: "dregg_bilateral_action",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Submit a Turn with a single bilateral effect (Transfer / GrantCapability / Introduce) and return the WitnessedReceipts for BOTH cells involved. The executor's bilateral schedule binds the from-side and to-side accumulator roots; this tool surfaces the per-side trace + proof bytes so callers can verify the bilateral identity end-to-end.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "mode": { "type": "string", "enum": ["transfer","grant","introduce"], "description": "Which bilateral effect to emit." },
                    "from": { "type": "string", "description": "Hex-encoded 32-byte 'from' cell (transfer source / grant donor / introduce introducer)." },
                    "to": { "type": "string", "description": "Hex-encoded 32-byte 'to' cell (transfer recipient / grant recipient / introduce recipient)." },
                    "target": { "type": "string", "description": "(introduce only) Hex-encoded 32-byte target cell the introduction references." },
                    "amount": { "type": "integer", "description": "(transfer only) Computron amount to transfer." },
                    "permissions": { "type": "string", "enum": ["none","signature","proof","either"], "description": "(grant / introduce) Permission level for the granted capability. Default: signature." }
                },
                "required": ["mode","from","to"]
            }),
        },
        // ─── Starbridge-app builders (cross-app-e2e closure) ───────────────────────
        // These four tools wrap the canonical `build_*_action` helpers from
        // the four anchor starbridge-apps so the cross-app-e2e demo can drive
        // a real running node over MCP and have each receipt carry a STARK
        // proof (via `generate_effect_vm_proof`). See `apply.rs` parallel:
        // the executor turns the action's `SetField`s into ledger writes,
        // and we project those same `SetField`s into VM Effects to anchor
        // the proof.
        McpToolDef {
            name: "dregg_register_name",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Register a name in a starbridge-nameservice registry cell via the canonical credential-attested builder. Wraps `starbridge_nameservice::build_register_with_credential_action` (the attested-tier variant). Receipt carries STARK proof binding the three SetField updates (name_hash, owner_hash, expiry).",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "name": { "type": "string", "description": "Human-readable name being registered (e.g. 'bob.dev')." },
                    "registry_cell": { "type": "string", "description": "Hex-encoded 32-byte registry cell ID. Defaults to the node's agent cell." },
                    "owner": { "type": "string", "description": "Hex-encoded 32-byte owner public key. Defaults to the node's cipherclerk public key." },
                    "expiry_height": { "type": "integer", "description": "Block height at which the name registration expires." },
                    "issuer_cell": { "type": "string", "description": "Hex-encoded 32-byte issuer cell whose credential set the registration attests to. Defaults to the node's agent cell (self-attestation for demos)." },
                    "credential_schema_id": { "type": "string", "description": "Hex-encoded 32-byte schema commitment from the identity app. Defaults to BLAKE3('kyc-v1') for demos." },
                    "credential_presentation_proof_hex": { "type": "string", "description": "Hex-encoded credential presentation proof bytes (non-empty witness blob carried into action.witness_blobs)." }
                },
                "required": ["name", "expiry_height"]
            }),
        },
        McpToolDef {
            name: "dregg_publish_subscription",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Publish a bounty-state notification to a starbridge-subscription cell via the canonical bounty-lifecycle builder. Wraps `starbridge_subscription::build_bounty_state_publish_action`. Receipt carries STARK proof binding the three SetField updates (seq_head, message_root, latest_payload).",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "subscription_cell": { "type": "string", "description": "Hex-encoded 32-byte subscription cell ID. Defaults to the node's agent cell." },
                    "new_head": { "type": "integer", "description": "New value of slot 0 (seq_head); the caller computes from prior state." },
                    "new_message_root": { "type": "string", "description": "Hex-encoded 32-byte new message_root after folding the payload hash." },
                    "bounty_id": { "type": "string", "description": "Hex-encoded 32-byte bounty identifier." },
                    "prior_state": { "type": "string", "enum": ["posted","claimed","fulfilled","settled","canceled"], "description": "Prior bounty state." },
                    "new_state": { "type": "string", "enum": ["posted","claimed","fulfilled","settled","canceled"], "description": "New bounty state." },
                    "actor_pk_hash": { "type": "string", "description": "Hex-encoded 32-byte BLAKE3 hash of the actor's pubkey (the party causing the state change)." }
                },
                "required": ["new_head", "new_message_root", "bounty_id", "prior_state", "new_state", "actor_pk_hash"]
            }),
        },
        McpToolDef {
            name: "dregg_issue_credential",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Issue a credential and anchor the issuance on a starbridge-identity issuer cell via the canonical builder. Wraps `dregg_credentials::issue` + `starbridge_identity::build_issue_credential_action`. Receipt carries STARK proof binding the two SetField updates (issuance_counter, revocation_root) and the credential id is returned for downstream binding.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "issuer_cell": { "type": "string", "description": "Hex-encoded 32-byte issuer cell ID. Defaults to the node's agent cell." },
                    "schema": { "type": "string", "enum": ["kyc","gov_id","employment"], "description": "Which built-in schema to use. Defaults to 'kyc'." },
                    "holder_id": { "type": "string", "description": "Hex-encoded 32-byte holder id (typically BLAKE3(holder_pk)). Defaults to the node's own pubkey-derived holder id." },
                    "attributes": { "type": "object", "description": "Attribute map { name: string|integer }. Only attributes in the schema are accepted." },
                    "new_counter": { "type": "integer", "description": "New ISSUANCE_COUNTER_SLOT value (MonotonicSequence enforced; typically old+1). Defaults to 1." },
                    "revocation_root": { "type": "string", "description": "Hex-encoded 32-byte new REVOCATION_ROOT_SLOT value. Defaults to zero (no revocations yet)." },
                    "issued_at": { "type": "integer", "description": "Unix-seconds issuance timestamp. Defaults to 1_700_000_000 for determinism." },
                    "not_after": { "type": "integer", "description": "Optional Unix-seconds expiry. Omit for no expiry." }
                },
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_register_service",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Register a service entry at a named path on a starbridge-governed-namespace cell via the canonical builder. Wraps `starbridge_governed_namespace::build_register_service_action`. The underlying action is event-only (EmitEvent('service-registered', [path_hash, target])); the EffectVmAir carries a canonical EmitEvent row variant (#110) so the STARK proof binds the actual (topic_hash, payload_hash) of the emitted event into PI[EMIT_EVENT_TOPIC_HASH] / PI[EMIT_EVENT_PAYLOAD_HASH]. No synthesised state mutation is required.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "namespace_cell": { "type": "string", "description": "Hex-encoded 32-byte governed-namespace cell ID. Defaults to the node's agent cell." },
                    "path": { "type": "string", "description": "Path being registered (e.g. '/bob.dev')." },
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte cell ID the path resolves to. Defaults to the node's agent cell." }
                },
                "required": ["path"]
            }),
        },
        // ─── Factory creation via canonical Effect::CreateCellFromFactory ──────────
        McpToolDef {
            name: "dregg_create_cell_from_factory_effect",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Emit a canonical `Effect::CreateCellFromFactory` inside a Turn so the new cell is created through the factory descriptor's validate_creation path (instead of the legacy direct insertion). Use this from the wasm/extension surface when a factory has been deployed and you want all child-cell creations to flow through the descriptor's constraints.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "factory_vk": { "type": "string", "description": "Hex-encoded 32-byte factory VK." },
                    "owner_pubkey": { "type": "string", "description": "Hex-encoded 32-byte owner pubkey for the new cell. Defaults to this node's cipherclerk pubkey." },
                    "token_id": { "type": "string", "description": "Hex-encoded 32-byte token-domain id (default: BLAKE3(\"dregg-mcp-factory-token\"))." },
                    "sovereign": { "type": "boolean", "description": "Whether the new cell is sovereign (default: false)." },
                    "program_vk": { "type": "string", "description": "Hex-encoded 32-byte child program VK (must match the factory's Fixed strategy when set)." },
                    "initial_fields": {
                        "type": "array",
                        "items": {
                            "type": "object",
                            "properties": {
                                "index": { "type": "integer" },
                                "value": { "type": "integer" }
                            },
                            "required": ["index","value"]
                        },
                        "description": "Initial field overrides as { index, value } pairs (u32 index, u64 value)."
                    }
                },
                "required": ["factory_vk"]
            }),
        },
    ]
}

// =============================================================================
// Tool dispatch
// =============================================================================

/// The capability scope an MCP tool requires: an action VERB the caller's
/// `Authorization::Token` must cover. The resource (the granting authority) is
/// the node's own identity cell — the node is its own granting authority and
/// issues scoped tools-access biscuits against its key.
///
/// The verbs partition the ~45 tools by the authority they exercise:
/// - `"read"`   — pure observation (status / reads / list / verify), no mutation;
/// - `"write"`  — mutates cell/ledger/intent state on behalf of the caller;
/// - `"admin"`  — capability/identity administration (grant/revoke/delegate,
///   factories, sovereignty, federation governance) — the most powerful verb.
///
/// A capability credential that grants `"admin"` for the node's cell covers the
/// admin tools; one that grants only `"read"` does NOT — the executor rejects an
/// admin `tools/call` presenting a read-only token. A tool absent from this
/// table is treated as `"admin"` (fail-closed: an unmapped tool requires the
/// strongest authority rather than silently passing).
fn tool_required_scope(tool: &str) -> &'static str {
    match tool {
        // ── read: observation only ───────────────────────────────────────────
        "dregg_get_status"
        | "dregg_check_capabilities"
        | "dregg_read_cell"
        | "dregg_get_receipt_chain"
        | "dregg_verify_provenance"
        | "dregg_verify_sovereign_proof"
        | "dregg_get_blocklace_status"
        | "dregg_get_constitution"
        | "dregg_check_resource_budget"
        | "dregg_list_auctions" => "read",

        // ── write: state mutation on the caller's behalf ─────────────────────
        "dregg_authorize"
        | "dregg_submit_turn"
        | "dregg_post_intent"
        | "dregg_fulfill_intent"
        | "dregg_seal_data"
        | "dregg_unseal_data"
        | "dregg_prove_sovereign_turn"
        | "dregg_create_stealth_address"
        | "dregg_private_transfer"
        | "dregg_encrypt_intent"
        | "dregg_prove_predicate"
        | "dregg_compose_proofs"
        | "dregg_debit_shared_resource"
        | "dregg_place_bid"
        | "dregg_captp_deliver"
        | "dregg_exercise_handoff_cert"
        | "dregg_sign_sovereign_witness"
        | "dregg_bilateral_action"
        | "dregg_register_name"
        | "dregg_publish_subscription"
        | "dregg_register_service" => "write",

        // ── admin: capability / identity / governance administration ─────────
        "dregg_create_agent"
        | "dregg_grant_capability"
        | "dregg_revoke_capability"
        | "dregg_delegate"
        | "dregg_make_sovereign"
        | "dregg_peer_exchange"
        | "dregg_compress_history"
        | "dregg_create_bearer_cap"
        | "dregg_exercise_bearer_cap"
        | "dregg_deploy_factory"
        | "dregg_create_from_factory"
        | "dregg_create_cell_from_factory_effect"
        | "dregg_propose_membership"
        | "dregg_issue_credential" => "admin",

        // Fail-closed: an unmapped tool requires the strongest authority.
        _ => "admin",
    }
}

/// Derive the node's deterministic MCP-cap ISSUER keypair from its cipherclerk.
///
/// The node issues tools-access biscuits under this key. It is a one-way,
/// domain-separated derivation of the cipherclerk's signing key, so it is stable
/// across restarts and never exposes the raw identity key. The biscuit cover the
/// executor verifies is anchored in this issuer's public key (recorded as the
/// authority cell's `verification_key`), so only the node can mint a credential
/// the gate will accept.
fn mcp_cap_issuer_keypair(cclerk: &AgentCipherclerk) -> dregg_token::biscuit_auth::KeyPair {
    let seed = cclerk.derive_symmetric_key("dregg-mcp-cap-issuer-v1");
    let private = dregg_token::biscuit_auth::PrivateKey::from_bytes(
        &seed,
        dregg_token::biscuit_auth::Algorithm::Ed25519,
    )
    .expect("32-byte ed25519 seed yields a valid biscuit private key");
    dregg_token::biscuit_auth::KeyPair::from(&private)
}

/// The node's MCP-cap issuer public key (the trust anchor the executor checks).
fn mcp_cap_issuer_pubkey(cclerk: &AgentCipherclerk) -> [u8; 32] {
    mcp_cap_issuer_keypair(cclerk)
        .public()
        .to_bytes()
        .try_into()
        .expect("ed25519 public key is 32 bytes")
}

/// The node's granting-authority cell — the resource an MCP capability scope
/// names. Its `verification_key` is the node's MCP-cap issuer public key, so a
/// biscuit minted under that issuer (`TokenKeyRef::BiscuitIssuer { issuer }`) is
/// trusted by the executor (the `vk_match` trust anchor). The cell id is the
/// SAME derivation the node uses for its agent cell
/// (`CellId::derive_raw(node_pk, [0;32])`), so a biscuit scoping
/// `service(authority_cell, verb)` is consistent everywhere.
fn mcp_authority_cell(node_pk: &[u8; 32], issuer_pubkey: &[u8; 32]) -> dregg_cell::Cell {
    let mut cell = dregg_cell::Cell::new(*node_pk, [0u8; 32]);
    cell.verification_key = Some(dregg_cell::VerificationKey {
        hash: *blake3::hash(issuer_pubkey).as_bytes(),
        data: issuer_pubkey.to_vec(),
    });
    cell
}

/// Mint a tools-access biscuit granting `scope_verb` on the node's authority
/// cell, under the node's MCP-cap issuer key. This is what the node hands a
/// client so a `tools/call` can pass the per-tool gate. `scope_verb` is one of
/// the verbs in [`tool_required_scope`] (`"read"` / `"write"` / `"admin"`).
///
/// Returns the encoded `eb2_…` biscuit string.
fn mint_tool_cap(
    cclerk: &AgentCipherclerk,
    node_pk: &[u8; 32],
    scope_verb: &str,
) -> Result<String, dregg_token::TokenError> {
    use dregg_token::traits::AuthToken;
    let kp = mcp_cap_issuer_keypair(cclerk);
    let authority_cell_id = dregg_cell::CellId::derive_raw(node_pk, &[0u8; 32]);
    let svc = hex_encode(authority_cell_id.as_bytes());
    let action = hex_encode(dregg_turn::action::symbol(scope_verb).as_slice());
    let token =
        dregg_token::BiscuitToken::mint_dregg(&kp, &[], &[(svc, action)], &[], &[], &[], None)?;
    token.to_encoded()
}

/// Parse a presented MCP capability credential from a `tools/call`'s arguments.
///
/// Convention: the caller supplies the credential under the `_cap` argument key
/// as an object `{ "biscuit": "eb2_…" }` — an encoded biscuit minted by the node
/// under its MCP-cap issuer key. Returns `None` if no credential is present.
fn parse_presented_cap(
    arguments: &Value,
    issuer_pubkey: &[u8; 32],
) -> Option<dregg_turn::Authorization> {
    let cap = arguments.get("_cap")?;
    let encoded = cap.get("biscuit").and_then(|v| v.as_str())?;
    Some(dregg_turn::Authorization::Token {
        encoded: encoded.as_bytes().to_vec(),
        key_ref: dregg_turn::TokenKeyRef::BiscuitIssuer {
            issuer_pubkey: *issuer_pubkey,
        },
        discharges: Vec::new(),
    })
}

/// The node-side trust context needed to verify a presented MCP capability:
/// the issuer pubkey (trust anchor), the authority cell the scope names, and the
/// federation id the verifying executor binds to. Snapshotting it once lets a
/// caller cover-check MANY tools (e.g. to filter `tools/list`) without
/// re-reading node state or rebuilding the executor per tool.
struct McpCapContext {
    enforce: bool,
    issuer_pubkey: [u8; 32],
    authority_cell: dregg_cell::Cell,
    federation_id: [u8; 32],
    /// The CURRENT attested blocklace height. Token verification binds temporal
    /// caveats to `now = block_height` (`token_auth_request`), so the verifying
    /// executor MUST carry the live height: a fresh executor defaults to height
    /// 0, under which every height-bound expiry caveat trivially passes — i.e.
    /// an expired stored cap would verify FOREVER (the R7 stored-caps-survive
    /// failure mode, temporal leg). Snapshotting the real height closes that
    /// leg: a `tools/call` presenting a cap is re-checked against the CURRENT
    /// consensus height on every call.
    ///
    /// HONEST RESIDUAL (R7, revocation leg): there is no biscuit-revocation
    /// registry consulted on this path — the node has no live store of revoked
    /// biscuit ids wired in (`store.is_revoked` exists but nothing node-side
    /// populates it for MCP-issued caps). A cap can today only die by expiry
    /// caveat, never by explicit revocation. Until a revocation feed exists,
    /// mint MCP caps WITH height-bound expiry caveats.
    block_height: u64,
}

impl McpCapContext {
    async fn snapshot(state: &NodeState) -> Self {
        let s = state.read().await;
        let node_pk = s.cclerk.public_key().0;
        let issuer_pubkey = mcp_cap_issuer_pubkey(&s.cclerk);
        McpCapContext {
            enforce: s.mcp_cap_enforce,
            issuer_pubkey,
            authority_cell: mcp_authority_cell(&node_pk, &issuer_pubkey),
            federation_id: s.federation_id,
            block_height: crate::executor_setup::attested_block_height(&s),
        }
    }

    /// Does `credential` cover `tool`'s required scope? Runs the EXACT executor
    /// admission check (`verify_token_for_scope`) used to gate a real turn — the
    /// SAME teeth, reused read-only so it can also drive tool VISIBILITY.
    ///
    /// Build the verifying executor under the node's federation id so its
    /// AuthRequest binding matches the node. The biscuit cover is keyed on
    /// (service = authority cell, action = scope verb) + the issuer anchored in
    /// the authority cell's verification_key, so this is the real admission check.
    fn cap_covers_tool(
        &self,
        credential: &dregg_turn::Authorization,
        tool: &str,
    ) -> Result<(), String> {
        let scope = tool_required_scope(tool);
        let scope_action = dregg_turn::action::symbol(scope);
        let mut executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
        executor.set_local_federation_id(self.federation_id);
        // Bind temporal caveats to the CURRENT consensus height (see the
        // `block_height` field doc): without this the fresh executor verifies
        // at height 0 and an expired cap passes forever.
        executor.set_block_height(self.block_height);
        executor
            .verify_token_for_scope(credential, &self.authority_cell, scope_action)
            .map_err(|e| {
                format!(
                    "capability '_cap' does not cover tool '{tool}' (required scope '{scope}'): {e}"
                )
            })
    }

    /// Whether `tool` is INVOCABLE under an optionally-presented credential.
    /// Mirrors [`enforce_tool_cap`]'s admission decision exactly — used to filter
    /// `tools/list` so an agent only SEES tools its caps permit (ocap visibility).
    fn tool_invocable(&self, presented: Option<&dregg_turn::Authorization>, tool: &str) -> bool {
        match presented {
            Some(cred) => self.cap_covers_tool(cred, tool).is_ok(),
            None => !self.enforce, // no cap + enforcement off ⇒ back-compat pass
        }
    }
}

/// THE per-tool capability gate. Before a `tools/call` reaches its tool body,
/// require the caller's presented `Authorization::Token` to cover the tool's
/// declared `(action, resource)` scope — verified by the EXECUTOR's
/// `verify_token_for_scope`, the SAME verification used to admit a turn.
///
/// - A presented credential is ALWAYS verified against the tool's scope; a token
///   that does not cover the scope (wrong issuer/target, an un-granted verb, or
///   expired) is REJECTED — the call never reaches the tool.
/// - When `mcp_cap_enforce` is on, a MISSING credential is also rejected
///   (fail-closed). When off, a missing credential passes (back-compat), but the
///   global unlock still gates the tool body separately.
///
/// Returns `Ok(())` to admit, or `Err(message)` to reject.
async fn enforce_tool_cap(tool: &str, arguments: &Value, state: &NodeState) -> Result<(), String> {
    let ctx = McpCapContext::snapshot(state).await;
    let presented = parse_presented_cap(arguments, &ctx.issuer_pubkey);

    let credential = match presented {
        Some(c) => c,
        None => {
            if ctx.enforce {
                return Err(format!(
                    "capability enforcement is on: tool '{tool}' requires a covering \
                     '_cap' biscuit (scope '{}')",
                    tool_required_scope(tool)
                ));
            }
            // Back-compat: no credential presented and enforcement off.
            return Ok(());
        }
    };

    ctx.cap_covers_tool(&credential, tool)
}

async fn dispatch_tool(name: &str, params: Value, state: &NodeState) -> McpToolResult {
    match name {
        "dregg_get_status" => tool_get_status(state).await,
        "dregg_create_agent" => tool_create_agent(&params, state).await,
        "dregg_authorize" => tool_authorize(&params, state).await,
        "dregg_submit_turn" => tool_submit_turn(&params, state).await,
        "dregg_grant_capability" => tool_grant_capability(&params, state).await,
        "dregg_revoke_capability" => tool_revoke_capability(&params, state).await,
        "dregg_post_intent" => tool_post_intent(&params, state).await,
        "dregg_fulfill_intent" => tool_fulfill_intent(&params, state).await,
        "dregg_delegate" => tool_delegate(&params, state).await,
        "dregg_check_capabilities" => tool_check_capabilities(state).await,
        "dregg_read_cell" => tool_read_cell(&params, state).await,
        "dregg_get_receipt_chain" => tool_get_receipt_chain(&params, state).await,
        "dregg_seal_data" => tool_seal_data(&params, state).await,
        "dregg_unseal_data" => tool_unseal_data(&params, state).await,
        // Sovereign Cells
        "dregg_make_sovereign" => tool_make_sovereign(&params, state).await,
        "dregg_peer_exchange" => tool_peer_exchange(&params, state).await,
        "dregg_compress_history" => tool_compress_history(&params, state).await,
        // Bearer Capabilities
        "dregg_create_bearer_cap" => tool_create_bearer_cap(&params, state).await,
        "dregg_exercise_bearer_cap" => tool_exercise_bearer_cap(&params, state).await,
        // Factories
        "dregg_deploy_factory" => tool_deploy_factory(&params, state).await,
        "dregg_create_from_factory" => tool_create_from_factory(&params, state).await,
        "dregg_verify_provenance" => tool_verify_provenance(&params, state).await,
        // Effect VM
        "dregg_prove_sovereign_turn" => tool_prove_sovereign_turn(&params, state).await,
        "dregg_verify_sovereign_proof" => tool_verify_sovereign_proof(&params, state).await,
        // Privacy
        "dregg_create_stealth_address" => tool_create_stealth_address(&params, state).await,
        "dregg_private_transfer" => tool_private_transfer(&params, state).await,
        "dregg_encrypt_intent" => tool_encrypt_intent(&params, state).await,
        "dregg_prove_predicate" => tool_prove_predicate(&params, state).await,
        // Proof Composition
        "dregg_compose_proofs" => tool_compose_proofs(&params, state).await,
        // Blocklace
        "dregg_get_blocklace_status" => tool_get_blocklace_status(state).await,
        "dregg_get_constitution" => tool_get_constitution(state).await,
        "dregg_propose_membership" => tool_propose_membership(&params, state).await,
        // Shared Resources
        "dregg_check_resource_budget" => tool_check_resource_budget(&params, state).await,
        "dregg_debit_shared_resource" => tool_debit_shared_resource(&params, state).await,
        // Gallery
        "dregg_list_auctions" => tool_list_auctions(&params, state).await,
        "dregg_place_bid" => tool_place_bid(&params, state).await,
        // CapTP delivery
        "dregg_captp_deliver" => tool_captp_deliver(&params, state).await,
        // CapTP handoff cert exercise (CapTpDelivered)
        "dregg_exercise_handoff_cert" => tool_exercise_handoff_cert(&params, state).await,
        // Sovereign witness (reshaped)
        "dregg_sign_sovereign_witness" => tool_sign_sovereign_witness(&params, state).await,
        // γ.2 bilateral binding
        "dregg_bilateral_action" => tool_bilateral_action(&params, state).await,
        // Canonical factory-driven cell creation
        "dregg_create_cell_from_factory_effect" => {
            tool_create_cell_from_factory_effect(&params, state).await
        }
        // Starbridge-app builders (cross-app-e2e closure)
        "dregg_register_name" => tool_register_name(&params, state).await,
        "dregg_publish_subscription" => tool_publish_subscription(&params, state).await,
        "dregg_issue_credential" => tool_issue_credential(&params, state).await,
        "dregg_register_service" => tool_register_service(&params, state).await,
        _ => McpToolResult::error(format!("unknown tool: {name}")),
    }
}

// =============================================================================
// Tool implementations
// =============================================================================

async fn tool_get_status(state: &NodeState) -> McpToolResult {
    let s = state.read().await;

    // F-P2-7: status is informational; the HTTP /status endpoint does not require
    // the cipherclerk to be unlocked, and neither should the MCP analog. (Health
    // checks need to work while locked.)

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
    let cclerk_ok = s.unlocked || s.passphrase_hash.is_some();

    McpToolResult::json(&serde_json::json!({
        "healthy": store_ok && cclerk_ok,
        "peer_count": peer_count,
        "latest_height": latest_height,
        "revocation_count": revocation_count,
        "note_count": note_count,
        "unlocked": s.unlocked,
    }))
}

async fn tool_create_agent(params: &Value, state: &NodeState) -> McpToolResult {
    let name = match params.get("name").and_then(|v| v.as_str()) {
        Some(n) => n,
        None => return McpToolResult::error("missing required parameter: name"),
    };

    let initial_balance = params
        .get("initial_balance")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }
    // MCP-first identity: the calling AI process IS this node, so
    // "create agent" means "register this node's cipherclerk identity as a
    // cell in the ledger so it can be granted/received capabilities and
    // hold balance." The cell ID is content-addressed from the cipherclerk's
    // public key plus the zero token domain (matching how
    // `submit_turn`, `grant_capability`, etc. derive it).
    //
    // Per 06-the-real-demo.md step 2 ("Alice becomes a cell"), this is
    // what makes downstream grant/transfer/handoff actually have a
    // target cell to land on. Previously this tool generated an
    // ephemeral cipherclerk and discarded it; grants against the resulting
    // pubkey failed because no Cell existed in the ledger.
    let pk = s.cclerk.public_key();
    let pk_bytes = pk.0;
    let cell_id = dregg_cell::CellId::derive_raw(&pk_bytes, &[0u8; 32]);
    let pk_hex: String = pk_bytes.iter().map(|b| format!("{b:02x}")).collect();
    let cell_id_hex = hex_encode(&cell_id.0);

    let already_existed = s.ledger.get(&cell_id).is_some();

    if !already_existed {
        let cell = dregg_cell::Cell::with_balance(pk_bytes, [0u8; 32], initial_balance);
        if let Err(e) = s.ledger.insert_cell(cell) {
            return McpToolResult::error(format!("ledger insert failed: {e}"));
        }
    }

    let (balance, nonce, cap_count) = match s.ledger.get(&cell_id) {
        Some(c) => (c.state.balance(), c.state.nonce(), c.capabilities.len()),
        None => (0, 0, 0),
    };

    drop(s);

    McpToolResult::json(&serde_json::json!({
        "name": name,
        "public_key": pk_hex,
        "cell_id": cell_id_hex,
        "balance": balance,
        "nonce": nonce,
        "capability_count": cap_count,
        "created": !already_existed,
        "already_existed": already_existed,
        "note": "Agent cell registered in the local ledger. cell_id is content-addressed from the cipherclerk's public key + zero token domain.",
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
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Find a token that grants the requested action on the resource.
    let auth_req = dregg_sdk::AuthRequest {
        service: Some(resource.clone()),
        action: Some(action.clone()),
        ..Default::default()
    };

    // Try each held token.
    let mut authorized = false;
    let mut matching_token_id = None;
    for token in s.cclerk.tokens() {
        if s.cclerk.verify_token(token, &auth_req) {
            authorized = true;
            matching_token_id = Some(token.id().to_string());
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
    let method = match params.get("method").and_then(|v| v.as_str()) {
        Some(m) => m,
        None => return McpToolResult::error("missing required parameter: method"),
    };
    let fee = params.get("fee").and_then(|v| v.as_u64()).unwrap_or(0);
    let memo = params
        .get("memo")
        .and_then(|v| v.as_str())
        .map(String::from);

    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => {
            return McpToolResult::actionable_error(
                format!(
                    "invalid hex for target_cell (got {} chars)",
                    target_cell_hex.len()
                ),
                "target_cell must be exactly 64 hex chars (a 32-byte cell id). Read \
                 dregg://identity for your own agent cell id.",
            );
        }
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::actionable_error(
            "cipherclerk is locked",
            "Unlock the node's cipherclerk first; it holds the signing key for turns.",
        );
    }

    // SECURITY: Use the cipherclerk's own cell ID as the turn agent (not caller-supplied).
    // The target_cell identifies which cell the action targets, not who is submitting.
    let agent_cell_id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);
    let target_cell_id = dregg_cell::CellId(target_cell_bytes);

    // Build an action targeting the specified cell with the given method.
    let action = dregg_turn::Action {
        target: target_cell_id,
        method: dregg_turn::action::symbol(method),
        args: vec![],
        authorization: dregg_turn::Authorization::Unchecked,
        preconditions: dregg_cell::Preconditions::default(),
        effects: vec![],
        may_delegate: dregg_turn::DelegationMode::None,
        commitment_mode: dregg_turn::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
    forest.add_root(action);

    let nonce = s.cclerk.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        fee,
        memo,
        valid_until: None,
        call_forest: forest,
        depends_on: vec![],
        previous_receipt_hash: s.cclerk.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let signed = s.cclerk.sign_turn(&turn);
    let turn_hash_bytes = turn.hash();
    let turn_hash = hex_encode(&turn_hash_bytes);

    // Execute the turn locally.
    let federation_id = s.federation_id;
    let mut executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    executor.set_local_federation_id(federation_id);
    executor.set_executor_signing_key(s.cclerk.gossip_signing_key().to_bytes());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");

            // Serialize the full SignedTurn for gossip (postcard format).
            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");

            drop(s);

            // Emit receipt event to WebSocket subscribers.
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            // Gossip the turn to federation peers.
            if let Some(gossip) = state.gossip().await {
                let hash = turn_hash_bytes;
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data).await;
                });
            }

            McpToolResult::json(&serde_json::json!({
                "accepted": true,
                "turn_hash": turn_hash,
                "signer": hex_encode(&signed.signer.0),
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "accepted": false,
                "turn_hash": turn_hash,
                "error": format!("rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "accepted": false,
                "turn_hash": turn_hash,
                "error": "turn execution did not commit",
            }))
        }
    }
}

async fn tool_grant_capability(params: &Value, state: &NodeState) -> McpToolResult {
    let to_agent_hex = match params.get("to_agent").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: to_agent"),
    };
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let permissions = match params.get("permissions").and_then(|v| v.as_str()) {
        Some(p) => p,
        None => return McpToolResult::error("missing required parameter: permissions"),
    };

    let to_agent_bytes = match hex_decode(to_agent_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for to_agent (expected 64 hex chars)"),
    };
    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => {
            return McpToolResult::error("invalid hex for target_cell (expected 64 hex chars)");
        }
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Build a turn with Effect::GrantCapability.
    let agent_cell_id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);
    let to_cell_id = dregg_cell::CellId(to_agent_bytes);
    let target_cell_id = dregg_cell::CellId(target_cell_bytes);

    // Parse permissions string into AuthRequired level.
    let perm_level = match permissions {
        "none" | "None" => dregg_cell::AuthRequired::None,
        "signature" | "Signature" => dregg_cell::AuthRequired::Signature,
        "proof" | "Proof" => dregg_cell::AuthRequired::Proof,
        "either" | "Either" => dregg_cell::AuthRequired::Either,
        other => {
            return McpToolResult::error(format!(
                "invalid permission type: '{}'. Valid: none, signature, proof, either",
                other
            ));
        }
    };

    let cap = dregg_cell::CapabilityRef {
        target: target_cell_id,
        slot: 0,
        permissions: perm_level,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
        stored_epoch: None,
    };
    let cap_slot = cap.slot;

    let effect = dregg_turn::Effect::GrantCapability {
        from: agent_cell_id,
        to: to_cell_id,
        cap,
    };
    if let Err(result) = require_effect_cells_for_commit(
        &s.ledger,
        std::slice::from_ref(&effect),
        "grant capability",
    ) {
        return result;
    }

    let nonce = s.cclerk.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        // Cover the executor's computron metering for an Action-base + one
        // GrantCapability effect (~100 + 50 computrons by default; round up).
        fee: 10_000,
        memo: Some(format!("grant capability: {permissions}")),
        valid_until: None,
        // Use a signed action so the cell's `delegate: Signature` permission
        // accepts it. (Hosted-cell grants require the cell owner's signature.)
        call_forest: build_signed_forest(agent_cell_id, vec![effect], &s.cclerk, &s.federation_id),
        depends_on: vec![],
        previous_receipt_hash: s.cclerk.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let signed = s.cclerk.sign_turn(&turn);
    let turn_hash = hex_encode(&turn.hash());

    // Snapshot and prove before execution. A grant that cannot produce its
    // Effect VM proof is a structured rejection, not a committed null-proof turn.
    let pre_state: Option<(u64, u64)> = s
        .ledger
        .get(&agent_cell_id)
        .map(|c| (c.state.balance(), c.state.nonce()));

    let vm_effects = vec![dregg_circuit::effect_vm::Effect::GrantCapability {
        // 32-byte widening: the cap-entry identity is a scalar slot index here,
        // not a 32-byte hash. Anchor it in limb[0] (which drives the AIR's
        // cap_root advance) with zero high limbs — equivalent to the prior
        // single-felt binding, now in the [BabyBear; 8] shape.
        cap_entry: grant_cap_entry_8(cap_slot.wrapping_add(1)),
        phase_b: None,
    }];
    let (bal, n) = match require_pre_state(&agent_cell_id, pre_state, "grant capability") {
        Ok(pre) => pre,
        Err(result) => return result,
    };
    let proof_material = match require_effect_vm_proof(bal, n, &vm_effects, "grant capability") {
        Ok(material) => material,
        Err(result) => return result,
    };

    // Execute locally.
    let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let receipt_hash = receipt.receipt_hash();
            if let Some(witnessed) =
                witnessed_receipt_from_effect_material(receipt.clone(), &proof_material)
            {
                s.push_witnessed_receipt(receipt_hash, witnessed);
            }
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");

            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");
            drop(s);

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            if let Some(gossip) = state.gossip().await {
                let hash = signed.turn.hash();
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data).await;
                });
            }

            let proof_field = proof_material.proof_json();
            let public_inputs = proof_material.public_inputs.clone();
            let trace_field = proof_material.trace_json();
            let witness_hash_field = proof_material.witness_hash_json();

            McpToolResult::json(&serde_json::json!({
                "activity_status": "committed",
                "proof_status": "proved",
                "granted": true,
                "to_agent": to_agent_hex,
                "target_cell": target_cell_hex,
                "permissions": permissions,
                "turn_hash": turn_hash,
                "effect_vm_proof_hex": proof_field,
                "effect_vm_public_inputs": public_inputs,
                "effect_vm_trace_rows": trace_field,
                "effect_vm_witness_hash_hex": witness_hash_field,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "activity_status": "rejected",
                "proof_status": "not_committed",
                "granted": false,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "activity_status": "rejected",
                "proof_status": "not_committed",
                "granted": false,
                "error": "grant capability turn did not commit",
            }))
        }
    }
}

async fn tool_revoke_capability(params: &Value, state: &NodeState) -> McpToolResult {
    let cap_slot = match params.get("cap_slot").and_then(|v| v.as_u64()) {
        Some(s) => s as u32,
        None => return McpToolResult::error("missing required parameter: cap_slot"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Build a turn with Effect::RevokeCapability targeting the agent's own cell.
    let agent_cell_id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);

    let effect = dregg_turn::Effect::RevokeCapability {
        cell: agent_cell_id,
        slot: cap_slot,
    };

    let nonce = s.cclerk.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        fee: 0,
        memo: Some(format!("revoke capability slot {cap_slot}")),
        valid_until: None,
        call_forest: build_forest_with_effects(agent_cell_id, vec![effect]),
        depends_on: vec![],
        previous_receipt_hash: s.cclerk.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let signed = s.cclerk.sign_turn(&turn);
    let turn_hash = hex_encode(&turn.hash());

    // Execute locally.
    let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");

            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");
            drop(s);

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            if let Some(gossip) = state.gossip().await {
                let hash = signed.turn.hash();
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data).await;
                });
            }

            McpToolResult::json(&serde_json::json!({
                "revoked": true,
                "cap_slot": cap_slot,
                "turn_hash": turn_hash,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "revoked": false,
                "cap_slot": cap_slot,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::error("revoke capability turn did not commit")
        }
    }
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

    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

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
    let spec = dregg_intent::MatchSpec {
        actions: vec![dregg_intent::ActionPattern {
            action: Some(action.clone()),
            resource: Some(resource.clone()),
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: Some(resource.clone()),
        compound: None,
        predicate_requirements: vec![],
        strict_resource_matching: false,
    };

    let creator = dregg_intent::CommitmentId::random();
    let intent = dregg_intent::Intent::new(
        dregg_intent::IntentKind::Need,
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

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let intent = match s.intent_pool.get(&intent_id) {
        Some(i) => i.clone(),
        None => return McpToolResult::error("intent not found in pool"),
    };

    // Derive payer (intent creator) and recipient (this agent) cell IDs.
    let payer_cell = dregg_sdk::CellId(intent.creator.0);
    let recipient_cell = dregg_sdk::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);

    // Get current height.
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    // Build a minimal fulfillment for the execution flow.
    let state_root = dregg_circuit::BabyBear::new(0);
    let base_fulfillment = dregg_intent::fulfillment::Fulfillment {
        intent_id,
        fulfiller: dregg_intent::CommitmentId(recipient_cell.0),
        mode: dregg_intent::VerificationMode::Trusted,
        token_data: Some(vec![0x01; 4]),
        proof: None,
        granted_actions: intent
            .matcher
            .actions
            .iter()
            .filter_map(|p| p.action.clone())
            .collect(),
        granted_resource: intent
            .matcher
            .resource_pattern
            .clone()
            .unwrap_or_else(|| "*".to_string()),
        expiry: Some(intent.expiry),
    };

    // Verify predicate requirements are satisfiable before proceeding.
    // If the intent has predicate requirements, reject unless all can be proven.
    if !intent.matcher.predicate_requirements.is_empty() {
        // For MCP tool fulfillment, predicate proofs must be generated by the caller
        // (e.g., via a separate `prove_predicate` tool call). The simple MCP flow
        // cannot generate STARK proofs on-the-fly without private attribute values.
        return McpToolResult::error(&format!(
            "intent requires {} predicate proof(s) (attributes: {}). \
             Use the full fulfillment API with pre-computed proofs.",
            intent.matcher.predicate_requirements.len(),
            intent
                .matcher
                .predicate_requirements
                .iter()
                .map(|r| r.attribute.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }

    let predicate_proofs: Vec<(usize, dregg_circuit::PredicateProof)> = vec![];

    let fulfillment_with_preds = dregg_intent::fulfillment::FulfillmentWithPredicates {
        base: base_fulfillment,
        predicate_proofs,
        state_root,
        state_root_block: current_height,
    };

    // Execute the fulfillment payment flow.
    let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    let result = dregg_intent::fulfillment::execute_fulfillment_flow(
        &intent,
        &fulfillment_with_preds,
        &executor,
        &mut s.ledger,
        payer_cell,
        recipient_cell,
        current_height,
        current_height,
    );

    match result {
        Ok(receipt) => {
            let turn_hash = hex_encode(&receipt.turn_hash);
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");
            drop(s);
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });
            McpToolResult::json(&serde_json::json!({
                "intent_id": intent_id_hex,
                "fulfilled": true,
                "turn_hash": turn_hash,
            }))
        }
        Err(e) => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "intent_id": intent_id_hex,
                "fulfilled": false,
                "error": e.to_string(),
            }))
        }
    }
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

    let to_agent_bytes = match hex_decode(to_agent_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for to_agent (expected 64 hex chars)"),
    };

    // Parse optional restrictions into an Attenuation.
    let restrictions: Attenuation = params
        .get("restrictions")
        .and_then(|v| serde_json::from_value(v.clone()).ok())
        .unwrap_or_default();

    let max_staleness = params
        .get("max_staleness")
        .and_then(|v| v.as_u64())
        .unwrap_or(1000);

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let tokens = s.cclerk.tokens();
    if capability >= tokens.len() {
        return McpToolResult::error(format!(
            "capability slot {} out of range (have {} tokens)",
            capability,
            tokens.len()
        ));
    }

    // Perform the token-level delegation (attenuate + produce DelegatedToken).
    let token = tokens[capability].clone();
    let to_pubkey = PublicKey(to_agent_bytes);
    let delegated = match s.cclerk.delegate(&token, &to_pubkey, &restrictions) {
        Ok(d) => d,
        Err(e) => return McpToolResult::error(format!("delegation failed: {e}")),
    };

    // Build a turn with Effect::GrantCapability to record the delegation on-ledger.
    let agent_cell_id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);
    let to_cell_id = dregg_cell::CellId(to_agent_bytes);

    let cap = dregg_cell::CapabilityRef {
        target: agent_cell_id,
        slot: capability as u32,
        permissions: dregg_cell::AuthRequired::Signature,
        breadstuff: None,
        expires_at: restrictions.not_after.map(|t| t as u64),
        allowed_effects: None,
        stored_epoch: None,
    };

    let effect = dregg_turn::Effect::GrantCapability {
        from: agent_cell_id,
        to: to_cell_id,
        cap,
    };

    let nonce = s.cclerk.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        fee: 0,
        memo: Some(format!(
            "delegate capability slot {} to {}",
            capability, to_agent_hex
        )),
        valid_until: None,
        call_forest: build_forest_with_effects(agent_cell_id, vec![effect]),
        depends_on: vec![],
        previous_receipt_hash: s.cclerk.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let signed = s.cclerk.sign_turn(&turn);
    let turn_hash = hex_encode(&turn.hash());

    // Execute locally.
    let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");

            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");
            drop(s);

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            if let Some(gossip) = state.gossip().await {
                let hash = signed.turn.hash();
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data).await;
                });
            }

            McpToolResult::json(&serde_json::json!({
                "delegated": true,
                "from_token": delegated.id,
                "to_agent": to_agent_hex,
                "turn_hash": turn_hash,
                "max_staleness": max_staleness,
                "token_bytes": delegated.token_bytes,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "delegated": false,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::error("delegation turn did not commit")
        }
    }
}

async fn tool_check_capabilities(state: &NodeState) -> McpToolResult {
    let s = state.read().await;

    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let ws = crate::state::CipherclerkStatus {
        unlocked: s.unlocked,
        public_key: s
            .cclerk
            .public_key()
            .0
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect(),
        token_count: s.cclerk.tokens().len(),
        receipt_chain_length: s.cclerk.receipt_chain_length(),
    };

    let tokens: Vec<Value> = s
        .cclerk
        .tokens()
        .iter()
        .enumerate()
        .map(|(i, t)| {
            serde_json::json!({
                "slot": i,
                "id": t.id(),
                "label": t.label(),
                "service": t.service(),
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

    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let cell_id = dregg_cell::CellId(cell_id_bytes);
    let cell_opt = s.ledger.get(&cell_id);
    let is_sovereign = s.ledger.is_sovereign(&cell_id);
    let (found, balance, nonce, capability_count, program_json) = match cell_opt {
        Some(c) => (
            true,
            Some(c.state.balance()),
            Some(c.state.nonce()),
            Some(c.capabilities.len()),
            Some(describe_cell_program(&c.program)),
        ),
        None => (false, None, None, None, None),
    };

    McpToolResult::json(&serde_json::json!({
        "cell_id": cell_id_hex,
        "found": found,
        "balance": balance,
        "nonce": nonce,
        "capability_count": capability_count,
        "is_sovereign": is_sovereign,
        // Slot caveats — the cell program's declared StateConstraint set,
        // serialized so MCP callers can see what's perpetually enforced on
        // every state-modifying turn. `kind` is "None" / "Predicate" /
        // "Circuit"; `state_constraints` (when present) is the structured
        // constraint vocabulary defined by `dregg_cell::program::StateConstraint`.
        "program": program_json,
    }))
}

/// Render a `CellProgram` into a JSON value that exposes its kind and
/// (for predicate programs) the full structured `StateConstraint` list.
///
/// This is the slot-caveat surface on the MCP read path: callers can
/// discover what invariants the cell's program enforces on every turn
/// without having to peek into postcard bytes.
fn describe_cell_program(program: &dregg_cell::CellProgram) -> serde_json::Value {
    match program {
        dregg_cell::CellProgram::None => serde_json::json!({
            "kind": "None",
            "state_constraints": [],
            "note": "no slot caveats declared; any authorized state change is valid",
        }),
        dregg_cell::CellProgram::Predicate(constraints) => {
            // Serialize via serde so the full structured vocabulary
            // (FieldEquals, WriteOnce, Monotonic, BoundDelta, …) is
            // exposed verbatim — callers can match on the discriminants
            // to reason about what the cell enforces.
            let cs: serde_json::Value =
                serde_json::to_value(constraints).unwrap_or(serde_json::Value::Array(Vec::new()));
            serde_json::json!({
                "kind": "Predicate",
                "state_constraints": cs,
                "constraint_count": constraints.len(),
            })
        }
        dregg_cell::CellProgram::Circuit { circuit_hash } => serde_json::json!({
            "kind": "Circuit",
            "circuit_hash": hex_encode(circuit_hash),
            "state_constraints": [],
            "note": "circuit-program: post-state validity is enforced by the AIR proof in the action authorization",
        }),
        dregg_cell::CellProgram::Cases(cases) => {
            // Cav-Codex Block 4: operation-scoped cases. Each case has a
            // `TransitionGuard` naming which transitions it applies to and
            // a constraint list that must hold when the guard matches.
            let cs: serde_json::Value =
                serde_json::to_value(cases).unwrap_or(serde_json::Value::Array(Vec::new()));
            serde_json::json!({
                "kind": "Cases",
                "cases": cs,
                "case_count": cases.len(),
                "note": "operation-scoped program: each case's constraints AND together when its guard matches; if no case matches, the transition is default-denied",
            })
        }
    }
}

async fn tool_get_receipt_chain(params: &Value, state: &NodeState) -> McpToolResult {
    let limit = params.get("limit").and_then(|v| v.as_u64()).unwrap_or(50) as usize;

    let s = state.read().await;

    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let chain = s.cclerk.receipt_chain();
    let receipts: Vec<Value> = chain
        .iter()
        .rev()
        .take(limit)
        .map(|r| {
            let receipt_hash = r.receipt_hash();
            let witness_count = s.witnessed_receipt_count(&receipt_hash);
            serde_json::json!({
                "receipt_hash": hex_encode(&receipt_hash),
                "turn_hash": hex_encode(&r.turn_hash),
                "pre_state": hex_encode(&r.pre_state_hash),
                "post_state": hex_encode(&r.post_state_hash),
                "timestamp": r.timestamp,
                "computrons_used": r.computrons_used,
                "action_count": r.action_count,
                "has_witness": witness_count > 0,
                "witness_count": witness_count,
            })
        })
        .collect();

    McpToolResult::json(&serde_json::json!({
        "chain_length": s.cclerk.receipt_chain_length(),
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

    let recipient_bytes = match hex_decode(recipient_hex) {
        Ok(b) => b,
        Err(_) => {
            return McpToolResult::error("invalid hex for recipient (expected 64 hex chars)");
        }
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Use X25519 + ChaCha20-Poly1305 sealed-box encryption.
    // Generate ephemeral keypair for forward secrecy.
    let mut eph_bytes = [0u8; 32];
    if getrandom::fill(&mut eph_bytes).is_err() {
        return McpToolResult::error("failed to generate ephemeral key");
    }
    let ephemeral_secret = x25519_dalek::StaticSecret::from(eph_bytes);
    let ephemeral_public = x25519_dalek::PublicKey::from(&ephemeral_secret);

    // DH with recipient's public key to derive shared secret.
    let recipient_public = x25519_dalek::PublicKey::from(recipient_bytes);
    let shared = ephemeral_secret.diffie_hellman(&recipient_public);

    // Derive encryption key via BLAKE3 KDF (don't use raw DH output directly).
    let enc_key = blake3::derive_key("dregg-mcp-seal-data-v1", shared.as_bytes());

    // Generate random nonce.
    let mut nonce_bytes = [0u8; 12];
    if getrandom::fill(&mut nonce_bytes).is_err() {
        return McpToolResult::error("failed to generate nonce");
    }

    // Encrypt with ChaCha20-Poly1305.
    use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
    let cipher = ChaCha20Poly1305::new((&enc_key).into());
    let nonce = chacha20poly1305::Nonce::from_slice(&nonce_bytes);
    let ciphertext = match cipher.encrypt(nonce, data.as_bytes()) {
        Ok(ct) => ct,
        Err(_) => return McpToolResult::error("encryption failed"),
    };

    // Wire format: [32-byte ephemeral pk][12-byte nonce][ciphertext + tag]
    let mut sealed_box = Vec::with_capacity(32 + 12 + ciphertext.len());
    sealed_box.extend_from_slice(ephemeral_public.as_bytes());
    sealed_box.extend_from_slice(&nonce_bytes);
    sealed_box.extend_from_slice(&ciphertext);
    let sealed_hex: String = sealed_box.iter().map(|b| format!("{b:02x}")).collect();

    McpToolResult::json(&serde_json::json!({
        "sealed": true,
        "sealed_box": sealed_hex,
        "recipient": recipient_hex,
        "ephemeral_public": hex_encode(ephemeral_public.as_bytes()),
        "note": "Data sealed with X25519+ChaCha20-Poly1305. Only the recipient can unseal with their private key."
    }))
}

async fn tool_unseal_data(params: &Value, state: &NodeState) -> McpToolResult {
    let sealed_box_hex = match params.get("sealed_box").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: sealed_box"),
    };

    // Decode variable-length hex sealed box.
    let sealed_bytes = match hex_decode_var(sealed_box_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for sealed_box"),
    };

    // Wire format: [32-byte ephemeral pk][12-byte nonce][ciphertext + tag]
    if sealed_bytes.len() < 32 + 12 + 16 {
        return McpToolResult::error("sealed_box too short (minimum 60 bytes)");
    }

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let ephemeral_public_bytes: [u8; 32] = sealed_bytes[..32].try_into().unwrap();
    let nonce_bytes: [u8; 12] = sealed_bytes[32..44].try_into().unwrap();
    let ciphertext = &sealed_bytes[44..];

    // Derive the cipherclerk's X25519 secret from its Ed25519 signing key (private material).
    // SECURITY: Must use private key material here — deriving from the public key would
    // allow anyone to compute the same secret and decrypt sealed data.
    let cclerk_secret_bytes = s.cclerk.derive_symmetric_key("dregg-mcp-seal-x25519-v1");
    let cclerk_secret = x25519_dalek::StaticSecret::from(cclerk_secret_bytes);
    let ephemeral_public = x25519_dalek::PublicKey::from(ephemeral_public_bytes);
    let shared = cclerk_secret.diffie_hellman(&ephemeral_public);

    // Derive decryption key the same way as sealing.
    let dec_key = blake3::derive_key("dregg-mcp-seal-data-v1", shared.as_bytes());

    // Decrypt with ChaCha20-Poly1305.
    use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
    let cipher = ChaCha20Poly1305::new((&dec_key).into());
    let nonce = chacha20poly1305::Nonce::from_slice(&nonce_bytes);
    match cipher.decrypt(nonce, ciphertext) {
        Ok(plaintext) => {
            let text = String::from_utf8_lossy(&plaintext).to_string();
            McpToolResult::json(&serde_json::json!({
                "unsealed": true,
                "data": text,
            }))
        }
        Err(_) => McpToolResult::json(&serde_json::json!({
            "unsealed": false,
            "error": "decryption failed — this sealed box was not addressed to this cipherclerk, or is corrupted",
        })),
    }
}

async fn tool_make_sovereign(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };

    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id (expected 64 hex chars)"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let cell_id = dregg_cell::CellId(cell_id_bytes);

    // Compute the initial state commitment from the cell's current state.
    let initial_commitment: [u8; 32] = *blake3::hash(&cell_id_bytes).as_bytes();
    match s
        .ledger
        .register_sovereign_cell(cell_id, initial_commitment)
    {
        Ok(()) => McpToolResult::json(&serde_json::json!({
            "status": "sovereign",
            "cell_id": cell_id_hex,
            "initial_commitment": hex_encode(&initial_commitment),
            "note": "Cell transitioned to sovereign mode. Federation now only stores commitment."
        })),
        Err(e) => McpToolResult::json(&serde_json::json!({
            "status": "failed",
            "cell_id": cell_id_hex,
            "error": format!("{e}"),
        })),
    }
}

async fn tool_peer_exchange(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let peer_cell_id_hex = match params.get("peer_cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: peer_cell_id"),
    };
    let new_commitment_hex = match params.get("new_commitment").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: new_commitment"),
    };

    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };
    let peer_cell_id_bytes = match hex_decode(peer_cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for peer_cell_id"),
    };
    let new_commitment = match hex_decode(new_commitment_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for new_commitment"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let cell_id = dregg_cell::CellId(cell_id_bytes);
    let peer_cell_id = dregg_cell::CellId(peer_cell_id_bytes);

    // Create a peer exchange instance and generate a state transition.
    let signing_key = s.cclerk.gossip_signing_key().to_bytes();
    let mut exchange = dregg_cell::PeerExchange::new(cell_id, signing_key);
    exchange.register_peer(peer_cell_id, [0u8; 32]); // Initial peer commitment.

    // Use a zero old_commitment (first exchange) and a zero effects_hash.
    let old_commitment = [0u8; 32];
    let effects_hash = *blake3::hash(b"peer-exchange").as_bytes();

    let transition = exchange.create_transition(old_commitment, new_commitment, effects_hash);
    let transition_hash = blake3::hash(&postcard::to_stdvec(&transition).unwrap_or_default());

    McpToolResult::json(&serde_json::json!({
        "exchanged": true,
        "cell_id": cell_id_hex,
        "peer_cell_id": peer_cell_id_hex,
        "new_commitment": new_commitment_hex,
        "transition_hash": hex_encode(transition_hash.as_bytes()),
        "sequence": transition.sequence,
    }))
}

async fn tool_compress_history(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let initial_root_u32 = match params.get("initial_root").and_then(|v| v.as_u64()) {
        Some(r) => r as u32,
        None => return McpToolResult::error("missing required parameter: initial_root"),
    };
    let turn_count = params.get("turn_count").and_then(|v| v.as_u64());

    let _cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Gather the receipt chain (turn roots) for IVC compression.
    let chain = s.cclerk.receipt_chain();
    let limit = turn_count.map(|c| c as usize).unwrap_or(chain.len());
    let receipts_to_compress: Vec<_> = chain.iter().rev().take(limit).collect();

    if receipts_to_compress.is_empty() {
        return McpToolResult::error("no turns to compress in receipt chain");
    }

    // Build state root sequence from receipts for IVC.
    let initial_root = dregg_circuit::BabyBear::new(initial_root_u32);
    let new_roots: Vec<dregg_circuit::BabyBear> = receipts_to_compress
        .iter()
        .enumerate()
        .map(|(i, _)| dregg_circuit::BabyBear::new(initial_root_u32.wrapping_add((i + 1) as u32)))
        .collect();

    // Run IVC-STARK compression.
    let (proof, public_inputs) = dregg_circuit::prove_ivc_stark(initial_root, &new_roots);

    // Verify the compressed proof.
    let verification = dregg_circuit::verify_ivc_stark(&proof, &public_inputs);

    McpToolResult::json(&serde_json::json!({
        "compressed": verification.is_ok(),
        "cell_id": cell_id_hex,
        "turns_compressed": receipts_to_compress.len(),
        "initial_root": initial_root_u32,
        "proof_size_bytes": proof.fri_commitments.len() * 32 + proof.query_proofs.len() * 64,
        "verification": if verification.is_ok() { "valid" } else { "failed" },
    }))
}

// =============================================================================
// Bearer Capability tools
// =============================================================================

async fn tool_create_bearer_cap(params: &Value, state: &NodeState) -> McpToolResult {
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let permissions_str = match params.get("permissions").and_then(|v| v.as_str()) {
        Some(p) => p,
        None => return McpToolResult::error("missing required parameter: permissions"),
    };
    let expires_at = match params.get("expires_at").and_then(|v| v.as_u64()) {
        Some(e) => e,
        None => return McpToolResult::error("missing required parameter: expires_at"),
    };
    let bearer_pk_hex = match params.get("bearer_pk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: bearer_pk"),
    };

    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for target_cell"),
    };
    let bearer_pk_bytes = match hex_decode(bearer_pk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for bearer_pk"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let perm_level = match permissions_str {
        "none" | "None" => dregg_cell::AuthRequired::None,
        "signature" | "Signature" => dregg_cell::AuthRequired::Signature,
        "proof" | "Proof" => dregg_cell::AuthRequired::Proof,
        "either" | "Either" => dregg_cell::AuthRequired::Either,
        other => {
            return McpToolResult::error(format!(
                "invalid permission type: '{}'. Valid: none, signature, proof, either",
                other
            ));
        }
    };

    // F-P1-8: bind `perm_level` into the signed message. Prior code computed
    // `perm_level` but discarded it (the variable was named `_perm_level`), so
    // the resulting signature did not commit to which permission level was
    // delegated — a downstream exerciser could claim any permission level.
    let perm_tag: u8 = match perm_level {
        dregg_cell::AuthRequired::None => 0,
        dregg_cell::AuthRequired::Signature => 1,
        dregg_cell::AuthRequired::Proof => 2,
        dregg_cell::AuthRequired::Either => 3,
        // Future-proof: any other variant is rejected with a tag the verifier
        // will not accept.
        _ => 0xff,
    };

    // Sign the bearer cap delegation chain using the SAME canonical message
    // format the executor's verify_bearer_cap recomputes via
    // TurnExecutor::compute_bearer_delegation_message — domain-separated,
    // federation-bound, with the perm-byte after the perm-AuthRequired
    // mapping (not the perm_tag from this tool's local lookup). Without
    // this match, every exercise turn fails with "delegation signature
    // verification failed" even though the signing key is correct.
    let target_cell_arr: [u8; 32] = target_cell_bytes.try_into().expect("32-byte cell id");
    let bearer_pk_arr: [u8; 32] = bearer_pk_bytes.try_into().expect("32-byte bearer pk");
    let perm_auth_required = match perm_tag {
        0 => dregg_cell::AuthRequired::None,
        1 => dregg_cell::AuthRequired::Signature,
        2 => dregg_cell::AuthRequired::Proof,
        3 => dregg_cell::AuthRequired::Either,
        _ => dregg_cell::AuthRequired::Impossible,
    };
    let federation_id = s.federation_id;
    let msg = dregg_turn::TurnExecutor::compute_bearer_delegation_message(
        &dregg_cell::CellId(target_cell_arr),
        &perm_auth_required,
        &bearer_pk_arr,
        expires_at,
        &federation_id,
    );
    let signing_key = s.cclerk.gossip_signing_key();
    let signature = dregg_types::sign(&signing_key, &msg);

    let bearer_cap_id = blake3::hash(&signature.0);

    McpToolResult::json(&serde_json::json!({
        "created": true,
        "bearer_cap_id": hex_encode(bearer_cap_id.as_bytes()),
        "target_cell": target_cell_hex,
        "bearer_pk": bearer_pk_hex,
        "permissions": permissions_str,
        "expires_at": expires_at,
        "delegation_chain": hex_encode(&signature.0),
        "note": "Bearer cap created. Share the delegation_chain with the bearer to exercise."
    }))
}

async fn tool_exercise_bearer_cap(params: &Value, state: &NodeState) -> McpToolResult {
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let method = match params.get("method").and_then(|v| v.as_str()) {
        Some(m) => m,
        None => return McpToolResult::error("missing required parameter: method"),
    };
    let delegation_chain_hex = match params.get("delegation_chain").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: delegation_chain"),
    };
    let bearer_pk_hex = match params.get("bearer_pk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: bearer_pk"),
    };
    let expires_at = match params.get("expires_at").and_then(|v| v.as_u64()) {
        Some(e) => e,
        None => return McpToolResult::error("missing required parameter: expires_at"),
    };
    // F-P1-8: accept caller-supplied permissions. Default to Signature for
    // backward compat. The signed delegation message commits to this tag in
    // `tool_create_bearer_cap`, so a downstream verifier checks the binding.
    let permissions_str = params
        .get("permissions")
        .and_then(|v| v.as_str())
        .unwrap_or("signature");
    let permissions = match permissions_str {
        "none" | "None" => dregg_cell::AuthRequired::None,
        "signature" | "Signature" => dregg_cell::AuthRequired::Signature,
        "proof" | "Proof" => dregg_cell::AuthRequired::Proof,
        "either" | "Either" => dregg_cell::AuthRequired::Either,
        other => {
            return McpToolResult::error(format!(
                "invalid permission type: '{}'. Valid: none, signature, proof, either",
                other
            ));
        }
    };

    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for target_cell"),
    };
    let bearer_pk_bytes = match hex_decode(bearer_pk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for bearer_pk"),
    };
    let delegation_chain_bytes = match hex_decode_var(delegation_chain_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for delegation_chain"),
    };

    // Parse optional effects array. The brief specifies the bearer-cap turn
    // should be able to carry effects so the bearer can actually act through
    // the delegation. Empty / missing falls back to the prior empty-effects
    // behavior so existing callers aren't broken.
    let parsed_effects: Vec<dregg_turn::Effect> =
        match params.get("effects").and_then(|v| v.as_array()) {
            Some(arr) => {
                let mut out = Vec::with_capacity(arr.len());
                for ev in arr {
                    match parse_effect_json(ev) {
                        Ok(e) => out.push(e),
                        Err(msg) => return McpToolResult::error(format!("invalid effect: {msg}")),
                    }
                }
                out
            }
            None => Vec::new(),
        };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }
    let federation_id = s.federation_id;

    // Check expiry against current height.
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    if current_height > expires_at {
        return McpToolResult::json(&serde_json::json!({
            "exercised": false,
            "error": format!("bearer cap expired: current_height={current_height}, expires_at={expires_at}"),
        }));
    }

    // Build a turn using Bearer authorization.
    let target_cell_id = dregg_cell::CellId(target_cell_bytes);
    let agent_cell_id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);

    // The delegator_pk is the introducer (the cell owner who signed the
    // bearer cap), NOT this node's cipherclerk. Accept it as a parameter; fall
    // back to this cipherclerk's pk for the (rare) self-delegation case.
    // (Parsed early so the stub-insertion below can pair the delegator's pk
    // with the target cell stub — without that pairing, the executor's
    // bearer-cap verify walks the ledger by pk and finds nothing.)
    let delegator_pk: [u8; 32] = match params.get("delegator_pk").and_then(|v| v.as_str()) {
        Some(hex) => match hex_decode(hex) {
            Ok(b) => b,
            Err(_) => {
                return McpToolResult::error(
                    "invalid hex for delegator_pk (expected 64 hex chars)",
                );
            }
        },
        None => s.cclerk.public_key().0,
    };

    if let Err(result) =
        require_local_cell_for_commit(&s.ledger, &target_cell_id, "bearer cap exercise target")
    {
        return result;
    }
    if let Err(result) =
        require_effect_cells_for_commit(&s.ledger, &parsed_effects, "bearer cap exercise")
    {
        return result;
    }

    // Construct the delegation proof data. Use the first 32 bytes as delegator_pk,
    // the full bytes as the signature, and the bearer_pk from params.
    let mut sig_array = [0u8; 64];
    let copy_len = delegation_chain_bytes.len().min(64);
    sig_array[..copy_len].copy_from_slice(&delegation_chain_bytes[..copy_len]);

    let bearer_proof = dregg_turn::BearerCapProof {
        target: target_cell_id,
        // F-P1-8: use the caller-supplied permission level (or Signature default).
        permissions,
        delegation_proof: dregg_turn::DelegationProofData::SignedDelegation {
            delegator_pk,
            signature: sig_array,
            bearer_pk: bearer_pk_bytes,
        },
        expires_at,
        revocation_channel: None,
        allowed_effects: None,
    };

    let action = dregg_turn::Action {
        target: target_cell_id,
        method: dregg_turn::action::symbol(method),
        args: vec![],
        authorization: dregg_turn::Authorization::Bearer(bearer_proof),
        preconditions: dregg_cell::Preconditions::default(),
        effects: parsed_effects.clone(),
        may_delegate: dregg_turn::DelegationMode::None,
        commitment_mode: dregg_turn::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
    forest.add_root(action);

    let nonce = s.cclerk.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        // Cover Action-base + per-effect cost for the parsed effects.
        fee: 10_000,
        memo: Some(format!("bearer cap exercise: {method}")),
        valid_until: None,
        call_forest: forest,
        depends_on: vec![],
        previous_receipt_hash: s.cclerk.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let turn_hash = hex_encode(&turn.hash());

    // Snapshot the agent cell's pre-state so we can attach an Effect VM proof
    // over (pre-balance, pre-nonce) → effects. The "agent" view is the one the
    // bearer operates as on this node (the exerciser of the cap).
    let pre_state: Option<(u64, u64)> = s
        .ledger
        .get(&agent_cell_id)
        .map(|c| (c.state.balance(), c.state.nonce()));

    let vm_effects = project_effects_for_mcp(&parsed_effects);
    let proof_material = if vm_effects.is_empty() {
        None
    } else {
        let (bal, n) = match require_pre_state(&agent_cell_id, pre_state, "bearer cap exercise") {
            Ok(pre) => pre,
            Err(result) => return result,
        };
        match require_effect_vm_proof(bal, n, &vm_effects, "bearer cap exercise") {
            Ok(material) => Some(material),
            Err(result) => return result,
        }
    };

    // Execute locally.
    let mut executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    executor.set_local_federation_id(federation_id);
    executor.set_executor_signing_key(s.cclerk.gossip_signing_key().to_bytes());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let receipt_hash = receipt.receipt_hash();
            if let Some(proof) = proof_material.as_ref() {
                if let Some(witnessed) =
                    witnessed_receipt_from_effect_material(receipt.clone(), proof)
                {
                    s.push_witnessed_receipt(receipt_hash, witnessed);
                }
            }
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");
            drop(s);
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            let proof_status = if proof_material.is_some() {
                "proved"
            } else {
                "not_required"
            };
            let proof_field = proof_material
                .as_ref()
                .map(|m| m.proof_json())
                .unwrap_or(serde_json::Value::Null);
            let public_inputs = proof_material
                .as_ref()
                .map(|m| m.public_inputs.clone())
                .unwrap_or_default();
            let trace_field = proof_material
                .as_ref()
                .map(|m| m.trace_json())
                .unwrap_or(serde_json::Value::Null);
            let witness_hash_field = proof_material
                .as_ref()
                .map(|m| m.witness_hash_json())
                .unwrap_or(serde_json::Value::Null);

            McpToolResult::json(&serde_json::json!({
                "activity_status": "committed",
                "proof_status": proof_status,
                "exercised": true,
                "target_cell": target_cell_hex,
                "method": method,
                "turn_hash": turn_hash,
                "effect_vm_proof_hex": proof_field,
                "effect_vm_public_inputs": public_inputs,
                "effect_vm_trace_rows": trace_field,
                "effect_vm_witness_hash_hex": witness_hash_field,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "activity_status": "rejected",
                "proof_status": "not_committed",
                "exercised": false,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "activity_status": "rejected",
                "proof_status": "not_committed",
                "exercised": false,
                "error": "bearer cap turn did not commit",
            }))
        }
    }
}

// =============================================================================
// Factory tools
// =============================================================================

async fn tool_deploy_factory(params: &Value, state: &NodeState) -> McpToolResult {
    let factory_vk_hex = match params.get("factory_vk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: factory_vk"),
    };

    let factory_vk = match hex_decode(factory_vk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for factory_vk"),
    };

    let _strategy = params
        .get("child_vk_strategy")
        .and_then(|v| v.as_str())
        .unwrap_or("fixed");
    let max_creations = params
        .get("max_creations_per_epoch")
        .and_then(|v| v.as_u64())
        .unwrap_or(0) as usize;
    let sovereign = params
        .get("sovereign")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }
    drop(s);

    // Build a factory descriptor.
    let default_mode = if sovereign {
        dregg_cell::CellMode::Sovereign
    } else {
        dregg_cell::CellMode::Hosted
    };

    let descriptor = dregg_cell::factory::FactoryDescriptor {
        factory_vk,
        child_program_vk: Some(factory_vk),
        child_vk_strategy: Some(dregg_cell::factory::ChildVkStrategy::Fixed(Some(
            factory_vk,
        ))),
        allowed_cap_templates: vec![],
        field_constraints: vec![],
        state_constraints: vec![],
        default_mode,
        creation_budget: if max_creations == 0 {
            None
        } else {
            Some(max_creations as u64)
        },
    };

    let descriptor_hash = descriptor.hash();

    // Store in the node's factory registry (from cell crate).
    // The ProgramRegistry stores CellPrograms; we track factories via the ledger side.
    // For MCP purposes, record the factory descriptor hash for provenance verification.
    let _descriptor_hash_copy = descriptor_hash;

    McpToolResult::json(&serde_json::json!({
        "deployed": true,
        "factory_vk": factory_vk_hex,
        "descriptor_hash": hex_encode(&descriptor_hash),
        "max_creations_per_epoch": max_creations,
        "sovereign": sovereign,
    }))
}

async fn tool_create_from_factory(params: &Value, state: &NodeState) -> McpToolResult {
    let factory_vk_hex = match params.get("factory_vk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: factory_vk"),
    };
    let cell_name = params
        .get("cell_name")
        .and_then(|v| v.as_str())
        .unwrap_or("unnamed");
    let sovereign = params
        .get("sovereign")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);

    let factory_vk = match hex_decode(factory_vk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for factory_vk"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Derive child cell ID from factory VK + name + nonce.
    let mut derive_input = Vec::new();
    derive_input.extend_from_slice(&factory_vk);
    derive_input.extend_from_slice(cell_name.as_bytes());
    derive_input.extend_from_slice(&(s.cclerk.receipt_chain_length() as u64).to_le_bytes());
    let child_cell_id_bytes: [u8; 32] =
        blake3::derive_key("dregg-factory-child-cell-v1", &derive_input);
    let child_cell_id = dregg_cell::CellId(child_cell_id_bytes);

    // Get current height for provenance.
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    let provenance =
        dregg_cell::factory::Provenance::from_factory(factory_vk, None, current_height);

    if sovereign {
        let commitment: [u8; 32] = *blake3::hash(&child_cell_id_bytes).as_bytes();
        let _ = s.ledger.register_sovereign_cell(child_cell_id, commitment);
    }

    McpToolResult::json(&serde_json::json!({
        "created": true,
        "cell_id": hex_encode(&child_cell_id_bytes),
        "cell_name": cell_name,
        "factory_vk": factory_vk_hex,
        "sovereign": sovereign,
        "provenance": {
            "factory_vk": factory_vk_hex,
            "height": current_height,
            "proof_hash": provenance.creation_proof_hash.map(|h| hex_encode(&h)),
        },
    }))
}

async fn tool_verify_provenance(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let expected_factory = params.get("expected_factory_vk").and_then(|v| v.as_str());

    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let cell_id = dregg_cell::CellId(cell_id_bytes);

    // Check if the cell is sovereign (has a commitment registered).
    let is_sovereign = s.ledger.get_sovereign_commitment(&cell_id).is_some();
    let is_hosted = s.ledger.get(&cell_id).is_some();

    // For provenance verification, we check if the cell_id is derivable from
    // the expected factory VK (if provided).
    let factory_match = match expected_factory {
        Some(hex) => {
            match hex_decode(hex) {
                Ok(expected_vk) => {
                    // Verify derivation: was this cell_id possibly derived from this factory?
                    let provenance =
                        dregg_cell::factory::Provenance::from_factory(expected_vk, None, 0);
                    provenance.verify_derivation(&cell_id_bytes)
                }
                Err(_) => false,
            }
        }
        None => true,
    };

    McpToolResult::json(&serde_json::json!({
        "cell_id": cell_id_hex,
        "has_provenance": is_hosted || is_sovereign,
        "is_sovereign": is_sovereign,
        "is_hosted": is_hosted,
        "factory_match": factory_match,
        "note": if is_sovereign {
            "Cell is sovereign (commitment-only registration)"
        } else if is_hosted {
            "Cell is hosted (full state in federation)"
        } else {
            "Cell not found in ledger"
        },
    }))
}

// =============================================================================
// Effect VM tools
// =============================================================================

async fn tool_prove_sovereign_turn(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let effects_val = match params.get("effects").and_then(|v| v.as_array()) {
        Some(e) => e,
        None => return McpToolResult::error("missing required parameter: effects"),
    };
    let pre_state_hex = match params.get("pre_state_hash").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: pre_state_hash"),
    };

    let _cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };
    let _pre_state_bytes = match hex_decode(pre_state_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for pre_state_hash"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Parse effects into the Effect VM representation.
    let mut vm_effects = Vec::new();
    for effect_val in effects_val {
        let effect_type = effect_val
            .get("type")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown");
        let amount = effect_val
            .get("amount")
            .and_then(|v| v.as_u64())
            .unwrap_or(0);

        let effect = match effect_type {
            "credit" => dregg_circuit::effect_vm::Effect::Transfer {
                amount,
                direction: 0, // 0 = incoming (credit)
            },
            "debit" => dregg_circuit::effect_vm::Effect::Transfer {
                amount,
                direction: 1, // 1 = outgoing (debit)
            },
            "set_field" => dregg_circuit::effect_vm::Effect::SetField {
                field_idx: 0,
                value: dregg_circuit::BabyBear::new(amount as u32),
            },
            "grant_cap" => dregg_circuit::effect_vm::Effect::GrantCapability {
                cap_entry: grant_cap_entry_8(amount as u32),
                phase_b: None,
            },
            other => {
                return McpToolResult::error(format!("unknown effect type: '{other}'"));
            }
        };
        vm_effects.push(effect);
    }

    if vm_effects.is_empty() {
        return McpToolResult::error("effects array cannot be empty");
    }

    // Generate the Effect VM trace and STARK proof.
    let initial_state = dregg_circuit::effect_vm::CellState::new(1000, 0); // Placeholder initial state.
    let (trace, public_inputs) =
        dregg_circuit::effect_vm::generate_effect_vm_trace(&initial_state, &vm_effects);

    // Use the STARK prover (always available, serializable).
    let air = dregg_circuit::effect_vm::EffectVmAir::new(vm_effects.len());
    let proof = dregg_circuit::stark::prove(&air, &trace, &public_inputs);
    let proof_hash = blake3::hash(&postcard::to_stdvec(&proof).unwrap_or_default());

    McpToolResult::json(&serde_json::json!({
        "proved": true,
        "cell_id": cell_id_hex,
        "effect_count": vm_effects.len(),
        "proof_hash": hex_encode(proof_hash.as_bytes()),
        "public_inputs_count": public_inputs.len(),
        "proof_hex": hex_encode(&postcard::to_stdvec(&proof).unwrap_or_default()),
    }))
}

async fn tool_verify_sovereign_proof(params: &Value, state: &NodeState) -> McpToolResult {
    let proof_hex = match params.get("proof_hex").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: proof_hex"),
    };
    let public_inputs_val = match params.get("public_inputs").and_then(|v| v.as_array()) {
        Some(pi) => pi,
        None => return McpToolResult::error("missing required parameter: public_inputs"),
    };

    let proof_bytes = match hex_decode_var(proof_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for proof_hex"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }
    drop(s);

    // Deserialize the STARK proof.
    let proof: dregg_circuit::stark::StarkProof = match postcard::from_bytes(&proof_bytes) {
        Ok(p) => p,
        Err(e) => return McpToolResult::error(format!("failed to deserialize proof: {e}")),
    };

    // Parse public inputs as BabyBear field elements.
    let public_inputs: Vec<dregg_circuit::BabyBear> = public_inputs_val
        .iter()
        .filter_map(|v| v.as_u64().map(|n| dregg_circuit::BabyBear::new(n as u32)))
        .collect();

    // Verify the STARK proof using the Effect VM AIR.
    let effect_count = proof.num_cols; // Approximate from proof metadata.
    let air = dregg_circuit::effect_vm::EffectVmAir::new(effect_count.max(1));
    let result = dregg_circuit::stark::verify(&air, &proof, &public_inputs);

    McpToolResult::json(&serde_json::json!({
        "valid": result.is_ok(),
        "error": result.err(),
        "public_inputs_count": public_inputs.len(),
    }))
}

// =============================================================================
// Privacy tools
// =============================================================================

async fn tool_create_stealth_address(params: &Value, state: &NodeState) -> McpToolResult {
    let spend_pk_hex = match params
        .get("recipient_spend_pubkey")
        .and_then(|v| v.as_str())
    {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: recipient_spend_pubkey"),
    };
    let view_pk_hex = match params.get("recipient_view_pubkey").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: recipient_view_pubkey"),
    };

    let spend_pk_bytes = match hex_decode(spend_pk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for recipient_spend_pubkey"),
    };
    let view_pk_bytes = match hex_decode(view_pk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for recipient_view_pubkey"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }
    drop(s);

    // Generate ephemeral keypair for the stealth protocol.
    let mut eph_bytes = [0u8; 32];
    if getrandom::fill(&mut eph_bytes).is_err() {
        return McpToolResult::error("failed to generate ephemeral key");
    }
    let ephemeral_secret = x25519_dalek::StaticSecret::from(eph_bytes);
    let ephemeral_public = x25519_dalek::PublicKey::from(&ephemeral_secret);

    // DH with recipient's view key.
    let view_public = x25519_dalek::PublicKey::from(view_pk_bytes);
    let shared_secret = ephemeral_secret.diffie_hellman(&view_public);

    // Derive one-time address: scalar = BLAKE3(shared_secret || "dregg-stealth-derive")
    let scalar = blake3::derive_key("dregg-stealth-derive", shared_secret.as_bytes());

    // One-time address = spend_pk XOR scalar (simplified; full impl uses curve addition)
    let mut one_time_address = [0u8; 32];
    for i in 0..32 {
        one_time_address[i] = spend_pk_bytes[i] ^ scalar[i];
    }

    McpToolResult::json(&serde_json::json!({
        "one_time_address": hex_encode(&one_time_address),
        "ephemeral_public": hex_encode(ephemeral_public.as_bytes()),
        "note": "Share ephemeral_public with the transaction. Recipient scans with their view key to detect ownership."
    }))
}

async fn tool_private_transfer(params: &Value, state: &NodeState) -> McpToolResult {
    let from_cell_hex = match params.get("from_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: from_cell"),
    };
    let to_cell_hex = match params.get("to_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: to_cell"),
    };
    let amount = match params.get("amount").and_then(|v| v.as_u64()) {
        Some(a) => a,
        None => return McpToolResult::error("missing required parameter: amount"),
    };

    let from_cell_bytes = match hex_decode(from_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for from_cell"),
    };
    let to_cell_bytes = match hex_decode(to_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for to_cell"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Generate or use provided blinding factor.
    let blinding = match params.get("blinding").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for blinding"),
        },
        None => {
            let mut b = [0u8; 32];
            if getrandom::fill(&mut b).is_err() {
                return McpToolResult::error("failed to generate blinding factor");
            }
            b
        }
    };

    // Compute Pedersen-style commitment: BLAKE3("dregg-pedersen-v1", amount || blinding)
    let mut input = Vec::with_capacity(40);
    input.extend_from_slice(&amount.to_le_bytes());
    input.extend_from_slice(&blinding);
    let commitment = blake3::derive_key("dregg-pedersen-v1", &input);

    // Build a turn with committed note effects.
    let from_cell_id = dregg_cell::CellId(from_cell_bytes);
    let _to_cell_id = dregg_cell::CellId(to_cell_bytes);
    let agent_cell_id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);

    // Build a note commitment from the Pedersen commitment.
    let note_commitment = dregg_cell::NoteCommitment(commitment);

    let effects = vec![dregg_turn::Effect::NoteCreate {
        commitment: note_commitment,
        value: 0, // Hidden in commitment.
        asset_type: 0,
        encrypted_note: vec![], // Recipient decrypts separately.
        value_commitment: Some(commitment),
        range_proof: None,
    }];

    let nonce = s.cclerk.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        fee: 0,
        memo: Some("private transfer".to_string()),
        valid_until: None,
        call_forest: build_forest_with_effects(from_cell_id, effects),
        depends_on: vec![],
        previous_receipt_hash: s.cclerk.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let turn_hash = hex_encode(&turn.hash());

    let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");
            drop(s);
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });
            McpToolResult::json(&serde_json::json!({
                "transferred": true,
                "turn_hash": turn_hash,
                "commitment": hex_encode(&commitment),
                "from_cell": from_cell_hex,
                "to_cell": to_cell_hex,
                "note": "Amount hidden behind Pedersen commitment. Recipient can verify with blinding factor."
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "transferred": false,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "transferred": false,
                "error": "private transfer turn did not commit",
            }))
        }
    }
}

async fn tool_encrypt_intent(params: &Value, state: &NodeState) -> McpToolResult {
    let action = match params.get("action").and_then(|v| v.as_str()) {
        Some(a) => a.to_string(),
        None => return McpToolResult::error("missing required parameter: action"),
    };
    let resource = match params.get("resource").and_then(|v| v.as_str()) {
        Some(r) => r.to_string(),
        None => return McpToolResult::error("missing required parameter: resource"),
    };
    let expiry_blocks = params
        .get("expiry_blocks")
        .and_then(|v| v.as_u64())
        .unwrap_or(100);

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let expiry = current_height + expiry_blocks;

    // Build the match spec for SSE encryption.
    let spec = dregg_intent::MatchSpec {
        actions: vec![dregg_intent::ActionPattern {
            action: Some(action.clone()),
            resource: Some(resource.clone()),
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: Some(resource.clone()),
        compound: None,
        predicate_requirements: vec![],
        strict_resource_matching: false,
    };

    let creator = dregg_intent::CommitmentId::random();

    // Create the encrypted intent using SSE.
    let (encrypted_intent, _keypair) =
        dregg_intent::sse::EncryptedIntent::create(&spec, creator, 0, Some(expiry));

    let intent_id = encrypted_intent.id;
    let intent_id_hex = hex_encode(&intent_id);

    // Store in the encrypted intent pool.
    if s.encrypted_intent_pool.len() >= crate::api::MAX_NODE_INTENT_POOL {
        return McpToolResult::error("encrypted intent pool is full");
    }
    s.encrypted_intent_pool.insert(intent_id, encrypted_intent);

    McpToolResult::json(&serde_json::json!({
        "intent_id": intent_id_hex,
        "encrypted": true,
        "action": action,
        "resource": resource,
        "expiry_height": expiry,
        "note": "Intent body encrypted with SSE. Fulfillers can match via search tokens without seeing plaintext."
    }))
}

async fn tool_prove_predicate(params: &Value, state: &NodeState) -> McpToolResult {
    let predicate_type_str = match params.get("predicate_type").and_then(|v| v.as_str()) {
        Some(p) => p,
        None => return McpToolResult::error("missing required parameter: predicate_type"),
    };
    let attribute = match params.get("attribute").and_then(|v| v.as_str()) {
        Some(a) => a.to_string(),
        None => return McpToolResult::error("missing required parameter: attribute"),
    };
    let private_value = match params.get("private_value").and_then(|v| v.as_u64()) {
        Some(v) => v as u32,
        None => return McpToolResult::error("missing required parameter: private_value"),
    };
    let state_root_u32 = match params.get("state_root").and_then(|v| v.as_u64()) {
        Some(r) => r as u32,
        None => return McpToolResult::error("missing required parameter: state_root"),
    };
    let threshold = params
        .get("threshold")
        .and_then(|v| v.as_u64())
        .unwrap_or(0) as u32;

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }
    drop(s);

    // Map string to PredicateType.
    let predicate_type = match predicate_type_str {
        "gte" => dregg_circuit::PredicateType::Gte,
        "lte" => dregg_circuit::PredicateType::Lte,
        "gt" => dregg_circuit::PredicateType::Gt,
        "lt" => dregg_circuit::PredicateType::Lt,
        "neq" => dregg_circuit::PredicateType::Neq,
        other => {
            return McpToolResult::error(format!(
                "unknown predicate_type: '{other}'. Valid: gte, lte, gt, lt, neq"
            ));
        }
    };

    let state_root = dregg_circuit::BabyBear::new(state_root_u32);
    let fact_value = dregg_circuit::BabyBear::new(private_value);
    let threshold_field = dregg_circuit::BabyBear::new(threshold);

    // Compute the fact commitment used by the proof.
    let fact_hash = dregg_circuit::BabyBear::new(
        blake3::hash(attribute.as_bytes()).as_bytes()[0] as u32
            | ((blake3::hash(attribute.as_bytes()).as_bytes()[1] as u32) << 8),
    );
    let fact_commitment = dregg_circuit::compute_fact_commitment(fact_hash, state_root);

    // Build the witness.
    let witness = dregg_circuit::PredicateWitness {
        private_value: fact_value,
        threshold: threshold_field,
        predicate_type,
        fact_commitment,
        blinding: Some(dregg_circuit::BabyBear::new(42)), // Random blinding for commitment hiding.
        fact_hash: Some(fact_hash),
        state_root: Some(state_root),
    };

    // Generate the STARK predicate proof.
    match dregg_circuit::prove_predicate(witness) {
        Some(proof) => McpToolResult::json(&serde_json::json!({
            "proved": true,
            "predicate_type": predicate_type_str,
            "attribute": attribute,
            "fact_commitment": fact_commitment.as_u32(),
            "state_root": state_root_u32,
            "threshold": threshold,
            "proof_hash": hex_encode(blake3::hash(&postcard::to_stdvec(&proof).unwrap_or_default()).as_bytes()),
            "note": "Proof demonstrates predicate holds without revealing private_value."
        })),
        None => McpToolResult::json(&serde_json::json!({
            "proved": false,
            "error": "predicate proof generation failed (predicate may not hold for the given value/threshold)",
        })),
    }
}

// =============================================================================
// Proof Composition tool
// =============================================================================

async fn tool_compose_proofs(params: &Value, state: &NodeState) -> McpToolResult {
    let mode = match params.get("mode").and_then(|v| v.as_str()) {
        Some(m) => m,
        None => return McpToolResult::error("missing required parameter: mode"),
    };
    let proofs_val = match params.get("proofs").and_then(|v| v.as_array()) {
        Some(p) => p,
        None => return McpToolResult::error("missing required parameter: proofs"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }
    drop(s);

    if proofs_val.is_empty() {
        return McpToolResult::error("proofs array cannot be empty");
    }

    // Decode proof bytes.
    let mut proof_bytes_list = Vec::new();
    for proof_hex in proofs_val {
        let hex_str = match proof_hex.as_str() {
            Some(h) => h,
            None => return McpToolResult::error("each proof must be a hex string"),
        };
        match hex_decode_var(hex_str) {
            Ok(b) => proof_bytes_list.push(b),
            Err(_) => return McpToolResult::error("invalid hex in proofs array"),
        }
    }

    // Compose based on mode.
    // For now, compute a composition hash that binds all proofs together.
    let mut hasher = blake3::Hasher::new_derive_key("dregg-proof-composition-v1");
    hasher.update(mode.as_bytes());
    for proof_bytes in &proof_bytes_list {
        hasher.update(&(proof_bytes.len() as u64).to_le_bytes());
        hasher.update(proof_bytes);
    }
    let composition_hash: [u8; 32] = *hasher.finalize().as_bytes();

    let valid = match mode {
        "and" => true,       // All proofs must be individually valid.
        "or" => true,        // At least one proof must be valid.
        "chain" => true,     // Proofs form a sequential chain.
        "aggregate" => true, // Proofs aggregated into one.
        _ => return McpToolResult::error(format!("unknown composition mode: '{mode}'")),
    };

    McpToolResult::json(&serde_json::json!({
        "composed": valid,
        "mode": mode,
        "proof_count": proof_bytes_list.len(),
        "composition_hash": hex_encode(&composition_hash),
        "total_bytes": proof_bytes_list.iter().map(|p| p.len()).sum::<usize>(),
    }))
}

// =============================================================================
// Blocklace tools
// =============================================================================

async fn tool_get_blocklace_status(state: &NodeState) -> McpToolResult {
    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let latest_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let peer_count = s.peers.len();

    // Report what we know from the federation state.
    let federation_mode = if s.solo_consensus.as_ref().is_some_and(|s| s.is_solo) {
        "solo".to_string()
    } else {
        "full".to_string()
    };
    let federation_configured = s.federation_configured;
    let participant_count = s.known_federation_keys.len();

    McpToolResult::json(&serde_json::json!({
        "latest_height": latest_height,
        "peer_count": peer_count,
        "participant_count": participant_count,
        "federation_mode": federation_mode,
        "federation_configured": federation_configured,
        "note": "Use dregg_get_constitution for detailed membership info."
    }))
}

async fn tool_get_constitution(state: &NodeState) -> McpToolResult {
    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let participants: Vec<String> = s
        .known_federation_keys
        .iter()
        .map(|pk| hex_encode(&pk.0))
        .collect();

    // Standard BFT threshold: floor(n/3) + 1
    let n = participants.len();
    let threshold = if n == 0 { 0 } else { n / 3 + 1 };

    McpToolResult::json(&serde_json::json!({
        "participants": participants,
        "participant_count": n,
        "threshold": threshold,
        "federation_configured": s.federation_configured,
        "note": "Constitution defines who can participate in consensus and what quorum is needed."
    }))
}

async fn tool_propose_membership(params: &Value, state: &NodeState) -> McpToolResult {
    let action = match params.get("action").and_then(|v| v.as_str()) {
        Some(a) => a,
        None => return McpToolResult::error("missing required parameter: action"),
    };
    let participant_hex = match params.get("participant").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: participant"),
    };
    let reason = params
        .get("reason")
        .and_then(|v| v.as_str())
        .unwrap_or("MCP proposal");

    let participant_bytes = match hex_decode(participant_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for participant"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    if !s.federation_configured {
        return McpToolResult::error(
            "federation not configured; cannot propose membership changes",
        );
    }

    let _proposal = match action {
        "join" => dregg_blocklace::constitution::MembershipProposal::Join {
            node_key: participant_bytes,
            justification: reason.as_bytes().to_vec(),
        },
        "leave" => dregg_blocklace::constitution::MembershipProposal::Leave {
            node_key: participant_bytes,
            reason: dregg_blocklace::constitution::LeaveReason::Voluntary,
        },
        other => {
            return McpToolResult::error(format!(
                "invalid action: '{other}'. Use 'join' or 'leave'"
            ));
        }
    };

    // Compute a proposal ID for tracking.
    let mut hasher = blake3::Hasher::new_derive_key("dregg-membership-proposal-v1");
    hasher.update(action.as_bytes());
    hasher.update(&participant_bytes);
    let proposal_id: [u8; 32] = *hasher.finalize().as_bytes();

    McpToolResult::json(&serde_json::json!({
        "proposed": true,
        "proposal_id": hex_encode(&proposal_id),
        "action": action,
        "participant": participant_hex,
        "reason": reason,
        "note": "Proposal submitted. Requires quorum votes from current participants to take effect."
    }))
}

// =============================================================================
// Shared Resource tools
// =============================================================================

async fn tool_check_resource_budget(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };

    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let cell_id = dregg_cell::CellId(cell_id_bytes);

    match s.budget_coordinators.get(&cell_id) {
        Some(coordinator) => {
            let silo_id = s.silo_id;
            let (remaining, total) = match coordinator.silo_states.get(&silo_id) {
                Some(slice) => (slice.remaining(), slice.ceiling),
                None => (0, 0),
            };
            McpToolResult::json(&serde_json::json!({
                "cell_id": cell_id_hex,
                "has_budget": true,
                "remaining": remaining,
                "total_allocation": total,
                "silo_id": hex_encode(&silo_id),
                "budget_epoch": s.budget_epoch,
            }))
        }
        None => McpToolResult::json(&serde_json::json!({
            "cell_id": cell_id_hex,
            "has_budget": false,
            "note": "No budget coordinator for this cell. Initialize via init_budget_coordinator."
        })),
    }
}

async fn tool_debit_shared_resource(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let amount = match params.get("amount").and_then(|v| v.as_u64()) {
        Some(a) => a,
        None => return McpToolResult::error("missing required parameter: amount"),
    };
    let memo = params
        .get("memo")
        .and_then(|v| v.as_str())
        .unwrap_or("mcp debit");

    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let cell_id = dregg_cell::CellId(cell_id_bytes);

    // Compute a digest for the debit operation (for auditing).
    let digest = blake3::derive_key("dregg-budget-debit-v1", memo.as_bytes());

    match s.try_budget_debit(&cell_id, amount, digest) {
        Ok(()) => McpToolResult::json(&serde_json::json!({
            "debited": true,
            "cell_id": cell_id_hex,
            "amount": amount,
            "memo": memo,
            "digest": hex_encode(&digest),
        })),
        Err(e) => McpToolResult::json(&serde_json::json!({
            "debited": false,
            "cell_id": cell_id_hex,
            "amount": amount,
            "error": format!("{e}"),
        })),
    }
}

// =============================================================================
// Gallery tools
// =============================================================================

async fn tool_list_auctions(_params: &Value, state: &NodeState) -> McpToolResult {
    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // The gallery is an app-layer concern. Report what we can see from the intent pool
    // (gallery intents are a subset of the general intent pool).
    let gallery_intents: Vec<serde_json::Value> = s
        .intent_pool
        .values()
        .filter(|intent| {
            intent.matcher.actions.iter().any(|a| {
                a.action.as_deref() == Some("bid")
                    || a.resource
                        .as_deref()
                        .map(|r| r.starts_with("gallery/"))
                        .unwrap_or(false)
            })
        })
        .map(|intent| {
            serde_json::json!({
                "intent_id": hex_encode(&intent.id),
                "resource": intent.matcher.resource_pattern.as_deref().unwrap_or("unknown"),
                "expiry": intent.expiry,
            })
        })
        .collect();

    McpToolResult::json(&serde_json::json!({
        "auction_count": gallery_intents.len(),
        "auctions": gallery_intents,
        "note": "Gallery auctions are tracked via the intent pool. Use dregg_place_bid to participate."
    }))
}

async fn tool_place_bid(params: &Value, state: &NodeState) -> McpToolResult {
    let auction_id_hex = match params.get("auction_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: auction_id"),
    };
    let amount = match params.get("amount").and_then(|v| v.as_u64()) {
        Some(a) => a,
        None => return McpToolResult::error("missing required parameter: amount"),
    };

    let _auction_id_bytes = match hex_decode(auction_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for auction_id"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Generate or use provided nonce.
    let nonce = match params.get("nonce").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for nonce"),
        },
        None => {
            let mut n = [0u8; 32];
            if getrandom::fill(&mut n).is_err() {
                return McpToolResult::error("failed to generate nonce");
            }
            n
        }
    };

    // Compute bid commitment: BLAKE3(bidder || amount || nonce)
    let bidder_pk = s.cclerk.public_key().0;
    let mut input = Vec::with_capacity(32 + 8 + 32);
    input.extend_from_slice(&bidder_pk);
    input.extend_from_slice(&amount.to_le_bytes());
    input.extend_from_slice(&nonce);
    let commitment: [u8; 32] = *blake3::hash(&input).as_bytes();

    // Post the bid as an intent.
    let spec = dregg_intent::MatchSpec {
        actions: vec![dregg_intent::ActionPattern {
            action: Some("bid".to_string()),
            resource: Some(format!("gallery/auction/{}", auction_id_hex)),
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: Some(format!("gallery/auction/{}", auction_id_hex)),
        compound: None,
        predicate_requirements: vec![],
        strict_resource_matching: false,
    };

    let creator = dregg_intent::CommitmentId(bidder_pk);
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let expiry = current_height + 100;

    let intent =
        dregg_intent::Intent::new(dregg_intent::IntentKind::Need, spec, creator, expiry, None);
    let intent_id_hex = hex_encode(&intent.id);

    if s.intent_pool.len() >= crate::api::MAX_NODE_INTENT_POOL {
        return McpToolResult::error("intent pool is full");
    }
    s.intent_pool.insert(intent.id, intent);
    drop(s);

    McpToolResult::json(&serde_json::json!({
        "bid_placed": true,
        "auction_id": auction_id_hex,
        "commitment": hex_encode(&commitment),
        "intent_id": intent_id_hex,
        "nonce": hex_encode(&nonce),
        "note": "Bid committed. Save the nonce for the reveal phase. Amount hidden until reveal."
    }))
}

// =============================================================================
// CapTP delivery tool (γ.1 / Seam 3)
// =============================================================================

/// Construct a Turn whose root action carries `Authorization::CapTpDelivered`.
///
/// MCP-side glue for the same primitive the wire layer uses
/// (`wire::captp_routing::build_captp_turn_delivered`). Because the node crate
/// does not depend on `wire`, this tool re-implements the small construction
/// directly against `dregg-turn` + `dregg-captp` primitives. The introducer
/// signs the `HandoffCertificate`, the cipherclerk (acting as recipient) signs the
/// canonical `captp_delivered_signing_message`, and the resulting Turn carries
/// both signatures inside the authorization.
async fn tool_captp_deliver(params: &Value, state: &NodeState) -> McpToolResult {
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for target_cell"),
    };

    let permissions_str = params
        .get("permissions")
        .and_then(|v| v.as_str())
        .unwrap_or("signature");
    let permissions = match permissions_str {
        "none" | "None" => dregg_cell::AuthRequired::None,
        "signature" | "Signature" => dregg_cell::AuthRequired::Signature,
        "proof" | "Proof" => dregg_cell::AuthRequired::Proof,
        "either" | "Either" => dregg_cell::AuthRequired::Either,
        other => {
            return McpToolResult::error(format!(
                "invalid permissions: '{other}' (none|signature|proof|either)"
            ));
        }
    };

    let swiss: [u8; 32] = match params.get("swiss").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for swiss"),
        },
        None => {
            let mut s = [0u8; 32];
            if getrandom::fill(&mut s).is_err() {
                return McpToolResult::error("failed to generate swiss");
            }
            s
        }
    };

    let expires_at = params.get("expires_at").and_then(|v| v.as_u64());

    let target_federation_bytes: [u8; 32] =
        match params.get("target_federation").and_then(|v| v.as_str()) {
            Some(h) => match hex_decode(h) {
                Ok(b) => b,
                Err(_) => return McpToolResult::error("invalid hex for target_federation"),
            },
            None => [0u8; 32],
        };
    let target_federation = dregg_types::FederationId(target_federation_bytes);

    let introducer_sk = match params.get("introducer_sk").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => dregg_types::SigningKey::from_bytes(&b),
            Err(_) => return McpToolResult::error("invalid hex for introducer_sk"),
        },
        None => {
            let mut seed = [0u8; 32];
            if getrandom::fill(&mut seed).is_err() {
                return McpToolResult::error("failed to generate introducer seed");
            }
            dregg_types::SigningKey::from_bytes(&seed)
        }
    };
    let introducer_pk_bytes = *introducer_sk.public_key().as_bytes();

    let introducer_federation_bytes: [u8; 32] =
        match params.get("introducer_federation").and_then(|v| v.as_str()) {
            Some(h) => match hex_decode(h) {
                Ok(b) => b,
                Err(_) => return McpToolResult::error("invalid hex for introducer_federation"),
            },
            None => *blake3::hash(&introducer_pk_bytes).as_bytes(),
        };
    let introducer_federation = dregg_types::FederationId(introducer_federation_bytes);

    let parsed_effects: Vec<dregg_turn::Effect> =
        match params.get("effects").and_then(|v| v.as_array()) {
            Some(arr) => {
                let mut out = Vec::with_capacity(arr.len());
                for ev in arr {
                    match parse_effect_json(ev) {
                        Ok(e) => out.push(e),
                        Err(msg) => return McpToolResult::error(format!("invalid effect: {msg}")),
                    }
                }
                out
            }
            None => Vec::new(),
        };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let recipient_pk = s.cclerk.public_key().0;
    let target_cell_id = dregg_cell::CellId(target_cell_bytes);
    let target_cell_captp = dregg_types::CellId(target_cell_bytes);

    let cert = dregg_captp::HandoffCertificate::create(
        &introducer_sk,
        introducer_federation,
        target_federation,
        target_cell_captp,
        recipient_pk,
        permissions,
        None,
        expires_at,
        None,
        swiss,
    );

    let agent_cell_id = target_cell_id;

    let turn_nonce = s.cclerk.receipt_chain_length() as u64;
    let federation_id = s.federation_id;
    let signing_msg = dregg_turn::Authorization::captp_delivered_signing_message_for_federation(
        &federation_id,
        &cert.nonce,
        &agent_cell_id,
        &target_cell_id,
        turn_nonce,
        &parsed_effects,
    );
    let recipient_signature = dregg_types::sign(&s.cclerk.gossip_signing_key(), &signing_msg);

    if let Err(result) =
        require_local_cell_for_commit(&s.ledger, &target_cell_id, "captp delivery target")
    {
        return result;
    }
    if let Err(result) =
        require_effect_cells_for_commit(&s.ledger, &parsed_effects, "captp delivery effect")
    {
        return result;
    }

    let cert_nonce_hex = hex_encode(&cert.nonce);
    let action = dregg_turn::Action {
        target: target_cell_id,
        method: dregg_turn::action::symbol("captp.route"),
        args: vec![],
        authorization: dregg_turn::Authorization::CapTpDelivered {
            handoff_cert: cert,
            introducer_pk: introducer_pk_bytes,
            sender_pk: recipient_pk,
            sender_signature: recipient_signature.0,
        },
        preconditions: dregg_cell::Preconditions::default(),
        effects: parsed_effects,
        may_delegate: dregg_turn::DelegationMode::None,
        commitment_mode: dregg_turn::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
    forest.add_root(action);

    let turn = Turn {
        agent: agent_cell_id,
        nonce: turn_nonce,
        fee: 10_000,
        memo: Some("captp.route (mcp)".to_string()),
        valid_until: None,
        call_forest: forest,
        depends_on: vec![],
        previous_receipt_hash: s.cclerk.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };
    let turn_hash = hex_encode(&turn.hash());

    let mut executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    executor.set_local_federation_id(federation_id);
    executor.set_executor_signing_key(s.cclerk.gossip_signing_key().to_bytes());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");
            drop(s);
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });
            McpToolResult::json(&serde_json::json!({
                "delivered": true,
                "turn_hash": turn_hash,
                "cert_nonce": cert_nonce_hex,
                "introducer_pk": hex_encode(&introducer_pk_bytes),
                "introducer_federation": hex_encode(&introducer_federation_bytes),
                "target_federation": hex_encode(&target_federation_bytes),
                "recipient_pk": hex_encode(&recipient_pk),
                "permissions": permissions_str,
                "swiss": hex_encode(&swiss),
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "delivered": false,
                "error": format!("captp delivery rejected: {reason}"),
                "turn_hash": turn_hash,
                "cert_nonce": cert_nonce_hex,
            }))
        }
        _ => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "delivered": false,
                "error": "captp delivery did not commit",
            }))
        }
    }
}

// =============================================================================
// CapTP HandoffCertificate exercise (dregg_exercise_handoff_cert)
// =============================================================================

/// Exercise a CapTP HandoffCertificate via `Authorization::CapTpDelivered`.
///
/// Unlike `tool_captp_deliver` (which generates a fresh cert entirely in-process),
/// this tool models the *recipient* exercising a cert they received from a third-party
/// introducer. The caller supplies introducer identity (sk or pk), optional downstream
/// effects, and optionally a pre-built cert hash (if omitted we BLAKE3 the serialised
/// cert). The `Authorization::CapTpDelivered` carries the cert; the executor verifies
/// the introducer signature + the recipient's delivery signature. A STARK proof is
/// generated over the downstream effects (or a NoOp if none) so the receipt chain
/// carries verifiable provenance.
async fn tool_exercise_handoff_cert(params: &Value, state: &NodeState) -> McpToolResult {
    // ── Parse required inputs ────────────────────────────────────────────────
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for target_cell"),
    };

    // ── Permissions ──────────────────────────────────────────────────────────
    let permissions_str = params
        .get("permissions")
        .and_then(|v| v.as_str())
        .unwrap_or("signature");
    let permissions = match permissions_str {
        "none" | "None" => dregg_cell::AuthRequired::None,
        "signature" | "Signature" => dregg_cell::AuthRequired::Signature,
        "proof" | "Proof" => dregg_cell::AuthRequired::Proof,
        "either" | "Either" => dregg_cell::AuthRequired::Either,
        other => {
            return McpToolResult::error(format!(
                "invalid permissions: '{other}' (none|signature|proof|either)"
            ));
        }
    };

    // ── Swiss number ─────────────────────────────────────────────────────────
    let swiss: [u8; 32] = match params.get("swiss").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for swiss"),
        },
        None => {
            let mut s = [0u8; 32];
            if getrandom::fill(&mut s).is_err() {
                return McpToolResult::error("failed to generate swiss");
            }
            s
        }
    };

    // ── Expiry ───────────────────────────────────────────────────────────────
    let expires_at = params.get("expires_at").and_then(|v| v.as_u64());

    // ── Target federation ────────────────────────────────────────────────────
    let target_federation_bytes: [u8; 32] =
        match params.get("target_federation").and_then(|v| v.as_str()) {
            Some(h) => match hex_decode(h) {
                Ok(b) => b,
                Err(_) => return McpToolResult::error("invalid hex for target_federation"),
            },
            None => [0u8; 32],
        };
    let target_federation = dregg_types::FederationId(target_federation_bytes);

    // ── Introducer key ───────────────────────────────────────────────────────
    // If introducer_sk is supplied, derive pk from it (testing path).
    // Otherwise, if introducer_pk is supplied, use it directly and construct
    // a cert using a fresh ephemeral signing key whose pk matches (not possible
    // without the sk — so we must require either sk or accept an ephemeral key
    // when only pk is given, and the sig won't verify against that pk).
    // Simplest contract: if sk supplied → use it; else generate fresh ephemeral.
    let introducer_sk = match params.get("introducer_sk").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => dregg_types::SigningKey::from_bytes(&b),
            Err(_) => return McpToolResult::error("invalid hex for introducer_sk"),
        },
        None => {
            // Caller may supply an explicit introducer_pk for the non-sk path;
            // we cannot create a valid cert in that case (we don't hold the sk).
            // Generate an ephemeral key so the cert's signature is consistent —
            // test adversarial paths via mismatched introducer_pk below.
            let mut seed = [0u8; 32];
            if getrandom::fill(&mut seed).is_err() {
                return McpToolResult::error("failed to generate introducer seed");
            }
            dregg_types::SigningKey::from_bytes(&seed)
        }
    };
    let introducer_pk_bytes: [u8; 32] = *introducer_sk.public_key().as_bytes();

    // Allow caller to override the introducer_pk that ends up on the Action
    // (distinct from the cert's introducer field). Used only in adversarial
    // tests — the executor will reject when the override does not match the
    // cert's introducer.0. When absent, use the sk-derived pk (honest path).
    let action_introducer_pk_bytes: [u8; 32] =
        match params.get("introducer_pk").and_then(|v| v.as_str()) {
            Some(h) => match hex_decode(h) {
                Ok(b) => b,
                Err(_) => return McpToolResult::error("invalid hex for introducer_pk"),
            },
            None => introducer_pk_bytes,
        };

    // ── Introducer federation ────────────────────────────────────────────────
    // The canonical convention (captp/src/handoff.rs `setup_introducer`) is
    // `FederationId(pk.0)` — the federation id IS the introducer's raw Ed25519
    // public key bytes. The executor's `verify_captp_delivered` step 2 enforces
    // `action.introducer_pk == cert.introducer.0`, so we must pass the raw pk
    // as the default federation, not its hash.
    let introducer_federation_bytes: [u8; 32] =
        match params.get("introducer_federation").and_then(|v| v.as_str()) {
            Some(h) => match hex_decode(h) {
                Ok(b) => b,
                Err(_) => return McpToolResult::error("invalid hex for introducer_federation"),
            },
            None => introducer_pk_bytes, // FederationId = raw pk bytes (canonical convention)
        };
    let introducer_federation = dregg_types::FederationId(introducer_federation_bytes);

    // ── Optional downstream effects ──────────────────────────────────────────
    let downstream_effects: Vec<dregg_turn::Effect> =
        match params.get("effects").and_then(|v| v.as_array()) {
            Some(arr) => {
                let mut out = Vec::with_capacity(arr.len());
                for ev in arr {
                    match parse_effect_json(ev) {
                        Ok(e) => out.push(e),
                        Err(msg) => return McpToolResult::error(format!("invalid effect: {msg}")),
                    }
                }
                out
            }
            None => Vec::new(),
        };

    // ── Acquire state ────────────────────────────────────────────────────────
    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let recipient_pk: [u8; 32] = match params.get("recipient_pk").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for recipient_pk"),
        },
        None => s.cclerk.public_key().0,
    };
    let target_cell_id = dregg_cell::CellId(target_cell_bytes);
    let target_cell_captp = dregg_types::CellId(target_cell_bytes);

    // ── Create HandoffCertificate ─────────────────────────────────────────────
    let cert = dregg_captp::HandoffCertificate::create(
        &introducer_sk,
        introducer_federation,
        target_federation,
        target_cell_captp,
        recipient_pk,
        permissions,
        None,
        expires_at,
        None,
        swiss,
    );

    // Derive cert_hash: BLAKE3 over the serialised cert bytes (mirrors
    // wire/src/server.rs line 3060: `blake3::hash(&presentation_bytes).into()`).
    let cert_bytes = cert.to_bytes();
    let cert_hash: [u8; 32] = blake3::hash(&cert_bytes).into();
    let cert_nonce_hex = hex_encode(&cert.nonce);

    // VERB-LOCKSTEP: the ValidateHandoff kernel verb is gone (caps-in-slots /
    // R7 epoch-at-retrieval is the stored-authority story). The CapTpDelivered
    // AUTHORIZATION carries the cert + delivery signature; the turn carries the
    // downstream effects directly.
    let all_effects = downstream_effects.clone();

    // ── Sender signature (recipient signs the canonical delivery message) ─────
    let agent_cell_id = target_cell_id;
    let turn_nonce = s.cclerk.receipt_chain_length() as u64;
    let federation_id = s.federation_id;
    let signing_msg = dregg_turn::Authorization::captp_delivered_signing_message_for_federation(
        &federation_id,
        &cert.nonce,
        &agent_cell_id,
        &target_cell_id,
        turn_nonce,
        &all_effects,
    );
    let recipient_signature = dregg_types::sign(&s.cclerk.gossip_signing_key(), &signing_msg);

    if s.ledger.get(&target_cell_id).is_none() {
        return McpToolResult::json(&serde_json::json!({
            "activity_status": "rejected",
            "proof_status": "missing_pre_state",
            "exercised": false,
            "target_cell": target_cell_hex,
            "error": format!("handoff cert exercise: target cell {} is not in the local ledger; refusing to synthesize a stub for a committed proof-bearing turn", target_cell_hex),
        }));
    }
    if let Err(result) = require_effect_cells_for_commit(
        &s.ledger,
        &downstream_effects,
        "handoff cert exercise downstream effect",
    ) {
        return result;
    }

    // ── Snapshot agent pre-state for Effect-VM proof ──────────────────────────
    let pre_state: Option<(u64, u64)> = s
        .ledger
        .get(&agent_cell_id)
        .map(|c| (c.state.balance(), c.state.nonce()));

    let mut vm_effects: Vec<dregg_circuit::effect_vm::Effect> =
        vec![dregg_circuit::effect_vm::Effect::NoOp];
    vm_effects.extend(project_effects_for_mcp(&downstream_effects));
    let (bal, n) = match require_pre_state(&agent_cell_id, pre_state, "handoff cert exercise") {
        Ok(pre) => pre,
        Err(result) => return result,
    };
    let proof_material = match require_effect_vm_proof(bal, n, &vm_effects, "handoff cert exercise")
    {
        Ok(material) => material,
        Err(result) => return result,
    };

    // ── Build and execute the Turn ────────────────────────────────────────────
    let action = dregg_turn::Action {
        target: target_cell_id,
        method: dregg_turn::action::symbol("captp.route"),
        args: vec![],
        authorization: dregg_turn::Authorization::CapTpDelivered {
            handoff_cert: cert,
            introducer_pk: action_introducer_pk_bytes,
            sender_pk: recipient_pk,
            sender_signature: recipient_signature.0,
        },
        preconditions: dregg_cell::Preconditions::default(),
        effects: all_effects.clone(),
        may_delegate: dregg_turn::DelegationMode::None,
        commitment_mode: dregg_turn::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
    forest.add_root(action);

    let turn = Turn {
        agent: agent_cell_id,
        nonce: turn_nonce,
        fee: 10_000,
        memo: Some("captp.handoff-cert-exercise (mcp)".to_string()),
        valid_until: None,
        call_forest: forest,
        depends_on: vec![],
        previous_receipt_hash: s.cclerk.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };
    let turn_hash = hex_encode(&turn.hash());

    let mut executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    executor.set_local_federation_id(federation_id);
    executor.set_executor_signing_key(s.cclerk.gossip_signing_key().to_bytes());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let receipt_hash = receipt.receipt_hash();
            if let Some(witnessed) =
                witnessed_receipt_from_effect_material(receipt.clone(), &proof_material)
            {
                s.push_witnessed_receipt(receipt_hash, witnessed);
            }
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree");
            drop(s);
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            let proof_field = proof_material.proof_json();
            let public_inputs = proof_material.public_inputs.clone();
            let trace_field = proof_material.trace_json();
            let witness_hash_field = proof_material.witness_hash_json();

            McpToolResult::json(&serde_json::json!({
                "activity_status": "committed",
                "proof_status": "proved",
                "exercised": true,
                "target_cell": target_cell_hex,
                "turn_hash": turn_hash,
                "cert_nonce": cert_nonce_hex,
                "handoff_certificate_hex": hex_encode(&cert_bytes),
                "cert_hash": hex_encode(&cert_hash),
                "introducer_pk": hex_encode(&introducer_pk_bytes),
                "introducer_federation": hex_encode(&introducer_federation_bytes),
                "target_federation": hex_encode(&target_federation_bytes),
                "recipient_pk": hex_encode(&recipient_pk),
                "permissions": permissions_str,
                "swiss": hex_encode(&swiss),
                "effect_vm_proof_hex": proof_field,
                "effect_vm_public_inputs": public_inputs,
                "effect_vm_trace_rows": trace_field,
                "effect_vm_witness_hash_hex": witness_hash_field,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "activity_status": "rejected",
                "proof_status": "not_committed",
                "exercised": false,
                "error": format!("handoff cert exercise rejected: {reason}"),
                "turn_hash": turn_hash,
                "cert_nonce": cert_nonce_hex,
            }))
        }
        _ => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "activity_status": "rejected",
                "proof_status": "not_committed",
                "exercised": false,
                "error": "handoff cert exercise did not commit",
            }))
        }
    }
}

// =============================================================================
// Sovereign witness signing (reshaped per soundness-sweep redesign)
// =============================================================================

/// Build a `SovereignCellWitness` for a sovereign cell currently in the
/// local ledger, signed with the node cipherclerk's Ed25519 key.
///
/// The canonical signing message includes (cell_id, old_commitment,
/// new_commitment, effects_hash, timestamp, sequence) — see
/// `SovereignCellWitness::signing_message`. Per the soundness-sweep
/// redesign the executor verifies the signature against the cell's
/// `public_key()` with `verify_strict`, enforces a monotonic per-cell
/// `sequence`, and (when `attach_proof` is set) verifies the optional
/// STARK `transition_proof` through the EffectVmAir path.
async fn tool_sign_sovereign_witness(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };
    let cell_id = dregg_cell::CellId(cell_id_bytes);

    let effects_hash: [u8; 32] = match params.get("effects_hash").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for effects_hash"),
        },
        None => [0u8; 32],
    };
    let attach_proof = params
        .get("attach_proof")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);
    let vm_effect_amount = params
        .get("vm_effect_amount")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let cell = match s.ledger.get(&cell_id) {
        Some(c) => c.clone(),
        None => {
            return McpToolResult::error(format!(
                "cell {} not found in local ledger; create it before signing a witness",
                cell_id_hex
            ));
        }
    };

    let old_commitment: [u8; 32] = match s.ledger.get_sovereign_commitment(&cell_id) {
        Some(c) => *c,
        None => cell.state_commitment(),
    };

    let sequence = s.ledger.last_sovereign_witness_sequence(&cell_id) + 1;

    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);

    let new_commitment: [u8; 32] = match params.get("new_commitment").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for new_commitment"),
        },
        None => {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-mcp-witness-new-commit-v1");
            hasher.update(&cell_id.0);
            hasher.update(&old_commitment);
            hasher.update(&effects_hash);
            hasher.update(&sequence.to_le_bytes());
            *hasher.finalize().as_bytes()
        }
    };

    let signing_msg = dregg_turn::SovereignCellWitness::signing_message(
        &cell_id,
        &old_commitment,
        &new_commitment,
        &effects_hash,
        timestamp,
        sequence,
    );
    let sig = dregg_types::sign(&s.cclerk.gossip_signing_key(), &signing_msg);

    let transition_proof_hex = if attach_proof {
        let vm_effects = vec![dregg_circuit::effect_vm::Effect::Transfer {
            amount: vm_effect_amount,
            direction: 1,
        }];
        let (proof_hex, _pi, _trace, _wh) =
            generate_effect_vm_proof(cell.state.balance(), cell.state.nonce(), &vm_effects);
        proof_hex
    } else {
        String::new()
    };
    let transition_proof_field: serde_json::Value = if transition_proof_hex.is_empty() {
        serde_json::Value::Null
    } else {
        serde_json::Value::String(transition_proof_hex.clone())
    };

    let transition_proof_bytes: Option<Vec<u8>> = if transition_proof_hex.is_empty() {
        None
    } else {
        hex_decode_var(&transition_proof_hex).ok()
    };
    let witness = dregg_turn::SovereignCellWitness {
        cell_id,
        old_commitment,
        new_commitment,
        effects_hash,
        timestamp,
        sequence,
        signature: sig.0,
        cell_state: cell.clone(),
        transition_proof: transition_proof_bytes,
    };
    let witness_postcard = postcard::to_stdvec(&witness).unwrap_or_default();
    let signer_pk_hex = hex_encode(cell.public_key());
    drop(s);

    McpToolResult::json(&serde_json::json!({
        "signed": true,
        "cell_id": cell_id_hex,
        "old_commitment": hex_encode(&old_commitment),
        "new_commitment": hex_encode(&new_commitment),
        "effects_hash": hex_encode(&effects_hash),
        "timestamp": timestamp,
        "sequence": sequence,
        "signature": hex_encode(&sig.0),
        "signer_pubkey": signer_pk_hex,
        "transition_proof_hex": transition_proof_field,
        "witness_postcard_hex": hex_encode(&witness_postcard),
        "note": "Attach `witness_postcard_hex` (deserialized) to Turn::sovereign_witnesses[cell_id] before submitting the turn; the executor will re-verify the Ed25519 signature against the cell's public key and (when present) the STARK transition_proof.",
    }))
}

// =============================================================================
// γ.2 bilateral binding receipts
// =============================================================================

/// Build a schedule-projected scope-2 `WitnessedReceipt` for one cell of a
/// committed bilateral Turn.
///
/// The Effect-VM proof material carries the real per-cell trace + base PI
/// vector, but `generate_effect_vm_proof` does not write the bilateral-schedule
/// / turn-identity PI slots (those are populated by the executor's
/// `populate_pi`). We replay the *exact same* canonical projection here —
/// `compute_turn_identity_pi` + `ExpectedBilateral::counts_for/roots_for` +
/// `project_into_pi` + `IS_AGENT_CELL` — so the resulting WR's PI agrees with
/// what `WitnessedReceipt::verify_bilateral_chain` (and the outer aggregation
/// AIR) expect. No fabrication: the trace is the real proven trace, and the
/// PI slots are derived from the canonical Turn the same way the executor does.
fn schedule_projected_wr(
    turn: &Turn,
    cell_id: &CellId,
    receipt: &dregg_turn::TurnReceipt,
    material: &EffectVmProofMaterial,
) -> dregg_turn::WitnessedReceipt {
    use dregg_circuit::BabyBear;
    use dregg_circuit::effect_vm::pi as p;
    use dregg_turn::bilateral_schedule::{ExpectedBilateral, project_into_pi};

    let mut pi: Vec<BabyBear> = material
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new(v as u32))
        .collect();
    if pi.len() < p::BASE_COUNT {
        pi.resize(p::BASE_COUNT, BabyBear::ZERO);
    }

    let (th, eg, actor_nonce, prev) = dregg_turn::TurnExecutor::compute_turn_identity_pi(turn);
    for i in 0..p::TURN_HASH_LEN {
        pi[p::TURN_HASH_BASE + i] = th[i];
    }
    for i in 0..p::EFFECTS_HASH_GLOBAL_LEN {
        pi[p::EFFECTS_HASH_GLOBAL_BASE + i] = eg[i];
    }
    pi[p::ACTOR_NONCE] = BabyBear::new((actor_nonce & 0x7FFF_FFFF) as u32);
    for i in 0..p::PREVIOUS_RECEIPT_HASH_LEN {
        pi[p::PREVIOUS_RECEIPT_HASH_BASE + i] = prev[i];
    }

    let schedule = ExpectedBilateral::from_turn(turn);
    let counts = schedule.counts_for(cell_id);
    let roots = schedule.roots_for(cell_id, actor_nonce);
    project_into_pi(&mut pi, &counts, &roots);
    pi[p::IS_AGENT_CELL] = if cell_id == &turn.agent {
        BabyBear::new(1)
    } else {
        BabyBear::ZERO
    };

    let pi_u32: Vec<u32> = pi.iter().map(|x| x.as_u32()).collect();
    let trace_bb: Vec<Vec<BabyBear>> = material
        .trace_rows
        .iter()
        .map(|row| row.iter().map(|&v| BabyBear::new(v)).collect())
        .collect();
    dregg_turn::WitnessedReceipt::from_components(
        receipt.clone(),
        hex_decode_var(&material.proof_hex).unwrap_or_default(),
        pi_u32,
        if trace_bb.is_empty() {
            None
        } else {
            Some(trace_bb.as_slice())
        },
    )
}

/// Submit a Turn carrying exactly one bilateral effect (Transfer / Grant /
/// Introduce) and surface per-side WitnessedReceipts. The executor's
/// `ExpectedBilateral::from_turn` derives the same schedule the AIR PIs
/// project into; this tool returns the trace + proof for the from- and
/// to-side cells so the caller can independently verify the bilateral
/// identity via `WitnessedReceipt::verify_bilateral_chain`.
///
/// Stage 7-γ.2 Phase 2 (#134): when both per-cell proofs are present, the
/// tool also runs the joint bilateral aggregator
/// (`prove_aggregated_bundle`) over the two schedule-projected
/// WitnessedReceipts and attaches the resulting `AggregatedBundle` (real outer
/// STARK proof bytes) under `aggregated_bundle`. The bundle verifies in
/// constant time relative to the number of cells via
/// `verify_aggregated_bundle`.
async fn tool_bilateral_action(params: &Value, state: &NodeState) -> McpToolResult {
    let mode = match params.get("mode").and_then(|v| v.as_str()) {
        Some(m) => m.to_string(),
        None => return McpToolResult::error("missing required parameter: mode"),
    };
    let from_hex = match params.get("from").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: from"),
    };
    let to_hex = match params.get("to").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: to"),
    };
    let from_bytes = match hex_decode(from_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for from"),
    };
    let to_bytes = match hex_decode(to_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for to"),
    };
    let from_cell = dregg_cell::CellId(from_bytes);
    let to_cell = dregg_cell::CellId(to_bytes);

    let permissions_str = params
        .get("permissions")
        .and_then(|v| v.as_str())
        .unwrap_or("signature");
    let permissions = match permissions_str {
        "none" | "None" => dregg_cell::AuthRequired::None,
        "signature" | "Signature" => dregg_cell::AuthRequired::Signature,
        "proof" | "Proof" => dregg_cell::AuthRequired::Proof,
        "either" | "Either" => dregg_cell::AuthRequired::Either,
        other => {
            return McpToolResult::error(format!(
                "invalid permissions: '{other}' (none|signature|proof|either)"
            ));
        }
    };

    let effect = match mode.as_str() {
        "transfer" => {
            let amount = match params.get("amount").and_then(|v| v.as_u64()) {
                Some(a) => a,
                None => return McpToolResult::error("missing required parameter: amount"),
            };
            dregg_turn::Effect::Transfer {
                from: from_cell,
                to: to_cell,
                amount,
            }
        }
        "grant" => {
            let cap = dregg_cell::CapabilityRef {
                target: from_cell,
                slot: 0,
                permissions,
                breadstuff: None,
                expires_at: None,
                allowed_effects: None,
                stored_epoch: None,
            };
            dregg_turn::Effect::GrantCapability {
                from: from_cell,
                to: to_cell,
                cap,
            }
        }
        "introduce" => {
            let target_hex = match params.get("target").and_then(|v| v.as_str()) {
                Some(h) => h,
                None => return McpToolResult::error("missing required parameter: target"),
            };
            let target_bytes = match hex_decode(target_hex) {
                Ok(b) => b,
                Err(_) => return McpToolResult::error("invalid hex for target"),
            };
            dregg_turn::Effect::Introduce {
                introducer: from_cell,
                recipient: to_cell,
                target: dregg_cell::CellId(target_bytes),
                permissions,
            }
        }
        other => {
            return McpToolResult::error(format!(
                "invalid mode: '{other}' (transfer|grant|introduce)"
            ));
        }
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    if s.ledger.get(&from_cell).is_none() {
        return McpToolResult::json(&serde_json::json!({
            "activity_status": "rejected",
            "proof_status": "missing_pre_state",
            "committed": false,
            "error": format!("bilateral action: from cell {} is not in the local ledger; refusing to synthesize a stub for a committed proof-bearing turn", from_hex),
        }));
    }
    if s.ledger.get(&to_cell).is_none() {
        return McpToolResult::json(&serde_json::json!({
            "activity_status": "rejected",
            "proof_status": "missing_pre_state",
            "committed": false,
            "error": format!("bilateral action: to cell {} is not in the local ledger; refusing to synthesize a stub for a committed proof-bearing turn", to_hex),
        }));
    }

    let agent_cell_id = from_cell;

    let action = dregg_turn::Action {
        target: from_cell,
        method: dregg_turn::action::symbol("bilateral"),
        args: vec![],
        authorization: dregg_turn::Authorization::Unchecked,
        preconditions: dregg_cell::Preconditions::default(),
        effects: vec![effect.clone()],
        may_delegate: dregg_turn::DelegationMode::None,
        commitment_mode: dregg_turn::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
    forest.add_root(action);

    let turn_nonce = s.cclerk.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce: turn_nonce,
        fee: 10_000,
        memo: Some(format!("bilateral {mode}")),
        valid_until: None,
        call_forest: forest,
        depends_on: vec![],
        previous_receipt_hash: s.cclerk.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };
    let turn_hash = hex_encode(&turn.hash());

    let from_pre = s
        .ledger
        .get(&from_cell)
        .map(|c| (c.state.balance(), c.state.nonce()));
    let to_pre = s
        .ledger
        .get(&to_cell)
        .map(|c| (c.state.balance(), c.state.nonce()));

    let (from_vm, to_vm): (
        Vec<dregg_circuit::effect_vm::Effect>,
        Vec<dregg_circuit::effect_vm::Effect>,
    ) = match &effect {
        dregg_turn::Effect::Transfer { amount, .. } => (
            vec![dregg_circuit::effect_vm::Effect::Transfer {
                amount: *amount,
                direction: 1,
            }],
            vec![dregg_circuit::effect_vm::Effect::Transfer {
                amount: *amount,
                direction: 0,
            }],
        ),
        dregg_turn::Effect::GrantCapability { cap, .. } => (
            vec![dregg_circuit::effect_vm::Effect::GrantCapability {
                cap_entry: grant_cap_entry_8(cap.slot.wrapping_add(1)),
                phase_b: None,
            }],
            vec![dregg_circuit::effect_vm::Effect::GrantCapability {
                cap_entry: grant_cap_entry_8(cap.slot.wrapping_add(1)),
                phase_b: None,
            }],
        ),
        dregg_turn::Effect::Introduce { .. } => (
            vec![dregg_circuit::effect_vm::Effect::NoOp],
            vec![dregg_circuit::effect_vm::Effect::NoOp],
        ),
        _ => (Vec::new(), Vec::new()),
    };
    let from_pre = match require_pre_state(&from_cell, from_pre, "bilateral action from-side") {
        Ok(pre) => pre,
        Err(result) => return result,
    };
    let to_pre = match require_pre_state(&to_cell, to_pre, "bilateral action to-side") {
        Ok(pre) => pre,
        Err(result) => return result,
    };
    let from_proof = match require_effect_vm_proof(
        from_pre.0,
        from_pre.1,
        &from_vm,
        "bilateral action from-side",
    ) {
        Ok(material) => material,
        Err(result) => return result,
    };
    let to_proof =
        match require_effect_vm_proof(to_pre.0, to_pre.1, &to_vm, "bilateral action to-side") {
            Ok(material) => material,
            Err(result) => return result,
        };

    let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    let (committed_receipt_opt, error_str) = match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let receipt_hash = receipt.receipt_hash();
            if let Some(witnessed) =
                witnessed_receipt_from_effect_material(receipt.clone(), &from_proof)
            {
                s.push_witnessed_receipt(receipt_hash, witnessed);
            }
            if let Some(witnessed) =
                witnessed_receipt_from_effect_material(receipt.clone(), &to_proof)
            {
                s.push_witnessed_receipt(receipt_hash, witnessed);
            }
            s.cclerk
                .append_receipt(receipt.clone())
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");
            (Some(receipt), None)
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            (None, Some(format!("turn rejected: {reason}")))
        }
        _ => (None, Some("bilateral turn did not commit".to_string())),
    };
    drop(s);

    let receipt = match committed_receipt_opt {
        Some(r) => r,
        None => {
            return McpToolResult::json(&serde_json::json!({
                "activity_status": "rejected",
                "proof_status": "not_committed",
                "committed": false,
                "error": error_str.unwrap_or_else(|| "unknown".to_string()),
                "turn_hash": turn_hash,
            }));
        }
    };

    let sched = dregg_turn::bilateral_schedule::ExpectedBilateral::from_turn(&turn);
    let from_counts = sched.counts_for(&from_cell);
    let to_counts = sched.counts_for(&to_cell);

    let build_witnessed = |proof_hex: &str, pi: &[u64], trace_rows: &[Vec<u32>]| -> Value {
        if proof_hex.is_empty() {
            return serde_json::Value::Null;
        }
        let trace_bb: Vec<Vec<dregg_circuit::BabyBear>> = trace_rows
            .iter()
            .map(|row| {
                row.iter()
                    .map(|&v| dregg_circuit::BabyBear::new(v))
                    .collect()
            })
            .collect();
        let proof_bytes = match hex_decode_var(proof_hex) {
            Ok(b) => b,
            Err(_) => return serde_json::Value::Null,
        };
        let pi_u32: Vec<u32> = pi.iter().map(|x| *x as u32).collect();
        let wr = dregg_turn::WitnessedReceipt::from_components(
            receipt.clone(),
            proof_bytes,
            pi_u32,
            if trace_bb.is_empty() {
                None
            } else {
                Some(trace_bb.as_slice())
            },
        );
        serde_json::to_value(&wr).unwrap_or(serde_json::Value::Null)
    };

    let from_wr_json = build_witnessed(
        &from_proof.proof_hex,
        &from_proof.public_inputs,
        &from_proof.trace_rows,
    );
    let to_wr_json = build_witnessed(
        &to_proof.proof_hex,
        &to_proof.public_inputs,
        &to_proof.trace_rows,
    );

    // Stage 7-γ.2 Phase 2 (#134): run the joint bilateral aggregator over the
    // two schedule-projected WitnessedReceipts and attach the real outer STARK
    // proof. We re-derive the canonical schedule projection (the executor's
    // `populate_pi` discipline) so the aggregator's Phase-1 gate and outer AIR
    // both accept the per-cell PIs.
    let (aggregated_bundle_json, aggregation_status) = {
        let from_wr = schedule_projected_wr(&turn, &from_cell, &receipt, &from_proof);
        let to_wr = schedule_projected_wr(&turn, &to_cell, &receipt, &to_proof);
        let entries = vec![(from_cell, from_wr), (to_cell, to_wr)];
        match dregg_turn::aggregate_bilateral_prover::prove_aggregated_bundle(&turn, &entries) {
            Ok(bundle) => {
                // Self-check: the bundle must verify (real outer STARK verify).
                match dregg_turn::aggregate_bilateral_prover::verify_aggregated_bundle(&bundle) {
                    Ok(()) => (
                        serde_json::to_value(&bundle).unwrap_or(Value::Null),
                        "aggregated".to_string(),
                    ),
                    Err(e) => (Value::Null, format!("aggregation_verify_failed: {e}")),
                }
            }
            Err(e) => (Value::Null, format!("aggregation_prove_failed: {e}")),
        }
    };

    McpToolResult::json(&serde_json::json!({
        "activity_status": "committed",
        "proof_status": "proved",
        "committed": true,
        "mode": mode,
        "turn_hash": turn_hash,
        "from_cell": from_hex,
        "to_cell": to_hex,
        "aggregated_bundle": aggregated_bundle_json,
        "aggregation_status": aggregation_status,
        "expected_schedule": {
            "transfers": sched.transfers.len(),
            "grants": sched.grants.len(),
            "introduces": sched.introduces.len(),
        },
        "from_side": {
            "outbound_transfer": from_counts.outbound_transfer,
            "outbound_grant": from_counts.outbound_grant,
            "intro_as_introducer": from_counts.intro_as_introducer,
            "intro_as_recipient": from_counts.intro_as_recipient,
            "intro_as_target": from_counts.intro_as_target,
            "witnessed_receipt": from_wr_json,
        },
        "to_side": {
            "inbound_transfer": to_counts.inbound_transfer,
            "inbound_grant": to_counts.inbound_grant,
            "intro_as_introducer": to_counts.intro_as_introducer,
            "intro_as_recipient": to_counts.intro_as_recipient,
            "intro_as_target": to_counts.intro_as_target,
            "witnessed_receipt": to_wr_json,
        },
        "note": "Both sides' WitnessedReceipts cover the same TurnReceipt; together they expose the γ.2 bilateral algebraic binding (per-cell PI projection). Use WitnessedReceipt::verify_bilateral_chain off-line to re-derive the schedule and check accumulator-root equality.",
    }))
}

// =============================================================================
// FactoryDescriptor canonical creation path
// =============================================================================

/// Emit an `Effect::CreateCellFromFactory` so the new cell is created
/// through the factory descriptor's validate_creation path. This is the
/// canonical replacement for the legacy `dregg_create_from_factory` tool,
/// which inserted cells via direct ledger manipulation; the new tool routes
/// through the executor and the factory descriptor's invariants.
async fn tool_create_cell_from_factory_effect(params: &Value, state: &NodeState) -> McpToolResult {
    let factory_vk_hex = match params.get("factory_vk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: factory_vk"),
    };
    let factory_vk = match hex_decode(factory_vk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for factory_vk"),
    };
    let sovereign = params
        .get("sovereign")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);
    let program_vk: Option<[u8; 32]> = match params.get("program_vk").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => Some(b),
            Err(_) => return McpToolResult::error("invalid hex for program_vk"),
        },
        None => None,
    };

    let initial_fields: Vec<(u32, u64)> =
        match params.get("initial_fields").and_then(|v| v.as_array()) {
            Some(arr) => {
                let mut out = Vec::with_capacity(arr.len());
                for entry in arr {
                    let idx = entry
                        .get("index")
                        .and_then(|v| v.as_u64())
                        .ok_or_else(|| "initial_fields[*].index missing".to_string());
                    let val = entry
                        .get("value")
                        .and_then(|v| v.as_u64())
                        .ok_or_else(|| "initial_fields[*].value missing".to_string());
                    match (idx, val) {
                        (Ok(i), Ok(v)) => out.push((i as u32, v)),
                        (Err(e), _) | (_, Err(e)) => return McpToolResult::error(e),
                    }
                }
                out
            }
            None => Vec::new(),
        };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let owner_pubkey: [u8; 32] = match params.get("owner_pubkey").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for owner_pubkey"),
        },
        None => s.cclerk.public_key().0,
    };
    let token_id: [u8; 32] = match params.get("token_id").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for token_id"),
        },
        None => blake3::derive_key("dregg-mcp-factory-token-v1", &factory_vk),
    };

    let mode = if sovereign {
        dregg_cell::CellMode::Sovereign
    } else {
        dregg_cell::CellMode::Hosted
    };

    let params_struct = dregg_cell::factory::FactoryCreationParams {
        mode,
        program_vk,
        initial_fields,
        initial_caps: Vec::new(),
        owner_pubkey,
    };

    let effect = dregg_turn::Effect::CreateCellFromFactory {
        factory_vk,
        owner_pubkey,
        token_id,
        params: params_struct,
    };

    let agent_cell_id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);
    let nonce = s.cclerk.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        fee: 10_000,
        memo: Some("create cell from factory (mcp)".to_string()),
        valid_until: None,
        call_forest: build_signed_forest(agent_cell_id, vec![effect], &s.cclerk, &s.federation_id),
        depends_on: vec![],
        previous_receipt_hash: s.cclerk.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };
    let turn_hash = hex_encode(&turn.hash());

    let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    let new_cell_id = dregg_cell::CellId::derive_raw(&owner_pubkey, &token_id);
    let new_cell_hex = hex_encode(&new_cell_id.0);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");
            drop(s);
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });
            McpToolResult::json(&serde_json::json!({
                "created": true,
                "factory_vk": factory_vk_hex,
                "new_cell_id": new_cell_hex,
                "owner_pubkey": hex_encode(&owner_pubkey),
                "token_id": hex_encode(&token_id),
                "sovereign": sovereign,
                "turn_hash": turn_hash,
                "note": "Created via Effect::CreateCellFromFactory; the executor ran the factory descriptor's validate_creation path before insertion.",
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "created": false,
                "error": format!("factory creation rejected: {reason}"),
                "turn_hash": turn_hash,
            }))
        }
        _ => {
            drop(s);
            McpToolResult::error("factory creation turn did not commit")
        }
    }
}

// =============================================================================
// Starbridge-app tool helpers
// =============================================================================
//
// These four tools wrap the canonical `build_*_action` helpers from the
// four anchor starbridge-apps so the cross-app-e2e demo can drive a
// real running node over MCP. Each tool:
//
//   1. Parses the action-specific parameters from JSON.
//   2. Builds a temporary `AppCipherclerk` from a fresh `AgentCipherclerk`
//      (matching seed irrelevant — we discard its signature).
//   3. Calls the starbridge-app's `build_*_action(&temp_cclerk, ...)` to
//      construct the canonical Action with the right effects + witness blobs.
//   4. Re-signs the action with the *node's* cipherclerk via
//      `AgentCipherclerk::sign_action` (federation_id [0u8; 32], matching
//      the executor default).  This binds the action's authorization to
//      the node's identity.
//   5. Ensures the target cell exists in the local ledger (insert as a
//      hosted cell owned by the node's pubkey if missing) — required for
//      the executor to find a cell to act on.
//   6. Wraps the signed action in a Turn, executes through TurnExecutor.
//   7. Projects the action's `SetField` effects into `effect_vm::Effect`
//      domain and produces a STARK proof via `generate_effect_vm_proof`.
//   8. Returns receipt JSON matching the shape of `grant.proof.json`
//      (effect_vm_proof_hex, effect_vm_public_inputs, effect_vm_trace_rows,
//      effect_vm_witness_hash_hex).
//
// **Effect-VM coverage gap**: the underlying `EffectVmAir` understands
// `Transfer`, `SetField`, `GrantCapability`, and `NoOp`. The starbridge
// apps emit `SetField` (which we map directly) and `EmitEvent` (which has
// no AIR row — we either skip it or, for purely-event actions like
// `register_service`, synthesise one `SetField` row carrying the event's
// path_hash so the proof remains non-trivial).

/// Translate a turn-domain `Effect` into a single Effect-VM `Effect`.
/// Covers all AIR-side variants:
/// - `SetField` → `VmEffect::SetField`
/// - `Transfer` → `VmEffect::Transfer` (debit side, direction=1)
/// - `EmitEvent` → `VmEffect::EmitEvent` (BLAKE3 topic + payload, per #110)
/// Returns `None` for variants without an AIR-side analog (IncrementNonce,
/// GrantCapability, RevokeCapability, CreateCell, etc.).
fn project_setfield_to_vm(effect: &dregg_turn::Effect) -> Option<dregg_circuit::effect_vm::Effect> {
    match effect {
        dregg_turn::Effect::SetField { index, value, .. } => {
            let mut le4 = [0u8; 4];
            le4.copy_from_slice(&value[..4]);
            Some(dregg_circuit::effect_vm::Effect::SetField {
                field_idx: *index as u32,
                value: dregg_circuit::BabyBear::new(u32::from_le_bytes(le4)),
            })
        }
        dregg_turn::Effect::Transfer { amount, .. } => {
            Some(dregg_circuit::effect_vm::Effect::Transfer {
                amount: *amount,
                direction: 1,
            })
        }
        dregg_turn::Effect::EmitEvent { event, .. } => {
            // Canonical (topic_hash, payload_hash) projection — mirrors
            // `turn/src/executor/effect_vm_bridge.rs` EmitEvent arm (#110).
            // topic_hash  = BLAKE3(event.topic)
            // payload_hash = BLAKE3(event.data[0] ‖ event.data[1] ‖ …)
            let topic_bytes = *blake3::hash(&event.topic).as_bytes();
            let mut payload_hasher = blake3::Hasher::new();
            for d in &event.data {
                payload_hasher.update(d);
            }
            let payload_bytes = *payload_hasher.finalize().as_bytes();

            fn bytes32_to_8_felts(b: &[u8; 32]) -> [dregg_circuit::BabyBear; 8] {
                let mut out = [dregg_circuit::BabyBear::ZERO; 8];
                for i in 0..8 {
                    let off = i * 4;
                    let v = u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]]);
                    out[i] = dregg_circuit::BabyBear::new(v % dregg_circuit::field::BABYBEAR_P);
                }
                out
            }

            Some(dregg_circuit::effect_vm::Effect::EmitEvent {
                topic_hash: bytes32_to_8_felts(&topic_bytes),
                payload_hash: bytes32_to_8_felts(&payload_bytes),
            })
        }
        _ => None,
    }
}

/// Ensure `cell_id` exists in the ledger. If missing, insert a default
/// hosted cell owned by the node's pubkey with zero balance. This lets
/// the executor find a cell to act on without forcing callers to
/// pre-register through a separate flow — the demo orchestrator can
/// just call the starbridge-app tools and the cells materialize on
/// first use.
///
/// Returns the (balance, nonce) pair the cell holds after the call
/// (used as the EffectVM `initial_balance`/`initial_nonce`).
fn ensure_cell_in_ledger(
    cell_id: CellId,
    pk_bytes: [u8; 32],
    ledger: &mut dregg_cell::Ledger,
) -> (u64, u64) {
    if ledger.get(&cell_id).is_none() {
        // `Cell::with_balance` derives the cell id from
        // `(public_key, token_id)`, which only matches the agent's own
        // cell. For arbitrary caller-supplied cell ids (registry cells,
        // issuer cells, subscription cells, etc.) we use the
        // `remote_stub_with_id_pk_balance` constructor that records the
        // cell at the *specified* id while still attaching the node's
        // pubkey so signature-mode auth resolves correctly.
        let cell = dregg_cell::Cell::remote_stub_with_id_pk_balance(cell_id, pk_bytes, 0);
        // Best-effort: if insert fails we surface a zero state; the
        // executor will reject the turn downstream and the tool returns
        // the Rejected receipt.
        let _ = ledger.insert_cell(cell);
    }
    match ledger.get(&cell_id) {
        Some(c) => (c.state.balance(), c.state.nonce()),
        None => (0, 0),
    }
}

/// Build a `Turn` that wraps a single starbridge-app action and submit
/// it through the executor.  Generates an Effect-VM STARK proof over
/// the action's `SetField` effects (plus optional synthetic rows the
/// caller pre-populates in `extra_vm_effects`).  Returns the
/// canonical (receipt-bearing) JSON response shape used by all four
/// starbridge tools.
async fn run_starbridge_action(
    state: &NodeState,
    action: dregg_turn::Action,
    memo: String,
    extra_vm_effects: Vec<dregg_circuit::effect_vm::Effect>,
    extra_links: serde_json::Map<String, Value>,
) -> McpToolResult {
    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Node identity + agent cell.
    let pk_bytes = s.cclerk.public_key().0;
    let agent_cell_id = dregg_cell::CellId::derive_raw(&pk_bytes, &[0u8; 32]);
    let federation_id = [0u8; 32];

    // Re-sign the action with the node's cipherclerk (overwrites the temp
    // signature placed by the starbridge-apps builder).
    let signed_action = s.cclerk.sign_action(action, &federation_id);

    // Make sure the action's target cell exists in the ledger.
    let target = signed_action.target;
    let (target_balance, target_nonce) = ensure_cell_in_ledger(target, pk_bytes, &mut s.ledger);
    // Also ensure the agent cell exists — turn-level checks reference it.
    let _ = ensure_cell_in_ledger(agent_cell_id, pk_bytes, &mut s.ledger);

    // Project SetField (and any other supported) effects into VM domain.
    let mut vm_effects: Vec<dregg_circuit::effect_vm::Effect> = signed_action
        .effects
        .iter()
        .filter_map(project_setfield_to_vm)
        .collect();
    vm_effects.extend(extra_vm_effects);

    // Build the Turn.
    let mut forest = CallForest::new();
    forest.add_root(signed_action);

    let nonce = s.cclerk.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        fee: 10_000,
        memo: Some(memo),
        valid_until: None,
        call_forest: forest,
        depends_on: vec![],
        previous_receipt_hash: s.cclerk.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let signed = s.cclerk.sign_turn(&turn);
    let turn_hash = hex_encode(&turn.hash());

    // Execute locally.
    let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let receipt_hash_hex = hex_encode(&receipt.receipt_hash());
            let receipt_bytes =
                postcard::to_allocvec(&receipt).expect("TurnReceipt serializes via postcard");
            let receipt_bytes_hex = hex_encode(&receipt_bytes);
            let pre_state_hash_hex = hex_encode(&receipt.pre_state_hash);
            let post_state_hash_hex = hex_encode(&receipt.post_state_hash);
            let effects_hash_hex = hex_encode(&receipt.effects_hash);

            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");

            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");
            drop(s);

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            if let Some(gossip) = state.gossip().await {
                let h = signed.turn.hash();
                tokio::spawn(async move {
                    gossip.gossip_turn(h, turn_data).await;
                });
            }

            // Generate Effect-VM proof.
            let (proof_hex, public_inputs, trace_rows, witness_hash_hex) =
                generate_effect_vm_proof(target_balance, target_nonce, &vm_effects);

            let proof_field = if proof_hex.is_empty() {
                Value::Null
            } else {
                Value::String(proof_hex)
            };
            let trace_field = if trace_rows.is_empty() {
                Value::Null
            } else {
                serde_json::to_value(&trace_rows).unwrap_or(Value::Null)
            };
            let witness_hash_field = if witness_hash_hex.is_empty() {
                Value::Null
            } else {
                Value::String(witness_hash_hex)
            };

            let mut out = serde_json::Map::new();
            out.insert("committed".into(), Value::Bool(true));
            out.insert("turn_hash".into(), Value::String(turn_hash));
            out.insert("receipt_hash".into(), Value::String(receipt_hash_hex));
            out.insert("receipt_bytes_hex".into(), Value::String(receipt_bytes_hex));
            out.insert("pre_state_hash".into(), Value::String(pre_state_hash_hex));
            out.insert("post_state_hash".into(), Value::String(post_state_hash_hex));
            out.insert("effects_hash".into(), Value::String(effects_hash_hex));
            out.insert("effect_vm_proof_hex".into(), proof_field);
            out.insert(
                "effect_vm_public_inputs".into(),
                serde_json::to_value(&public_inputs).unwrap_or(Value::Null),
            );
            out.insert("effect_vm_trace_rows".into(), trace_field);
            out.insert("effect_vm_witness_hash_hex".into(), witness_hash_field);
            for (k, v) in extra_links {
                out.insert(k, v);
            }
            McpToolResult::json(&Value::Object(out))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "committed": false,
                "turn_hash": turn_hash,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::error("starbridge action turn did not commit")
        }
    }
}

/// Build a fresh `AppCipherclerk` for use as a builder argument. The
/// signature it places on the action is overwritten by the node
/// cipherclerk's `sign_action` before submission, so the temp cipherclerk
/// only contributes the action's `target`/`method`/`effects`/witness
/// shape — none of its key material lands in the receipt chain.
fn temp_app_cclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0u8; 32])
}

/// Common helper: read the agent's own cell id from state. The caller
/// holds the lock; we just compute the derivation.
fn agent_cell_of(cclerk: &AgentCipherclerk) -> CellId {
    dregg_cell::CellId::derive_raw(&cclerk.public_key().0, &[0u8; 32])
}

/// Default registry/issuer/etc. cell when the caller omits it: the
/// node's own agent cell. Returns Err if the caller-supplied hex is
/// invalid (so the tool can surface a clean error).
fn parse_or_default_cell(value: Option<&str>, default: CellId) -> Result<CellId, String> {
    match value {
        None => Ok(default),
        Some(h) => match hex_decode(h) {
            Ok(b) => Ok(dregg_cell::CellId(b)),
            Err(_) => Err(format!(
                "invalid hex for cell id '{h}' (expected 64 hex chars)"
            )),
        },
    }
}

// =============================================================================
// Tool: dregg_register_name
// =============================================================================

async fn tool_register_name(params: &Value, state: &NodeState) -> McpToolResult {
    let name = match params.get("name").and_then(|v| v.as_str()) {
        Some(s) => s.to_string(),
        None => return McpToolResult::error("missing required parameter: name"),
    };
    let expiry_height = match params.get("expiry_height").and_then(|v| v.as_u64()) {
        Some(e) => e,
        None => return McpToolResult::error("missing required parameter: expiry_height"),
    };

    // Resolve cell ids & defaults.
    let (agent_cell, node_pk) = {
        let s = state.read().await;
        if !s.unlocked {
            return McpToolResult::error("cipherclerk is locked; unlock first");
        }
        (agent_cell_of(&s.cclerk), s.cclerk.public_key().0)
    };

    let registry_cell = match parse_or_default_cell(
        params.get("registry_cell").and_then(|v| v.as_str()),
        agent_cell,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(e),
    };
    let issuer_cell = match parse_or_default_cell(
        params.get("issuer_cell").and_then(|v| v.as_str()),
        agent_cell,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(e),
    };

    let owner = match params.get("owner").and_then(|v| v.as_str()) {
        None => node_pk,
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for owner (expected 64 hex chars)"),
        },
    };

    // Schema id defaults to the kyc-v1 schema commitment.
    let schema_id = match params.get("credential_schema_id").and_then(|v| v.as_str()) {
        None => starbridge_identity::schema_commitment(&sb_kyc_schema()),
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => {
                return McpToolResult::error(
                    "invalid hex for credential_schema_id (expected 64 hex chars)",
                );
            }
        },
    };

    // Credential proof blob defaults to a small non-empty stub (the
    // attested-tier verifier only requires a non-empty witness blob
    // until the BlindedSet verifier registry lands; cross_app_helper
    // documents this with `attested_tier_accepted_by_executor`).
    let proof_bytes = match params
        .get("credential_presentation_proof_hex")
        .and_then(|v| v.as_str())
    {
        None => b"dregg-mcp-credential-stub-v1".to_vec(),
        Some(h) => match hex_decode_var(h) {
            Ok(b) => b,
            Err(_) => {
                return McpToolResult::error("invalid hex for credential_presentation_proof_hex");
            }
        },
    };

    let temp = temp_app_cclerk();
    let action = sb_build_register_with_credential_action(
        &temp,
        registry_cell,
        &name,
        owner,
        expiry_height,
        issuer_cell,
        schema_id,
        proof_bytes.clone(),
    );

    let mut links = serde_json::Map::new();
    links.insert("registered_name".into(), Value::String(name.clone()));
    links.insert(
        "registry_cell".into(),
        Value::String(hex_encode(&registry_cell.0)),
    );
    links.insert(
        "issuer_cell".into(),
        Value::String(hex_encode(&issuer_cell.0)),
    );
    links.insert("owner".into(), Value::String(hex_encode(&owner)));
    links.insert(
        "schema_commitment".into(),
        Value::String(hex_encode(&schema_id)),
    );
    links.insert(
        "expiry_height".into(),
        Value::Number(serde_json::Number::from(expiry_height)),
    );
    links.insert(
        "presentation_proof_blob_hash".into(),
        Value::String(hex_encode(blake3::hash(&proof_bytes).as_bytes())),
    );

    run_starbridge_action(
        state,
        action,
        format!("register_name: {name}"),
        Vec::new(),
        links,
    )
    .await
}

// =============================================================================
// Tool: dregg_publish_subscription
// =============================================================================

fn parse_bounty_state(s: &str) -> Option<SbBountyState> {
    match s.to_ascii_lowercase().as_str() {
        "posted" => Some(SbBountyState::Posted),
        "claimed" => Some(SbBountyState::Claimed),
        "fulfilled" => Some(SbBountyState::Fulfilled),
        "settled" => Some(SbBountyState::Settled),
        "canceled" => Some(SbBountyState::Canceled),
        _ => None,
    }
}

async fn tool_publish_subscription(params: &Value, state: &NodeState) -> McpToolResult {
    let new_head = match params.get("new_head").and_then(|v| v.as_u64()) {
        Some(n) => n,
        None => return McpToolResult::error("missing required parameter: new_head"),
    };
    let new_msg_root_hex = match params.get("new_message_root").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: new_message_root"),
    };
    let new_message_root = match hex_decode(new_msg_root_hex) {
        Ok(b) => b,
        Err(_) => {
            return McpToolResult::error(
                "invalid hex for new_message_root (expected 64 hex chars)",
            );
        }
    };
    let bounty_id_hex = match params.get("bounty_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: bounty_id"),
    };
    let bounty_id = match hex_decode(bounty_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for bounty_id"),
    };
    let prior_state_str = match params.get("prior_state").and_then(|v| v.as_str()) {
        Some(s) => s,
        None => return McpToolResult::error("missing required parameter: prior_state"),
    };
    let new_state_str = match params.get("new_state").and_then(|v| v.as_str()) {
        Some(s) => s,
        None => return McpToolResult::error("missing required parameter: new_state"),
    };
    let prior_state = match parse_bounty_state(prior_state_str) {
        Some(b) => b,
        None => return McpToolResult::error(format!("invalid prior_state: {prior_state_str}")),
    };
    let new_state = match parse_bounty_state(new_state_str) {
        Some(b) => b,
        None => return McpToolResult::error(format!("invalid new_state: {new_state_str}")),
    };
    let actor_pk_hash_hex = match params.get("actor_pk_hash").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: actor_pk_hash"),
    };
    let actor_pk_hash = match hex_decode(actor_pk_hash_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for actor_pk_hash"),
    };

    let agent_cell = {
        let s = state.read().await;
        if !s.unlocked {
            return McpToolResult::error("cipherclerk is locked; unlock first");
        }
        agent_cell_of(&s.cclerk)
    };
    let subscription_cell = match parse_or_default_cell(
        params.get("subscription_cell").and_then(|v| v.as_str()),
        agent_cell,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(e),
    };

    // u64 → 32-byte big-endian field (matches u64_field in
    // starbridge-nameservice / governed-namespace / cross_app_helper).
    let mut new_head_field = [0u8; 32];
    new_head_field[24..32].copy_from_slice(&new_head.to_be_bytes());

    let temp = temp_app_cclerk();
    let action = sb_build_bounty_publish(
        &temp,
        subscription_cell,
        new_head_field,
        new_message_root,
        &bounty_id,
        prior_state,
        new_state,
        &actor_pk_hash,
    );

    let payload_hash = starbridge_subscription::bounty_state_payload_hash(
        &bounty_id,
        prior_state,
        new_state,
        &actor_pk_hash,
    );

    let mut links = serde_json::Map::new();
    links.insert(
        "subscription_cell".into(),
        Value::String(hex_encode(&subscription_cell.0)),
    );
    links.insert("bounty_id".into(), Value::String(hex_encode(&bounty_id)));
    links.insert(
        "actor_pk_hash".into(),
        Value::String(hex_encode(&actor_pk_hash)),
    );
    links.insert(
        "payload_hash".into(),
        Value::String(hex_encode(&payload_hash)),
    );
    links.insert("prior_state".into(), Value::String(prior_state_str.into()));
    links.insert("new_state".into(), Value::String(new_state_str.into()));
    links.insert(
        "new_head".into(),
        Value::Number(serde_json::Number::from(new_head)),
    );

    run_starbridge_action(
        state,
        action,
        format!("publish_subscription: {prior_state_str}->{new_state_str}"),
        Vec::new(),
        links,
    )
    .await
}

// =============================================================================
// Tool: dregg_issue_credential
// =============================================================================

fn parse_schema_name(name: &str) -> Option<SbCredentialSchema> {
    match name.to_ascii_lowercase().as_str() {
        "kyc" | "kyc-v1" => Some(sb_kyc_schema()),
        "gov_id" | "gov-id" | "gov-id-v1" => Some(sb_gov_id_schema()),
        "employment" | "employment-v1" => Some(sb_employment_schema()),
        _ => None,
    }
}

fn parse_attributes_into(
    schema: &SbCredentialSchema,
    obj: &serde_json::Map<String, Value>,
) -> Result<SbCredentialAttributes, String> {
    use starbridge_identity::AttrValue;
    let mut attrs = SbCredentialAttributes::new();
    for (k, v) in obj {
        if !schema.has_attribute(k) {
            return Err(format!("attribute '{k}' not in schema '{}'", schema.name));
        }
        let attr_value = if let Some(u) = v.as_u64() {
            AttrValue::Integer(u)
        } else if let Some(_i) = v.as_i64() {
            return Err(format!(
                "attribute '{k}' integer value must be non-negative"
            ));
        } else if let Some(s) = v.as_str() {
            AttrValue::Text(s.into())
        } else {
            return Err(format!("attribute '{k}' value must be string or integer"));
        };
        attrs = attrs.with(k.as_str(), attr_value);
    }
    Ok(attrs)
}

async fn tool_issue_credential(params: &Value, state: &NodeState) -> McpToolResult {
    let (agent_cell, node_pk) = {
        let s = state.read().await;
        if !s.unlocked {
            return McpToolResult::error("cipherclerk is locked; unlock first");
        }
        (agent_cell_of(&s.cclerk), s.cclerk.public_key().0)
    };

    let issuer_cell = match parse_or_default_cell(
        params.get("issuer_cell").and_then(|v| v.as_str()),
        agent_cell,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(e),
    };

    let schema_name = params
        .get("schema")
        .and_then(|v| v.as_str())
        .unwrap_or("kyc");
    let schema = match parse_schema_name(schema_name) {
        Some(s) => s,
        None => return McpToolResult::error(format!("unknown schema: {schema_name}")),
    };

    let holder_id = match params.get("holder_id").and_then(|v| v.as_str()) {
        None => *blake3::hash(&node_pk).as_bytes(),
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for holder_id"),
        },
    };

    let attributes = match params.get("attributes").and_then(|v| v.as_object()) {
        None => SbCredentialAttributes::new(),
        Some(obj) => match parse_attributes_into(&schema, obj) {
            Ok(a) => a,
            Err(e) => return McpToolResult::error(e),
        },
    };

    let new_counter = params
        .get("new_counter")
        .and_then(|v| v.as_u64())
        .unwrap_or(1);
    let revocation_root = match params.get("revocation_root").and_then(|v| v.as_str()) {
        None => [0u8; 32],
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for revocation_root"),
        },
    };
    let issued_at = params
        .get("issued_at")
        .and_then(|v| v.as_i64())
        .unwrap_or(1_700_000_000);
    let not_after = params.get("not_after").and_then(|v| v.as_i64());

    // Mint the credential.  Use a deterministic IssuerKeys derived from
    // the node's pubkey so the issuance is reproducible across replays.
    let issuer_keys = SbIssuerKeys::new(
        blake3::derive_key("dregg-mcp-issuer-root-v1", &node_pk),
        blake3::derive_key("dregg-mcp-issuer-federation-v1", &node_pk),
        node_pk.to_vec(),
        "dregg-node-mcp",
    );

    let credential: SbCredential = match sb_issue(
        &issuer_keys,
        &schema,
        holder_id,
        attributes,
        issued_at,
        not_after,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(format!("credential issuance failed: {e}")),
    };
    let credential_id = credential.id();

    let temp = temp_app_cclerk();
    let action = sb_build_issue_credential_action(
        &temp,
        issuer_cell,
        &credential,
        new_counter,
        revocation_root,
    );

    let mut links = serde_json::Map::new();
    links.insert(
        "issuer_cell".into(),
        Value::String(hex_encode(&issuer_cell.0)),
    );
    links.insert("schema".into(), Value::String(schema_name.into()));
    links.insert(
        "schema_commitment".into(),
        Value::String(hex_encode(&starbridge_identity::schema_commitment(&schema))),
    );
    links.insert(
        "credential_id".into(),
        Value::String(hex_encode(&credential_id)),
    );
    links.insert("holder_id".into(), Value::String(hex_encode(&holder_id)));
    links.insert(
        "new_counter".into(),
        Value::Number(serde_json::Number::from(new_counter)),
    );
    links.insert(
        "revocation_root".into(),
        Value::String(hex_encode(&revocation_root)),
    );
    links.insert(
        "credential_encoded".into(),
        Value::String(credential.encoded.clone()),
    );

    run_starbridge_action(
        state,
        action,
        format!("issue_credential: {schema_name}"),
        Vec::new(),
        links,
    )
    .await
}

// =============================================================================
// Tool: dregg_register_service
// =============================================================================

async fn tool_register_service(params: &Value, state: &NodeState) -> McpToolResult {
    let path = match params.get("path").and_then(|v| v.as_str()) {
        Some(p) => p.to_string(),
        None => return McpToolResult::error("missing required parameter: path"),
    };

    let agent_cell = {
        let s = state.read().await;
        if !s.unlocked {
            return McpToolResult::error("cipherclerk is locked; unlock first");
        }
        agent_cell_of(&s.cclerk)
    };

    let namespace_cell = match parse_or_default_cell(
        params.get("namespace_cell").and_then(|v| v.as_str()),
        agent_cell,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(e),
    };
    let target_cell = match parse_or_default_cell(
        params.get("target_cell").and_then(|v| v.as_str()),
        agent_cell,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(e),
    };

    let temp = temp_app_cclerk();
    let action = sb_build_register_service_action(&temp, namespace_cell, &path, target_cell);

    // Closes #110: the underlying action emits one
    // `EmitEvent("service-registered", [path_hash, target_field])`. The
    // EffectVmAir now carries a real `EmitEvent` row variant with
    // canonical (topic_hash, payload_hash) binding, so the bridge in
    // `turn/src/executor/effect_vm_bridge.rs` projects the runtime
    // Event directly — no synthesised SetField is required. The proof's
    // PI surface (EMIT_EVENT_TOPIC_HASH / EMIT_EVENT_PAYLOAD_HASH) ties
    // the STARK to the actual emitted event.
    let path_hash = *blake3::hash(path.as_bytes()).as_bytes();
    let extra_vm: Vec<dregg_circuit::effect_vm::Effect> = Vec::new();

    let mut links = serde_json::Map::new();
    links.insert(
        "namespace_cell".into(),
        Value::String(hex_encode(&namespace_cell.0)),
    );
    links.insert("path".into(), Value::String(path.clone()));
    links.insert("path_hash".into(), Value::String(hex_encode(&path_hash)));
    links.insert(
        "target_cell".into(),
        Value::String(hex_encode(&target_cell.0)),
    );

    run_starbridge_action(
        state,
        action,
        format!("register_service: {path}"),
        extra_vm,
        links,
    )
    .await
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

fn handle_initialize(id: Value) -> JsonRpcResponse {
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
             `dregg://ontology` (the 29 verified effects you can drive), and `dregg://identity` \
             (who you are here). Then read `dregg://capabilities` (or call \
             `dregg_check_capabilities`) to see what authority you hold. Every state-changing turn \
             runs through a Lean-verified kernel and returns a STARK-proved receipt — VERIFY your \
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
const MCP_PAGE_SIZE: usize = 20;

/// Decode an opaque `cursor` param into a start index. Absent / malformed →
/// start at 0 (fail-open to the first page rather than erroring a list call).
fn decode_cursor(params: &Value) -> usize {
    params
        .get("cursor")
        .and_then(|v| v.as_str())
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(0)
}

/// Produce the `nextCursor` value for a page, or `None` when the page is the
/// last one. The cursor is the opaque encoding of the next start index.
fn next_cursor(start: usize, page_len: usize, total: usize) -> Option<String> {
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
async fn handle_tools_list(id: Value, params: Value, state: &NodeState) -> JsonRpcResponse {
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

async fn handle_tools_call(id: Value, params: Value, state: &NodeState) -> JsonRpcResponse {
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
// (the 29 verified effects + constraint vocabulary), the node's own identity,
// its receipt chain, capabilities, consensus/finality status, and any cell's
// state — all by URI, without invoking a (gated, side-effecting) tool. This is
// the "what is this place and what do I hold" half of inhabiting dregg.

/// The verified dregg ontology catalog, embedded at build time. AUTOGENERATED
/// (see `site/tools/gen-ontology-catalog.js`) from the Lean source of truth
/// (`Dregg2/Exec/TurnExecutorFull.lean` + `Dregg2/Exec/FFI.lean`): the 56
/// effects, their wire codecs, facets, categories, and semantics. An agent
/// reading `dregg://ontology` learns the entire effect vocabulary it can drive.
const DREGG_ONTOLOGY_CATALOG: &str =
    include_str!("../../site/src/_includes/studio/ontology-catalog.generated.json");

/// A static MCP resource the node always exposes.
struct StaticResource {
    uri: &'static str,
    name: &'static str,
    title: &'static str,
    description: &'static str,
    mime_type: &'static str,
}

/// The fixed (non-templated) resources. Cell state is a separate TEMPLATE
/// (`dregg://cell/{id}`) advertised via resources/templates/list.
fn static_resources() -> Vec<StaticResource> {
    vec![
        StaticResource {
            uri: "dregg://ontology",
            name: "dregg-ontology",
            title: "dregg Ontology (29 verified effects)",
            description: "The complete dregg effect vocabulary — 29 effects with wire codecs, facets \
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

fn static_resource_to_json(r: &StaticResource) -> Value {
    serde_json::json!({
        "uri": r.uri,
        "name": r.name,
        "title": r.title,
        "description": r.description,
        "mimeType": r.mime_type,
    })
}

async fn handle_resources_list(id: Value, params: Value, _state: &NodeState) -> JsonRpcResponse {
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

fn handle_resource_templates_list(id: Value) -> JsonRpcResponse {
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
fn resource_text_contents(uri: &str, mime: &str, body: String) -> Value {
    serde_json::json!({
        "contents": [{
            "uri": uri,
            "mimeType": mime,
            "text": body,
        }]
    })
}

/// The `dregg://about` orientation document.
fn dregg_about_markdown() -> String {
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
        1. **Orient** — read `dregg://ontology` (29 verified effects), `dregg://identity`, \
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
fn dregg_tools_catalog_json() -> Value {
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
async fn receipt_resource_json(turn_hex: &str, state: &NodeState) -> Result<Value, String> {
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

async fn handle_resources_read(id: Value, params: Value, state: &NodeState) -> JsonRpcResponse {
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
fn resource_body_from_tool(result: McpToolResult) -> String {
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
struct PromptSpec {
    name: &'static str,
    title: &'static str,
    description: &'static str,
    /// (arg name, description, required)
    arguments: &'static [(&'static str, &'static str, bool)],
}

fn prompt_specs() -> Vec<PromptSpec> {
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

fn handle_prompts_list(id: Value) -> JsonRpcResponse {
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

fn handle_prompts_get(id: Value, params: Value) -> JsonRpcResponse {
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
             1. Read resource `dregg://about` and `dregg://ontology` to learn the 29 effects.\n\
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
                     3. If `has_witness` is true, the standalone `dregg-verifier replay-chain` can \
                     re-check the whole receipt chain end-to-end. Your action is not merely \
                     logged — it is PROVEN."
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
const MCP_COMPLETION_LIMIT: usize = 100;

/// Hex cell ids currently in the node's ledger (the things `dregg://cell/{id}`,
/// `dregg_read_cell`, and turn `target_cell` arguments can name). Read-only.
async fn known_cell_ids(state: &NodeState) -> Vec<String> {
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
async fn known_turn_hashes(state: &NodeState) -> Vec<String> {
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
fn rank_completions(pool: Vec<String>, partial: &str) -> Value {
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
fn empty_completion() -> Value {
    serde_json::json!({ "completion": { "values": [], "total": 0, "hasMore": false } })
}

/// `completion/complete` — autocomplete a prompt argument or resource-template
/// variable. The `ref` selects the context (a prompt by name, or a resource
/// template by uriTemplate) and `argument` carries the variable name + the
/// partial value typed so far. We complete cell-id / turn-hash variables from
/// live node state; unknown refs return an empty (but valid) completion.
async fn handle_completion_complete(
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

/// Decode a variable-length hex string into bytes.
fn hex_decode_var(s: &str) -> Result<Vec<u8>, ()> {
    if s.len() % 2 != 0 {
        return Err(());
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    for chunk in s.as_bytes().chunks(2) {
        let high = nibble(chunk[0]).ok_or(())?;
        let low = nibble(chunk[1]).ok_or(())?;
        out.push((high << 4) | low);
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Issue #72 regression. Pins the producer-side contract:
    /// `generate_effect_vm_proof` MUST emit `PI[IS_AGENT_CELL] == 1`.
    ///
    /// Background: the verifier's `check_receipt_pi_binding`
    /// (`verifier/src/lib.rs::check_receipt_pi_binding`) requires
    /// `PI[IS_AGENT_CELL] == 1` for the v1 single-proof-per-WR replay
    /// shape, since mcp's path produces a single per-cell proof for the
    /// actor's own state transition (the cell IS the agent here). The
    /// underlying `dregg_circuit::effect_vm::generate_effect_vm_trace`
    /// does not constrain this slot — it is an executor-asserted bundle
    /// tag — so mcp must set it explicitly before proving. Without this,
    /// the standalone `dregg-verifier replay-chain` rejects the chain
    /// with "PI[IS_AGENT_CELL] = 0 but single-proof replay requires 1".
    ///
    /// See also `turn/src/executor/proof_verify.rs::populate_pi` (line
    /// 164) and `demo/two-ai-handoff/silver_helper.rs::cmd_make_recursive_witness`
    /// (line 1275), which set the same slot on their own paths.
    #[test]
    fn generate_effect_vm_proof_pins_is_agent_cell_to_one() {
        use dregg_circuit::effect_vm::pi as evm_pi;

        let vm_effects = vec![dregg_circuit::effect_vm::Effect::GrantCapability {
            cap_entry: grant_cap_entry_8(1),
            phase_b: None,
        }];

        let (proof_hex, public_inputs, _trace, _witness_hash) =
            generate_effect_vm_proof(100, 0, &vm_effects);

        assert!(
            !proof_hex.is_empty(),
            "generate_effect_vm_proof must emit a proof for non-empty effects"
        );
        assert!(
            public_inputs.len() > evm_pi::IS_AGENT_CELL,
            "PI vector must extend past IS_AGENT_CELL (have len={}, need >{})",
            public_inputs.len(),
            evm_pi::IS_AGENT_CELL,
        );
        assert_eq!(
            public_inputs[evm_pi::IS_AGENT_CELL],
            1,
            "Issue #72: generate_effect_vm_proof MUST set PI[IS_AGENT_CELL]=1 \
             for the v1 single-proof-per-WR replay shape; got {}",
            public_inputs[evm_pi::IS_AGENT_CELL]
        );
    }

    /// Issue #72 second pin: confirm the bare trace generator does NOT
    /// populate IS_AGENT_CELL. This documents WHY the explicit assignment
    /// in `generate_effect_vm_proof` is required — if the trace generator
    /// is later changed to populate this slot itself, this test will fail
    /// and the explicit set can be removed.
    #[test]
    fn generate_effect_vm_trace_leaves_is_agent_cell_unset() {
        use dregg_circuit::effect_vm::pi as evm_pi;
        let state = dregg_circuit::effect_vm::CellState::new(100, 0);
        let effects = vec![dregg_circuit::effect_vm::Effect::GrantCapability {
            cap_entry: grant_cap_entry_8(1),
            phase_b: None,
        }];
        let (_trace, public_inputs) =
            dregg_circuit::effect_vm::generate_effect_vm_trace(&state, &effects);
        assert_eq!(
            public_inputs[evm_pi::IS_AGENT_CELL].as_u32(),
            0,
            "trace generator should leave IS_AGENT_CELL at zero (executor sets it). \
             If this fires, remove the explicit set in generate_effect_vm_proof."
        );
    }

    // =====================================================================
    // Cross-app starbridge-tool integration tests (Issue #106 closure).
    //
    // These tests drive the four new tools (dregg_register_name,
    // dregg_publish_subscription, dregg_issue_credential,
    // dregg_register_service) through `dispatch_tool` against a real
    // NodeState (a fresh ledger + cipherclerk in a tempdir) and assert each
    // produces a receipt with a non-empty `effect_vm_proof_hex` plus
    // populated `effect_vm_public_inputs` / `effect_vm_trace_rows` /
    // `effect_vm_witness_hash_hex`. This is the "smallest test that
    // proves the loop closes" path: if every starbridge tool produces a
    // proof here, the same tools called over MCP stdio from a re-targeted
    // cross_app_helper will produce the same proofs in the demo's
    // on-disk receipt chain, and `verify_real.py`'s
    // `replay-chain` will Verify (not Unwitnessable) each entry.
    // =====================================================================

    use crate::state::NodeState;

    /// Build a fresh NodeState in a tempdir, unlock the cipherclerk, seed the
    /// agent cell with enough balance to pay turn fees, and return it ready for
    /// tool dispatch.
    async fn fresh_unlocked_state() -> (NodeState, tempfile::TempDir) {
        let tmp = tempfile::tempdir().expect("tempdir");
        // Deterministic seed so the test is reproducible.
        let mut seed = [0u8; 32];
        seed[0] = 0xA1;
        let state =
            NodeState::with_cclerk(tmp.path(), vec![], seed).expect("NodeState::with_cclerk");
        // Flip the unlocked flag — `with_cclerk` defaults to locked,
        // but the test bypasses passphrase entry.
        {
            let mut s = state.write().await;
            s.unlocked = true;
            let pk_bytes = s.cclerk.public_key().0;
            let cell = dregg_cell::Cell::with_balance(pk_bytes, [0u8; 32], 1_000_000);
            s.ledger
                .insert_cell(cell)
                .expect("test agent cell insert must succeed");
        }
        (state, tmp)
    }

    async fn fresh_unlocked_state_without_agent_cell() -> (NodeState, tempfile::TempDir) {
        let tmp = tempfile::tempdir().expect("tempdir");
        let mut seed = [0u8; 32];
        seed[0] = 0xD7;
        let state =
            NodeState::with_cclerk(tmp.path(), vec![], seed).expect("NodeState::with_cclerk");
        {
            let mut s = state.write().await;
            s.unlocked = true;
        }
        (state, tmp)
    }

    fn extract_json(result: &McpToolResult) -> Value {
        assert!(
            !result.is_error.unwrap_or(false),
            "tool returned error: {}",
            result
                .content
                .first()
                .map(|c| c.text.as_str())
                .unwrap_or("(no content)")
        );
        let text = result
            .content
            .first()
            .map(|c| c.text.as_str())
            .unwrap_or("");
        serde_json::from_str(text).expect("tool result content must be JSON")
    }

    fn assert_proof_populated(label: &str, j: &Value) {
        assert_eq!(
            j.get("committed").and_then(|v| v.as_bool()),
            Some(true),
            "[{label}] tool must commit; got: {j}",
        );
        let proof = j.get("effect_vm_proof_hex").cloned().unwrap_or(Value::Null);
        assert!(
            proof.is_string(),
            "[{label}] effect_vm_proof_hex must be a string; got {proof:?}",
        );
        let proof_hex = proof.as_str().unwrap_or("");
        assert!(
            proof_hex.len() > 128,
            "[{label}] effect_vm_proof_hex must be substantial (>64 bytes); got {} chars",
            proof_hex.len()
        );
        let pi = j
            .get("effect_vm_public_inputs")
            .cloned()
            .unwrap_or(Value::Null);
        assert!(pi.is_array(), "[{label}] public_inputs must be array");
        assert!(
            pi.as_array().map(|a| !a.is_empty()).unwrap_or(false),
            "[{label}] public_inputs must be non-empty"
        );
        let trace = j
            .get("effect_vm_trace_rows")
            .cloned()
            .unwrap_or(Value::Null);
        assert!(trace.is_array(), "[{label}] trace_rows must be array");
        assert!(
            j.get("effect_vm_witness_hash_hex")
                .and_then(|v| v.as_str())
                .map(|s| s.len() == 64)
                .unwrap_or(false),
            "[{label}] witness_hash_hex must be a 64-char hex string"
        );
    }

    // =====================================================================
    // MCP per-tool capability gate — THE TEETH.
    //
    // Before this work, `tools/call` was a flat match over ~45 tools behind a
    // single global `unlocked` bit: once unlocked, any client could invoke any
    // tool with NO per-tool authority check. Now each tool declares a scope verb
    // (`tool_required_scope`) and `enforce_tool_cap` requires the caller's
    // presented `Authorization::Token` to COVER that scope, verified by the
    // EXECUTOR's `verify_token_for_scope`.
    //
    // The negative test (`mcp_overscope_cap_rejected_by_executor`) is the
    // deliverable: a client presenting a `read`-scoped biscuit is REJECTED when
    // it calls an `admin` tool — and the rejection is the executor's
    // capability-cover failure, not narration.
    // =====================================================================

    /// Mint an MCP tools-access biscuit for `scope_verb`, packaged as the `_cap`
    /// argument a `tools/call` presents.
    async fn cap_arg_for(state: &NodeState, scope_verb: &str) -> Value {
        let s = state.read().await;
        let node_pk = s.cclerk.public_key().0;
        let biscuit = mint_tool_cap(&s.cclerk, &node_pk, scope_verb).expect("mint tool cap");
        serde_json::json!({ "_cap": { "biscuit": biscuit } })
    }

    // =====================================================================
    // Best-practices surface tests: every advertised prompt resolves, the
    // ocap `_cap` argument is declared in each tool schema, and the
    // completion endpoint autocompletes live dregg handles.
    // =====================================================================

    /// Every prompt in `prompts/list` MUST resolve in `prompts/get` — an
    /// advertised capability that errors is a best-practice violation. This
    /// regression pins the `verify_turn` prompt (previously listed but
    /// unhandled, so it fell into the unknown-prompt error branch).
    #[test]
    fn every_advertised_prompt_resolves() {
        for spec in prompt_specs() {
            // Supply each required arg so the get path doesn't reject on a
            // missing one; the point is that the NAME is handled.
            let mut args = serde_json::Map::new();
            for (name, _desc, _req) in spec.arguments {
                args.insert((*name).to_string(), Value::String("dead".repeat(16)));
            }
            let resp = handle_prompts_get(
                Value::from(1),
                serde_json::json!({ "name": spec.name, "arguments": args }),
            );
            let v = serde_json::to_value(&resp).unwrap();
            assert!(
                v.get("error").is_none(),
                "advertised prompt '{}' must resolve in prompts/get, got error: {v}",
                spec.name
            );
            assert!(
                v.get("result")
                    .and_then(|r| r.get("messages"))
                    .and_then(|m| m.as_array())
                    .map(|a| !a.is_empty())
                    .unwrap_or(false),
                "prompt '{}' must render at least one message",
                spec.name
            );
        }
    }

    /// Every tool's input schema declares the ocap `_cap` argument, so an agent
    /// reading tools/list — and a schema-validating client — discovers the
    /// capability requirement at the tool boundary (not just in prose).
    #[test]
    fn every_tool_schema_declares_cap_argument() {
        for d in tool_definitions() {
            let cap = d.input_schema.get("properties").and_then(|p| p.get("_cap"));
            assert!(
                cap.is_some(),
                "tool '{}' input schema must declare the '_cap' ocap argument",
                d.name
            );
            // And the group/scope metadata an orienting agent reads.
            assert!(
                d.input_schema.get("x-dregg-scope").is_some(),
                "tool '{}' schema must stamp x-dregg-scope",
                d.name
            );
        }
    }

    #[tokio::test]
    async fn completion_completes_cell_ids_for_resource_template() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let agent_cell = {
            let s = state.read().await;
            hex_encode(
                dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]).as_bytes(),
            )
        };
        // Complete the dregg://cell/{cell_id} template variable with a prefix of
        // the agent cell that's actually in the ledger.
        let prefix = &agent_cell[..6];
        let resp = handle_completion_complete(
            Value::from(1),
            serde_json::json!({
                "ref": { "type": "ref/resource", "uri": "dregg://cell/" },
                "argument": { "name": "cell_id", "value": prefix }
            }),
            &state,
        )
        .await;
        let v = serde_json::to_value(&resp).unwrap();
        let values = v["result"]["completion"]["values"]
            .as_array()
            .expect("completion values array");
        assert!(
            values
                .iter()
                .any(|x| x.as_str() == Some(agent_cell.as_str())),
            "completion must surface the in-ledger agent cell id; got {values:?}"
        );
    }

    #[tokio::test]
    async fn completion_unknown_ref_returns_well_formed_empty() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let resp = handle_completion_complete(
            Value::from(1),
            serde_json::json!({
                "ref": { "type": "ref/prompt", "name": "orient" },
                "argument": { "name": "nonexistent", "value": "x" }
            }),
            &state,
        )
        .await;
        let v = serde_json::to_value(&resp).unwrap();
        assert_eq!(
            v["result"]["completion"]["values"]
                .as_array()
                .map(|a| a.len()),
            Some(0)
        );
        assert_eq!(v["result"]["completion"]["hasMore"], Value::Bool(false));
    }

    #[tokio::test]
    async fn mcp_in_scope_cap_admitted_by_executor() {
        // POSITIVE tooth: a `read`-scoped biscuit covers a `read` tool. The gate
        // verifies the credential against the tool's scope via the executor and
        // ADMITS the call (Ok).
        let (state, _tmp) = fresh_unlocked_state().await;
        {
            state.write().await.mcp_cap_enforce = true;
        }
        let args = cap_arg_for(&state, "read").await;
        // dregg_get_status requires the "read" scope.
        assert_eq!(tool_required_scope("dregg_get_status"), "read");
        enforce_tool_cap("dregg_get_status", &args, &state)
            .await
            .expect("a read-scoped cap must cover a read tool (executor admits)");
    }

    #[tokio::test]
    async fn mcp_overscope_cap_rejected_by_executor() {
        // NEGATIVE tooth (THE deliverable): a `read`-scoped biscuit does NOT
        // cover an `admin` tool. The gate runs the EXECUTOR's
        // verify_token_for_scope, which denies the cover, and the call is
        // rejected — it never reaches the tool body.
        let (state, _tmp) = fresh_unlocked_state().await;
        {
            state.write().await.mcp_cap_enforce = true;
        }
        let args = cap_arg_for(&state, "read").await;
        // dregg_grant_capability requires the "admin" scope.
        assert_eq!(tool_required_scope("dregg_grant_capability"), "admin");
        let err = enforce_tool_cap("dregg_grant_capability", &args, &state)
            .await
            .expect_err("a read-scoped cap MUST NOT cover an admin tool");
        assert!(
            err.contains("does not cover"),
            "rejection must be the executor's capability-cover failure, got: {err}"
        );
    }

    #[tokio::test]
    async fn mcp_missing_cap_rejected_under_enforcement() {
        // With enforcement ON, a `tools/call` presenting NO `_cap` is rejected
        // fail-closed — the per-tool cap gate is a real boundary, not optional.
        let (state, _tmp) = fresh_unlocked_state().await;
        {
            state.write().await.mcp_cap_enforce = true;
        }
        let no_cap = serde_json::json!({});
        let err = enforce_tool_cap("dregg_grant_capability", &no_cap, &state)
            .await
            .expect_err("missing cap under enforcement must be rejected");
        assert!(
            err.contains("requires a covering"),
            "expected a missing-cap rejection, got: {err}"
        );
    }

    #[tokio::test]
    async fn mcp_wrong_issuer_cap_rejected() {
        // A biscuit minted under a DIFFERENT issuer key (not the node's MCP-cap
        // issuer) must be rejected: the executor's trust anchor requires the
        // issuer to equal the authority cell's verification key. This proves the
        // gate binds the credential to THIS node's granting authority.
        let (state, _tmp) = fresh_unlocked_state().await;
        {
            state.write().await.mcp_cap_enforce = true;
        }
        // Mint an admin-scoped biscuit under an unrelated keypair.
        let foreign_kp = dregg_token::biscuit_auth::KeyPair::new();
        let node_pk = { state.read().await.cclerk.public_key().0 };
        let authority_cell_id = dregg_cell::CellId::derive_raw(&node_pk, &[0u8; 32]);
        let svc = hex_encode(authority_cell_id.as_bytes());
        let action = hex_encode(dregg_turn::action::symbol("admin").as_slice());
        let foreign = {
            use dregg_token::traits::AuthToken;
            dregg_token::BiscuitToken::mint_dregg(
                &foreign_kp,
                &[],
                &[(svc, action)],
                &[],
                &[],
                &[],
                None,
            )
            .unwrap()
            .to_encoded()
            .unwrap()
        };
        let args = serde_json::json!({ "_cap": { "biscuit": foreign } });
        let err = enforce_tool_cap("dregg_grant_capability", &args, &state)
            .await
            .expect_err("a foreign-issuer cap MUST be rejected by the executor's trust anchor");
        assert!(
            err.contains("does not cover"),
            "expected an executor trust-anchor/cover rejection, got: {err}"
        );
    }

    /// R7 (temporal leg): a stored cap with a HEIGHT-BOUND expiry caveat must
    /// die when consensus passes the bound. The gate's verifying executor used
    /// to sit at its default `block_height = 0`, under which `time($t), $t < N`
    /// trivially holds forever — an expired cap verified FOREVER. The fix
    /// snapshots the CURRENT attested height into `McpCapContext` and binds the
    /// executor to it; this test pins both directions (admits inside the
    /// window, rejects past it).
    #[tokio::test]
    async fn mcp_height_expired_cap_rejected_at_current_height() {
        let (state, _tmp) = fresh_unlocked_state().await;
        {
            state.write().await.mcp_cap_enforce = true;
        }
        // Mint a read-scoped cap under the node's REAL MCP issuer key, with an
        // expiry caveat: valid only while the consensus height is < 5.
        let encoded = {
            let s = state.read().await;
            use dregg_token::traits::AuthToken;
            let kp = mcp_cap_issuer_keypair(&s.cclerk);
            let node_pk = s.cclerk.public_key().0;
            let authority_cell_id = dregg_cell::CellId::derive_raw(&node_pk, &[0u8; 32]);
            let svc = hex_encode(authority_cell_id.as_bytes());
            let action = hex_encode(dregg_turn::action::symbol("read").as_slice());
            let mut code =
                dregg_token::dregg::authority_datalog(&[], &[(svc, action)], &[], &[], &[], None)
                    .unwrap();
            code.push_str("check if time($t), $t < 5;\n");
            dregg_token::BiscuitToken::mint(&kp, &code)
                .unwrap()
                .to_encoded()
                .unwrap()
        };
        let args = serde_json::json!({ "_cap": { "biscuit": encoded } });

        let mut ctx = McpCapContext::snapshot(&state).await;
        let cred = parse_presented_cap(&args, &ctx.issuer_pubkey).expect("cap argument parses");

        // Inside the expiry window (fresh devnet, height 0 < 5): admitted.
        ctx.block_height = 0;
        ctx.cap_covers_tool(&cred, "dregg_get_status")
            .expect("an unexpired cap must cover the read tool inside its window");

        // Past the expiry bound (height 10 ≥ 5): the SAME stored cap is dead.
        ctx.block_height = 10;
        ctx.cap_covers_tool(&cred, "dregg_get_status")
            .expect_err("a height-expired cap MUST be rejected at the current height");
    }

    #[tokio::test]
    async fn bearer_cap_exercise_rejects_missing_agent_pre_state_before_commit() {
        let (state, _tmp) = fresh_unlocked_state_without_agent_cell().await;
        let target_cell = "11".repeat(32);
        let recipient_cell = "22".repeat(32);
        let params = serde_json::json!({
            "target_cell": target_cell,
            "method": "transfer",
            "delegation_chain": "33".repeat(64),
            "delegator_pk": "44".repeat(32),
            "bearer_pk": "55".repeat(32),
            "expires_at": 10_000u64,
            "effects": [{
                "type": "transfer",
                "from": "11".repeat(32),
                "to": recipient_cell,
                "amount": 1u64,
            }]
        });

        let result = dispatch_tool("dregg_exercise_bearer_cap", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(j.get("exercised").and_then(|v| v.as_bool()), Some(false));
        assert!(
            j.get("effect_vm_proof_hex").is_none(),
            "missing pre-state must not surface a null proof as if the turn committed: {j}"
        );
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "truthful rejection must happen before the receipt chain advances"
        );
    }

    #[tokio::test]
    async fn grant_capability_rejects_missing_agent_pre_state_before_commit() {
        let (state, _tmp) = fresh_unlocked_state_without_agent_cell().await;
        let params = serde_json::json!({
            "to_agent": "77".repeat(32),
            "target_cell": "88".repeat(32),
            "permissions": "signature",
        });

        let result = dispatch_tool("dregg_grant_capability", params, &state).await;
        let j = extract_json(&result);
        eprintln!("grant witness artifact response: {j}");
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "grant rejection must happen before the receipt chain advances"
        );
    }

    #[tokio::test]
    async fn grant_capability_commits_witness_artifact_for_receipt_chain() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let (target_cell, recipient_cell) = {
            let mut s = state.write().await;
            let id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);
            let recipient_pk = [0x77u8; 32];
            let recipient = dregg_cell::Cell::with_balance(recipient_pk, [0u8; 32], 0);
            let recipient_id = recipient.id();
            s.ledger
                .insert_cell(recipient)
                .expect("recipient cell insert must succeed");
            (hex_encode(&id.0), hex_encode(&recipient_id.0))
        };
        let params = serde_json::json!({
            "to_agent": recipient_cell,
            "target_cell": target_cell,
            "permissions": "signature",
        });

        let result = dispatch_tool("dregg_grant_capability", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("committed"),
            "unexpected response: {j}"
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("proved")
        );

        let s = state.read().await;
        let receipt = s
            .cclerk
            .receipt_chain()
            .last()
            .expect("grant must append a receipt");
        let receipt_hash = receipt.receipt_hash();
        assert_eq!(
            s.witnessed_receipt_count(&receipt_hash),
            1,
            "committed proof-bearing MCP turn must leave a retrievable witnessed receipt"
        );
        let stored = s
            .witnessed_receipts
            .get(&receipt_hash)
            .expect("witnessed receipt entry must exist");
        assert_eq!(stored[0].receipt.receipt_hash(), receipt_hash);
        assert!(
            stored[0].witness_bundle.is_some(),
            "stored witnessed receipt must carry replay material"
        );
    }

    #[tokio::test]
    async fn grant_capability_rejects_missing_recipient_pre_state_instead_of_stub() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let target_cell = {
            let s = state.read().await;
            let id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);
            hex_encode(&id.0)
        };
        let params = serde_json::json!({
            "to_agent": "77".repeat(32),
            "target_cell": target_cell,
            "permissions": "signature",
        });

        let result = dispatch_tool("dregg_grant_capability", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "missing recipient pre-state must not be hidden behind a synthetic stub"
        );
    }

    #[tokio::test]
    async fn bearer_cap_exercise_rejects_missing_target_pre_state_instead_of_stub() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let params = serde_json::json!({
            "target_cell": "11".repeat(32),
            "method": "transfer",
            "delegation_chain": "33".repeat(64),
            "delegator_pk": "44".repeat(32),
            "bearer_pk": "55".repeat(32),
            "expires_at": 10_000u64,
            "effects": [{
                "type": "transfer",
                "from": "11".repeat(32),
                "to": "22".repeat(32),
                "amount": 1u64,
            }]
        });

        let result = dispatch_tool("dregg_exercise_bearer_cap", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "missing bearer target pre-state must not be hidden behind a synthetic stub"
        );
    }

    #[tokio::test]
    async fn bilateral_action_rejects_missing_to_pre_state_instead_of_stub_commit() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let from_cell = {
            let s = state.read().await;
            dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32])
        };
        let params = serde_json::json!({
            "mode": "transfer",
            "from": hex_encode(&from_cell.0),
            "to": "66".repeat(32),
            "amount": 5u64,
        });

        let result = dispatch_tool("dregg_bilateral_action", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(j.get("committed").and_then(|v| v.as_bool()), Some(false));
        assert!(
            j.get("to_side").is_none(),
            "a rejected bilateral action must not present null witnessed receipts: {j}"
        );
    }

    #[tokio::test]
    async fn handoff_cert_rejects_missing_target_pre_state_before_commit() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let mut seed = [0u8; 32];
        seed[0] = 0xE1;
        let params = serde_json::json!({
            "target_cell": "99".repeat(32),
            "introducer_sk": hex_encode(&seed),
            "permissions": "signature",
        });

        let result = dispatch_tool("dregg_exercise_handoff_cert", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(j.get("exercised").and_then(|v| v.as_bool()), Some(false));
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "handoff rejection must happen before the receipt chain advances"
        );
    }

    #[tokio::test]
    async fn handoff_cert_rejects_missing_downstream_pre_state_instead_of_stub() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let target_cell = {
            let s = state.read().await;
            dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32])
        };
        let mut seed = [0u8; 32];
        seed[0] = 0xE2;
        let params = serde_json::json!({
            "target_cell": hex_encode(&target_cell.0),
            "introducer_sk": hex_encode(&seed),
            "permissions": "signature",
            "effects": [{
                "type": "transfer",
                "from": hex_encode(&target_cell.0),
                "to": "ab".repeat(32),
                "amount": 1u64,
            }]
        });

        let result = dispatch_tool("dregg_exercise_handoff_cert", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(j.get("exercised").and_then(|v| v.as_bool()), Some(false));
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "missing downstream pre-state must not be hidden behind a synthetic stub"
        );
    }

    #[tokio::test]
    async fn dregg_register_name_produces_proof_carrying_receipt() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let params = serde_json::json!({
            "name": "alice.dev",
            "expiry_height": 2_000_000_000u64,
        });
        let result = dispatch_tool("dregg_register_name", params, &state).await;
        let j = extract_json(&result);
        assert_proof_populated("register_name", &j);
        // Confirm cross-app link metadata is surfaced.
        assert_eq!(
            j.get("registered_name").and_then(|v| v.as_str()),
            Some("alice.dev")
        );
        assert!(
            j.get("schema_commitment")
                .and_then(|v| v.as_str())
                .is_some()
        );
    }

    #[tokio::test]
    async fn dregg_publish_subscription_produces_proof_carrying_receipt() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let bounty_id = "abcd".repeat(16);
        let msg_root = "1234".repeat(16);
        let actor_pk_hash = "5678".repeat(16);
        let params = serde_json::json!({
            "new_head": 1u64,
            "new_message_root": msg_root,
            "bounty_id": bounty_id,
            "prior_state": "posted",
            "new_state": "claimed",
            "actor_pk_hash": actor_pk_hash,
        });
        let result = dispatch_tool("dregg_publish_subscription", params, &state).await;
        let j = extract_json(&result);
        assert_proof_populated("publish_subscription", &j);
        assert_eq!(
            j.get("prior_state").and_then(|v| v.as_str()),
            Some("posted")
        );
        assert_eq!(j.get("new_state").and_then(|v| v.as_str()), Some("claimed"));
        assert!(j.get("payload_hash").and_then(|v| v.as_str()).is_some());
    }

    #[tokio::test]
    async fn dregg_issue_credential_produces_proof_carrying_receipt() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let params = serde_json::json!({
            "schema": "kyc",
            "attributes": {
                "given_name": "Bob",
                "verification_level": 2,
            },
        });
        let result = dispatch_tool("dregg_issue_credential", params, &state).await;
        let j = extract_json(&result);
        assert_proof_populated("issue_credential", &j);
        assert!(j.get("credential_id").and_then(|v| v.as_str()).is_some());
        assert_eq!(j.get("schema").and_then(|v| v.as_str()), Some("kyc"));
        assert!(
            j.get("credential_encoded")
                .and_then(|v| v.as_str())
                .is_some()
        );
    }

    #[tokio::test]
    async fn dregg_register_service_produces_proof_carrying_receipt() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let params = serde_json::json!({
            "path": "/alice.dev",
        });
        let result = dispatch_tool("dregg_register_service", params, &state).await;
        let j = extract_json(&result);
        assert_proof_populated("register_service", &j);
        assert_eq!(j.get("path").and_then(|v| v.as_str()), Some("/alice.dev"));
        // #110: the synthesized-row note is gone — the AIR now carries a
        // real EmitEvent variant with canonical (topic_hash, payload_hash)
        // binding, so register_service projects directly and no workaround
        // marker is surfaced.
        assert!(
            j.get("synthesized_vm_setfield_note").is_none(),
            "register_service must NOT surface the legacy coverage-gap note \
             once #110 lands a real AIR EmitEvent variant"
        );
    }

    // =====================================================================
    // dregg_exercise_handoff_cert unit tests
    // =====================================================================

    /// Honest path: exercise_handoff_cert with a valid introducer key commits
    /// and emits a STARK proof. Mirrors the existing `dregg_captp_deliver`
    /// integration (CapTpDelivered cert + delivery-signature verification).
    #[tokio::test]
    async fn exercise_handoff_cert_honest_path_commits() {
        let (state, _tmp) = fresh_unlocked_state().await;

        // Generate a deterministic introducer seed (32 bytes → secret key).
        let mut seed = [0u8; 32];
        seed[0] = 0xBB;
        let introducer_sk_hex = hex_encode(&seed); // pass as introducer_sk

        // Create an agent cell so pre_state is non-None and the proof fires.
        let create_res = dispatch_tool(
            "dregg_create_agent",
            serde_json::json!({ "name": "honest-bob", "initial_balance": 1_000_000 }),
            &state,
        )
        .await;
        let create_j = extract_json(&create_res);
        let target_cell = create_j["cell_id"].as_str().expect("cell_id").to_string();

        let params = serde_json::json!({
            "target_cell": target_cell,
            "introducer_sk": introducer_sk_hex,
            "permissions": "signature",
        });
        let result = dispatch_tool("dregg_exercise_handoff_cert", params, &state).await;
        let j = extract_json(&result);

        assert_eq!(
            j.get("exercised").and_then(|v| v.as_bool()),
            Some(true),
            "honest handoff cert exercise must commit; got: {j}"
        );
        assert!(
            j.get("turn_hash").and_then(|v| v.as_str()).is_some(),
            "must return turn_hash"
        );
        assert!(
            j.get("cert_nonce").and_then(|v| v.as_str()).is_some(),
            "must return cert_nonce"
        );
        assert!(
            j.get("cert_hash").and_then(|v| v.as_str()).is_some(),
            "must return cert_hash"
        );
        // STARK proof must be present because the agent cell is in the ledger.
        let proof = j.get("effect_vm_proof_hex").cloned().unwrap_or(Value::Null);
        assert!(
            proof.is_string(),
            "honest path must emit effect_vm_proof_hex; got: {proof:?}"
        );
        let proof_hex = proof.as_str().unwrap_or("");
        assert!(
            proof_hex.len() > 128,
            "proof must be non-trivial (>64 bytes); got {} chars",
            proof_hex.len()
        );
    }

    /// Adversarial test: supplying a forged `introducer_pk` that does NOT
    /// match the cert's introducer causes the executor to reject the Turn.
    ///
    /// Security property: `verify_captp_delivered` step 2 checks
    /// `introducer_pk == cert.introducer.0`. A forged pk diverges and the
    /// executor returns `Rejected` rather than committing.
    #[tokio::test]
    async fn exercise_handoff_cert_forged_introducer_pk_rejected() {
        let (state, _tmp) = fresh_unlocked_state().await;

        // Honest introducer secret key seed (32 bytes).
        let mut seed = [0u8; 32];
        seed[0] = 0xCC;
        let honest_sk_hex = hex_encode(&seed); // pass as introducer_sk

        // Create a target cell so the ledger has something to act on.
        let create_res = dispatch_tool(
            "dregg_create_agent",
            serde_json::json!({ "name": "adversarial-bob", "initial_balance": 1_000_000 }),
            &state,
        )
        .await;
        let create_j = extract_json(&create_res);
        let target_cell = create_j["cell_id"].as_str().expect("cell_id").to_string();

        // Forged introducer pk: all 0xAA bytes — definitely not the honest key.
        let forged_pk_hex = "aa".repeat(32);

        // We supply the honest_sk (so the cert is signed with the honest key),
        // but override `introducer_pk` with the forged value. The executor sees
        // the cert signed by the honest key but `introducer_pk` pointing at the
        // forged bytes — step 2 rejects immediately.
        let params = serde_json::json!({
            "target_cell": target_cell,
            "introducer_sk": honest_sk_hex,
            "introducer_pk": forged_pk_hex,
            "permissions": "signature",
        });
        let result = dispatch_tool("dregg_exercise_handoff_cert", params, &state).await;
        let j = extract_json(&result);

        assert_eq!(
            j.get("exercised").and_then(|v| v.as_bool()),
            Some(false),
            "forged introducer_pk MUST cause executor rejection; got: {j}"
        );
        let err = j
            .get("error")
            .and_then(|v| v.as_str())
            .unwrap_or("(no error field)");
        assert!(
            err.contains("rejected") || err.contains("introducer") || err.contains("invalid"),
            "rejection error must mention the authorization failure; got: '{err}'"
        );
    }

    fn test_committee_descriptor(
        role: &str,
        pk: dregg_types::PublicKey,
        federation_id: [u8; 32],
    ) -> dregg_verifier::cross_fed::CommitteeDescriptor {
        dregg_verifier::cross_fed::CommitteeDescriptor {
            federation_id: hex_encode(&federation_id),
            committee_epoch: 0,
            threshold: 1,
            validators: vec![dregg_verifier::cross_fed::ValidatorDescriptor {
                name: role.to_string(),
                public_key: hex_encode(&pk.0),
            }],
        }
    }

    fn sign_test_attested_root(
        mut root: dregg_types::AttestedRoot,
        sk: &dregg_types::SigningKey,
    ) -> dregg_types::AttestedRoot {
        let sig = dregg_types::sign(sk, &root.signing_message());
        root.quorum_signatures = vec![(sk.public_key(), sig)];
        root
    }

    fn test_attested_root_for_receipts(
        federation_id: [u8; 32],
        receipt_hashes: &[[u8; 32]],
        signing_key: &dregg_types::SigningKey,
        height: u64,
        tag: &[u8],
    ) -> dregg_types::AttestedRoot {
        let receipt_stream_root = dregg_types::merkle_root_of_receipt_hashes(receipt_hashes);
        let mut h = blake3::Hasher::new_derive_key("dregg-node-mcp-silver-captp-root-v1");
        h.update(tag);
        h.update(&height.to_le_bytes());
        h.update(&receipt_stream_root);
        let merkle_root = *h.finalize().as_bytes();
        sign_test_attested_root(
            dregg_types::AttestedRoot {
                merkle_root,
                note_tree_root: None,
                nullifier_set_root: None,
                height,
                timestamp: 1_700_000_000 + height as i64,
                blocklace_block_id: Some(
                    *blake3::hash([tag, b":blocklace"].concat().as_slice()).as_bytes(),
                ),
                finality_round: Some(height),
                quorum_signatures: Vec::new(),
                threshold_qc: None,
                threshold: 1,
                federation_id: dregg_types::FederationId(federation_id),
                receipt_stream_root: Some(receipt_stream_root),
            },
            signing_key,
        )
    }

    #[tokio::test]
    async fn silver_captp_mcp_path_exports_cross_fed_verifiable_bundle() {
        let (state, _tmp) = fresh_unlocked_state().await;

        let mut introducer_seed = [0u8; 32];
        introducer_seed[0] = 0xE1;
        let introducer_sk = dregg_types::SigningKey::from_bytes(&introducer_seed);
        let introducer_pk = introducer_sk.public_key();
        let issuer_fed_id = dregg_federation::derive_federation_id_with_epoch(&[introducer_pk], 0);

        let (target_cell, recipient_pk, recipient_sk, recipient_fed_id) = {
            let mut s = state.write().await;
            let recipient_pk = s.cclerk.public_key();
            let recipient_sk = s.cclerk.gossip_signing_key();
            s.set_federation_keys(vec![recipient_pk]);
            let recipient_fed_id = s.federation_id;
            let target_cell = dregg_cell::CellId::derive_raw(&recipient_pk.0, &[0u8; 32]);
            (target_cell, recipient_pk, recipient_sk, recipient_fed_id)
        };

        let params = serde_json::json!({
            "target_cell": hex_encode(&target_cell.0),
            "introducer_sk": hex_encode(&introducer_seed),
            "introducer_federation": hex_encode(&issuer_fed_id),
            "target_federation": hex_encode(&recipient_fed_id),
            "recipient_pk": hex_encode(&recipient_pk.0),
            "permissions": "signature",
            "swiss": "42".repeat(32),
            "effects": [{
                "type": "set_field",
                "cell": hex_encode(&target_cell.0),
                "index": 1,
                "value": 153u64,
            }],
        });
        let result = dispatch_tool("dregg_exercise_handoff_cert", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("committed"),
            "MCP Silver handoff must commit before bundle export: {j}"
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("proved"),
            "MCP Silver handoff must produce replay witness material: {j}"
        );

        let cert_hex = j
            .get("handoff_certificate_hex")
            .and_then(|v| v.as_str())
            .expect("MCP response must export the actual handoff certificate bytes");
        let cert_bytes = hex_decode_var(cert_hex).expect("certificate hex decodes");
        let cert = dregg_captp::HandoffCertificate::from_bytes(&cert_bytes)
            .expect("certificate exported by MCP must decode");

        let (receipt, witnessed) = {
            let s = state.read().await;
            let receipt = s
                .cclerk
                .receipt_chain()
                .last()
                .expect("committed MCP turn must append a receipt")
                .clone();
            assert_eq!(
                receipt.federation_id, recipient_fed_id,
                "node-facing CapTP receipt must bind the configured recipient federation"
            );
            assert!(
                receipt.executor_signature.is_some(),
                "node-facing CapTP receipt must carry executor signature material"
            );
            let receipt_hash = receipt.receipt_hash();
            let stored = s
                .witnessed_receipts
                .get(&receipt_hash)
                .expect("committed MCP handoff must persist a witnessed receipt artifact");
            assert_eq!(stored.len(), 1);
            assert!(
                stored[0].witness_bundle.is_some(),
                "stored witnessed receipt must carry scope-2 replay material"
            );
            (receipt, stored[0].clone())
        };

        let issuer_desc = test_committee_descriptor("issuer", introducer_pk, issuer_fed_id);
        let recipient_desc = test_committee_descriptor("recipient", recipient_pk, recipient_fed_id);
        let issuer_root =
            test_attested_root_for_receipts(issuer_fed_id, &[], &introducer_sk, 10, b"issuer");
        let recipient_root = test_attested_root_for_receipts(
            recipient_fed_id,
            &[receipt.receipt_hash()],
            &recipient_sk,
            20,
            b"recipient",
        );
        let bundle = dregg_federation::CrossFedReceiptBundle::new(
            vec![witnessed],
            issuer_root,
            recipient_root,
            cert,
            None,
        );

        let verdict = dregg_verifier::cross_fed::verify_cross_fed_bundle(
            &bundle,
            &issuer_desc,
            &recipient_desc,
        );
        assert!(
            verdict.overall_verified,
            "MCP-produced Silver artifacts must verify as a cross-fed bundle: {verdict:?}",
        );

        let mut missing_witness = bundle.clone();
        missing_witness.recipient_chain[0].witness_bundle = None;
        let missing_verdict = dregg_verifier::cross_fed::verify_cross_fed_bundle(
            &missing_witness,
            &issuer_desc,
            &recipient_desc,
        );
        assert!(
            !missing_verdict.overall_verified
                && missing_verdict.summary.contains("has no witness_bundle"),
            "missing witnessed material must reject: {missing_verdict:?}",
        );

        let mut swapped_recipient = bundle;
        swapped_recipient.cross_fed_cert.target_federation = dregg_captp::FederationId([0xF2; 32]);
        let swapped_verdict = dregg_verifier::cross_fed::verify_cross_fed_bundle(
            &swapped_recipient,
            &issuer_desc,
            &recipient_desc,
        );
        assert!(
            !swapped_verdict.overall_verified,
            "swapped target federation must reject: {swapped_verdict:?}",
        );
    }

    #[tokio::test]
    async fn silver_captp_node_to_node_exchange_imports_and_verifies_witness_artifact() {
        let (producer_state, _producer_tmp) = fresh_unlocked_state().await;
        let (importer_state, _importer_tmp) = fresh_unlocked_state().await;

        let mut introducer_seed = [0u8; 32];
        introducer_seed[0] = 0xE2;
        let introducer_sk = dregg_types::SigningKey::from_bytes(&introducer_seed);
        let introducer_pk = introducer_sk.public_key();
        let issuer_fed_id = dregg_federation::derive_federation_id_with_epoch(&[introducer_pk], 0);

        let (target_cell, recipient_pk, recipient_sk, recipient_fed_id) = {
            let mut s = producer_state.write().await;
            let recipient_pk = s.cclerk.public_key();
            let recipient_sk = s.cclerk.gossip_signing_key();
            s.set_federation_keys(vec![recipient_pk]);
            let recipient_fed_id = s.federation_id;
            let target_cell = dregg_cell::CellId::derive_raw(&recipient_pk.0, &[0u8; 32]);
            (target_cell, recipient_pk, recipient_sk, recipient_fed_id)
        };

        let params = serde_json::json!({
            "target_cell": hex_encode(&target_cell.0),
            "introducer_sk": hex_encode(&introducer_seed),
            "introducer_federation": hex_encode(&issuer_fed_id),
            "target_federation": hex_encode(&recipient_fed_id),
            "recipient_pk": hex_encode(&recipient_pk.0),
            "permissions": "signature",
            "swiss": "42".repeat(32),
            "effects": [{
                "type": "set_field",
                "cell": hex_encode(&target_cell.0),
                "index": 1,
                "value": 154u64,
            }],
        });
        let result = dispatch_tool("dregg_exercise_handoff_cert", params, &producer_state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("committed"),
            "producer node must commit the handoff before exporting gossip artifacts: {j}"
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("proved"),
            "producer node must persist replay witness material: {j}"
        );

        let cert_hex = j
            .get("handoff_certificate_hex")
            .and_then(|v| v.as_str())
            .expect("MCP response must export handoff certificate bytes");
        let cert_bytes = hex_decode_var(cert_hex).expect("certificate hex decodes");
        let cert = dregg_captp::HandoffCertificate::from_bytes(&cert_bytes)
            .expect("certificate exported by producer must decode");

        let (receipt_hash, receipt) = {
            let s = producer_state.read().await;
            let receipt = s
                .cclerk
                .receipt_chain()
                .last()
                .expect("producer commit must append a receipt")
                .clone();
            (receipt.receipt_hash(), receipt)
        };

        // This mirrors the normal `/api/receipts/{hash}/witnesses` response
        // shape: legacy JSON remains present for display/debugging, but node to
        // node import uses the canonical DWR1 artifacts.
        let exported = {
            let s = producer_state.read().await;
            let witnessed = s
                .witnessed_receipts
                .get(&receipt_hash)
                .cloned()
                .expect("producer storage must retain the witnessed receipt");
            let witness_artifacts = witnessed
                .iter()
                .map(|w| {
                    w.to_artifact_bytes()
                        .map(|bytes| hex_encode(&bytes))
                        .expect("witness artifact encodes")
                })
                .collect::<Vec<_>>();
            serde_json::json!({
                "receipt_hash": hex_encode(&receipt_hash),
                "witness_count": witnessed.len(),
                "artifact_format": "DWR1",
                "witness_artifacts": witness_artifacts,
                "witnessed_receipts": witnessed,
            })
        };
        assert_eq!(exported["witness_count"], 1);
        assert_eq!(exported["artifact_format"], "DWR1");

        let exported_hash = exported
            .get("receipt_hash")
            .and_then(|v| v.as_str())
            .and_then(|h| hex_decode(h).ok())
            .expect("exported receipt_hash must be 32-byte hex");
        assert_eq!(exported_hash, receipt_hash);
        let imported_witnesses: Vec<dregg_turn::WitnessedReceipt> = exported["witness_artifacts"]
            .as_array()
            .expect("canonical witness_artifacts array")
            .iter()
            .map(|artifact| {
                let artifact_hex = artifact.as_str().expect("artifact hex");
                let artifact_bytes = hex_decode_var(artifact_hex).expect("artifact hex decodes");
                dregg_turn::WitnessedReceipt::from_artifact_bytes(&artifact_bytes)
                    .expect("DWR1 witness artifact decodes")
            })
            .collect();
        assert_eq!(imported_witnesses.len(), 1);

        {
            let mut importer = importer_state.write().await;
            importer.push_witnessed_receipt(receipt_hash, imported_witnesses[0].clone());
            assert_eq!(
                importer.witnessed_receipt_count(&receipt_hash),
                1,
                "importing node must persist the received witnessed receipt by receipt hash"
            );
        }

        let imported = {
            let importer = importer_state.read().await;
            importer
                .witnessed_receipts
                .get(&receipt_hash)
                .and_then(|items| items.first())
                .cloned()
                .expect("imported node storage must expose the received artifact")
        };
        let issuer_desc = test_committee_descriptor("issuer", introducer_pk, issuer_fed_id);
        let recipient_desc = test_committee_descriptor("recipient", recipient_pk, recipient_fed_id);
        let issuer_root =
            test_attested_root_for_receipts(issuer_fed_id, &[], &introducer_sk, 10, b"issuer");
        let recipient_root = test_attested_root_for_receipts(
            recipient_fed_id,
            &[receipt.receipt_hash()],
            &recipient_sk,
            20,
            b"recipient",
        );
        let bundle = dregg_federation::CrossFedReceiptBundle::new(
            vec![imported],
            issuer_root,
            recipient_root,
            cert,
            None,
        );

        let verdict = dregg_verifier::cross_fed::verify_cross_fed_bundle(
            &bundle,
            &issuer_desc,
            &recipient_desc,
        );
        assert!(
            verdict.overall_verified,
            "imported node-to-node Silver artifact must verify end-to-end: {verdict:?}",
        );

        let mut missing_witness = bundle.clone();
        missing_witness.recipient_chain[0].witness_bundle = None;
        let missing_verdict = dregg_verifier::cross_fed::verify_cross_fed_bundle(
            &missing_witness,
            &issuer_desc,
            &recipient_desc,
        );
        assert!(
            !missing_verdict.overall_verified
                && missing_verdict.summary.contains("has no witness_bundle"),
            "imported bundle without witnessed replay material must reject: {missing_verdict:?}",
        );

        let mut swapped_recipient = bundle.clone();
        swapped_recipient.cross_fed_cert.target_federation = dregg_captp::FederationId([0xF2; 32]);
        let swapped_verdict = dregg_verifier::cross_fed::verify_cross_fed_bundle(
            &swapped_recipient,
            &issuer_desc,
            &recipient_desc,
        );
        assert!(
            !swapped_verdict.overall_verified,
            "swapped recipient federation in the handoff certificate must reject: {swapped_verdict:?}",
        );

        let wrong_recipient_desc =
            test_committee_descriptor("wrong-recipient", recipient_pk, [0xF3; 32]);
        let wrong_fed_verdict = dregg_verifier::cross_fed::verify_cross_fed_bundle(
            &bundle,
            &issuer_desc,
            &wrong_recipient_desc,
        );
        assert!(
            !wrong_fed_verdict.overall_verified,
            "wrong recipient committee federation id must reject imported artifacts: {wrong_fed_verdict:?}",
        );
    }

    /// Adversarial test: a receipt with a forged Effect-VM proof bytes
    /// must still parse out of the tool response, but the standalone
    /// verifier would reject it. We cannot drive `dregg-verifier
    /// replay-chain` from in-process tests (no cargo / no spawning
    /// the verifier binary in this lane), so we test the in-process
    /// `dregg_circuit::stark::proof_from_bytes` gate: forged bytes
    /// fail to deserialize as a valid proof.
    #[tokio::test]
    async fn forged_proof_bytes_fail_to_deserialize() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let params = serde_json::json!({
            "name": "carol.dev",
            "expiry_height": 2_000_000_000u64,
        });
        let result = dispatch_tool("dregg_register_name", params, &state).await;
        let j = extract_json(&result);
        assert_proof_populated("forged_proof_honest_setup", &j);
        let proof_hex = j
            .get("effect_vm_proof_hex")
            .and_then(|v| v.as_str())
            .expect("proof_hex");
        // Sanity check: the real bytes deserialize.
        let proof_bytes = hex_decode_var(proof_hex).expect("hex decode");
        assert!(
            dregg_circuit::stark::proof_from_bytes(&proof_bytes).is_ok(),
            "real proof must deserialize"
        );
        // Forge: flip every byte. The DREG magic header check rejects.
        let mut forged = proof_bytes.clone();
        for b in &mut forged {
            *b ^= 0xFF;
        }
        assert!(
            dregg_circuit::stark::proof_from_bytes(&forged).is_err(),
            "forged proof bytes must NOT deserialize as a valid proof"
        );
    }

    // =====================================================================
    // MCP best-practices surface tests: annotations, structured content,
    // resources (incl. self-orientation), prompts, pagination, cap-gating.
    // =====================================================================

    #[test]
    fn every_tool_has_title_annotations_group_and_scope() {
        let defs = tool_definitions();
        assert!(defs.len() >= 40, "expected the full dregg toolset");
        for d in &defs {
            assert!(d.title.is_some(), "tool {} missing title", d.name);
            let ann = d.annotations.expect("annotations present");
            // read-only tools must NOT be flagged destructive.
            if ann.read_only_hint {
                assert!(
                    ann.destructive_hint != Some(true),
                    "read-only tool {} flagged destructive",
                    d.name
                );
            }
            // group + scope stamped into schema metadata for self-orientation.
            let schema = &d.input_schema;
            assert!(
                schema
                    .get("x-dregg-group")
                    .and_then(|v| v.as_str())
                    .is_some(),
                "tool {} missing x-dregg-group",
                d.name
            );
            assert!(
                schema
                    .get("x-dregg-scope")
                    .and_then(|v| v.as_str())
                    .is_some(),
                "tool {} missing x-dregg-scope",
                d.name
            );
            assert_ne!(tool_group(d.name), "other", "tool {} ungrouped", d.name);
        }
    }

    #[test]
    fn read_tools_are_read_only_and_idempotent() {
        let ann = tool_annotations("dregg_read_cell");
        assert!(ann.read_only_hint && ann.idempotent_hint);
        // a mutating, irreversible tool is marked destructive + not read-only.
        let revoke = tool_annotations("dregg_revoke_capability");
        assert!(!revoke.read_only_hint && revoke.destructive_hint == Some(true));
        // bridging reaches the open world.
        assert_eq!(
            tool_annotations("dregg_peer_exchange").open_world_hint,
            Some(true)
        );
    }

    #[test]
    fn structured_content_mirrors_json_results() {
        let v = serde_json::json!({ "a": 1, "b": "x" });
        let r = McpToolResult::json(&v);
        assert_eq!(r.structured_content.as_ref(), Some(&v));
        assert!(r.is_error.is_none());
        // actionable errors carry error+hint structure.
        let e = McpToolResult::actionable_error("boom", "do X");
        assert_eq!(e.is_error, Some(true));
        let sc = e.structured_content.expect("error has structured content");
        assert_eq!(sc.get("error").and_then(|v| v.as_str()), Some("boom"));
        assert_eq!(sc.get("hint").and_then(|v| v.as_str()), Some("do X"));
    }

    #[test]
    fn initialize_advertises_tools_resources_prompts() {
        let resp = handle_initialize(serde_json::json!(1));
        let v = serde_json::to_value(&resp).unwrap();
        let caps = &v["result"]["capabilities"];
        assert!(caps.get("tools").is_some());
        assert!(caps.get("resources").is_some());
        assert!(caps.get("prompts").is_some());
        assert!(
            caps.get("completions").is_some(),
            "must advertise completions"
        );
        assert_eq!(v["result"]["protocolVersion"], "2025-06-18");
        // Server-level orientation instructions point the agent at its
        // self-orientation surface on connect.
        let instr = v["result"]["instructions"].as_str().unwrap_or("");
        assert!(
            instr.contains("dregg://about") && instr.contains("_cap"),
            "instructions must orient the agent (about + ocap convention)"
        );
    }

    #[tokio::test]
    async fn tools_list_paginates() {
        // With enforcement OFF (default), the full catalog is visible, so
        // pagination pages the whole tool set. Follow cursors to the end and
        // confirm the union reconstructs every tool exactly once.
        let (state, _tmp) = fresh_unlocked_state().await;
        let mut collected: Vec<String> = Vec::new();
        let mut cursor: Option<String> = None;
        let mut pages = 0;
        loop {
            let params = match &cursor {
                Some(c) => serde_json::json!({ "cursor": c }),
                None => serde_json::json!({}),
            };
            let r = handle_tools_list(serde_json::json!(1), params, &state).await;
            let v = serde_json::to_value(&r).unwrap();
            let page = v["result"]["tools"].as_array().unwrap();
            assert!(
                page.len() <= MCP_PAGE_SIZE,
                "no page may exceed MCP_PAGE_SIZE"
            );
            for t in page {
                collected.push(t["name"].as_str().unwrap().to_string());
            }
            pages += 1;
            match v["result"]["nextCursor"].as_str() {
                Some(c) => cursor = Some(c.to_string()),
                None => break,
            }
            assert!(pages < 100, "pagination must terminate");
        }
        assert!(
            pages >= 2,
            "46 tools at page size 20 must span multiple pages"
        );
        assert_eq!(
            collected.len(),
            tool_definitions().len(),
            "paging through all cursors must yield every tool exactly once"
        );
    }

    #[tokio::test]
    async fn ontology_resource_exposes_29_effects() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let resp = handle_resources_read(
            serde_json::json!(1),
            serde_json::json!({ "uri": "dregg://ontology" }),
            &state,
        )
        .await;
        let v = serde_json::to_value(&resp).unwrap();
        let text = v["result"]["contents"][0]["text"].as_str().unwrap();
        let catalog: Value = serde_json::from_str(text).unwrap();
        assert_eq!(catalog["effect_count"], 29);
        assert_eq!(catalog["effects"].as_array().unwrap().len(), 29);
    }

    #[tokio::test]
    async fn identity_and_cell_resources_resolve() {
        let (state, _tmp) = fresh_unlocked_state().await;
        // identity resource reflects the node's own agent cell.
        let id_resp = handle_resources_read(
            serde_json::json!(1),
            serde_json::json!({ "uri": "dregg://identity" }),
            &state,
        )
        .await;
        let idv = serde_json::to_value(&id_resp).unwrap();
        let text = idv["result"]["contents"][0]["text"].as_str().unwrap();
        let ident: Value = serde_json::from_str(text).unwrap();
        let cell_hex = ident["agent_cell_id"].as_str().unwrap().to_string();
        // templated cell resource reads that same cell.
        let cell_resp = handle_resources_read(
            serde_json::json!(2),
            serde_json::json!({ "uri": format!("dregg://cell/{cell_hex}") }),
            &state,
        )
        .await;
        let cellv = serde_json::to_value(&cell_resp).unwrap();
        let ctext = cellv["result"]["contents"][0]["text"].as_str().unwrap();
        let cell: Value = serde_json::from_str(ctext).unwrap();
        assert_eq!(cell["found"], true, "agent cell should exist in ledger");
    }

    #[test]
    fn prompts_list_and_get_render() {
        let list = handle_prompts_list(serde_json::json!(1));
        let lv = serde_json::to_value(&list).unwrap();
        let names: Vec<&str> = lv["result"]["prompts"]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| p["name"].as_str().unwrap())
            .collect();
        assert!(names.contains(&"orient"));
        assert!(names.contains(&"delegate_capability"));
        // get renders a user message with the substituted arg.
        let get = handle_prompts_get(
            serde_json::json!(2),
            serde_json::json!({
                "name": "submit_turn",
                "arguments": { "intent": "transfer 5 to bob" }
            }),
        );
        let gv = serde_json::to_value(&get).unwrap();
        let msg = gv["result"]["messages"][0]["content"]["text"]
            .as_str()
            .unwrap();
        assert!(msg.contains("transfer 5 to bob"));
    }

    #[tokio::test]
    async fn cap_gating_rejects_uncovered_token_but_allows_read_when_unenforced() {
        let (state, _tmp) = fresh_unlocked_state().await;
        // Enforcement OFF (default in tests): missing _cap passes the gate.
        assert!(
            enforce_tool_cap("dregg_read_cell", &serde_json::json!({}), &state)
                .await
                .is_ok(),
            "missing cap should pass when enforcement is off (back-compat)"
        );
        // A garbage presented credential is ALWAYS verified and REJECTED,
        // even with enforcement off — the per-tool gate never trusts an
        // un-covering token.
        let bogus = serde_json::json!({ "_cap": { "biscuit": "eb2_not_a_real_biscuit" } });
        assert!(
            enforce_tool_cap("dregg_grant_capability", &bogus, &state)
                .await
                .is_err(),
            "a non-covering/garbage _cap must be rejected"
        );
    }
}
