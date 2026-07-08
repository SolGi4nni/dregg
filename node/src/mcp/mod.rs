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

mod dispatch;
mod handlers_act;
mod handlers_apps;
mod handlers_delegate;
mod handlers_orient;
mod handlers_privacy;
mod handlers_verify;
mod proof;
mod protocol;
mod tools_def;

// Re-import every submodule namespace so the shared helpers below, the
// `tests` module, and each sibling submodule (via its own `use super::*`)
// all see the full `mcp` surface — a pure-module-move convenience.
use dispatch::*;
use handlers_act::*;
use handlers_apps::*;
use handlers_delegate::*;
use handlers_orient::*;
use handlers_privacy::*;
use handlers_verify::*;
use proof::*;
use protocol::*;
use tools_def::*;

pub use protocol::run_stdio;

// =============================================================================
// Shared low-level helpers (used across every tool group).
// =============================================================================

/// Common helper: read the agent's own cell id from state. The caller
/// holds the lock; we just compute the derivation.
fn agent_cell_of(cclerk: &AgentCipherclerk) -> CellId {
    dregg_cell::CellId::derive_raw(&cclerk.public_key().0, &[0u8; 32])
}

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
    if !s.len().is_multiple_of(2) {
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
    ///
    /// v1 floor only: `generate_effect_vm_proof` produces a v1 hand-AIR proof, which is absent
    /// under the prover build.
    #[cfg(not(feature = "prover"))]
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

    // Used only by the prover-gated v1-floor `*_produces_proof_carrying_receipt` /
    // `forged_proof_bytes_*` tests (it asserts the synchronous v1 DREG `effect_vm_proof_hex`).
    #[cfg(not(feature = "prover"))]
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

    // V1-FLOOR (prover-gated): the MCP tool surface's SYNCHRONOUS standalone effect-vm proof is
    // the v1 hand-AIR (`EffectVmAir`) DREG-format `StarkProof` that `try_generate_effect_vm_proof`
    // produces and `require_effect_vm_proof` gates the commit on. Under `prover` (default) the v1
    // hand-AIR is retired (`EffectVmAir` is `#[cfg(not(prover))]`) and the live attestation is the
    // ROTATED finalized-turn proof the node's async prove pool produces through the commit pipeline
    // (covered by `turn_proving::tests::flow_b_*` + the executor rotated WR path). This standalone-
    // proof tool surface is therefore a `not(prover)` floor; the test runs under
    // `--no-default-features`.
    #[cfg(not(feature = "prover"))]
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

    // V1-FLOOR (prover-gated): these four `dregg_*_produces_proof_carrying_receipt` tests assert
    // the SYNCHRONOUS standalone v1 effect-vm DREG `StarkProof` (`assert_proof_populated`), which is
    // retired under `prover` (the live attestation is the rotated node-pipeline proof). They run
    // under `--no-default-features`. See `grant_capability_commits_witness_artifact_for_receipt_chain`.
    #[cfg(not(feature = "prover"))]
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

    #[cfg(not(feature = "prover"))] // v1-floor standalone proof (see register_name above)
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

    #[cfg(not(feature = "prover"))] // v1-floor standalone proof (see register_name above)
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

    #[cfg(not(feature = "prover"))] // v1-floor standalone proof (see register_name above)
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
    // V1-FLOOR (prover-gated): both handoff-cert tests drive the tool through
    // `require_effect_vm_proof` (which gates the COMMIT on the v1 standalone DREG proof) and assert
    // the v1 `effect_vm_proof_hex` / the v1-proof-generation error text. Under `prover` that v1
    // standalone proof is retired; the live attestation is the rotated node-pipeline proof. Runs
    // under `--no-default-features`. (The rotated handoff path is exercised by the silver-captp
    // integration + the executor rotated WR path.)
    #[cfg(not(feature = "prover"))]
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
    #[cfg(not(feature = "prover"))] // v1-floor standalone proof (see honest_path_commits above)
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

    // These three cross-fed test helpers are used ONLY by the prover-gated `silver_captp_*` tests
    // (whose handoff-commit step is v1-floor-only), so they are gated to match — else they would be
    // dead code under `prover`.
    #[cfg(not(feature = "prover"))]
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

    #[cfg(not(feature = "prover"))] // silver-captp-only helper (see test_committee_descriptor)
    fn sign_test_attested_root(
        mut root: dregg_types::AttestedRoot,
        sk: &dregg_types::SigningKey,
    ) -> dregg_types::AttestedRoot {
        let sig = dregg_types::sign(sk, &root.signing_message());
        root.quorum_signatures = vec![(sk.public_key(), sig)];
        root
    }

    #[cfg(not(feature = "prover"))] // silver-captp-only helper (see test_committee_descriptor)
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

    /// The cross-fed AttestedRoot quorum, made HYBRID (ed25519 ∧ ML-DSA-65).
    ///
    /// The cross-fed verifier checks `AttestedRoot.quorum_signatures` (ed25519)
    /// over `root.signing_message()`. Here a SELF-CONTAINED hybrid quorum (each
    /// signer's ed25519 signature AND its ML-DSA-65 signature + self-carried
    /// ML-DSA public key) over the SAME message is verified via the shared
    /// `dregg_federation::receipt::verify_hybrid_quorum_sigs` — the one place the
    /// classical ∧ pq rule lives. A forged or missing ML-DSA half is rejected
    /// even with a valid ed25519 half (the teeth), and a non-member signer is
    /// rejected. (Wiring this into `verify_cross_fed_bundle` and the `AttestedRoot`
    /// wire shape is a deferred flag-day: those live in `verifier/` and the
    /// `sdk/`-shared `types::AttestedRoot`, outside this lane.)
    #[test]
    fn cross_fed_attested_root_hybrid_quorum_teeth() {
        use dregg_federation::frost::MlDsaSigningKey;
        use dregg_federation::receipt::verify_hybrid_quorum_sigs;
        use dregg_types::{AttestedRoot, FederationId, HybridQuorumSig};

        let kps: Vec<(dregg_types::SigningKey, dregg_types::PublicKey)> = (0..3)
            .map(|i| {
                let mut s = [0u8; 32];
                s[0] = 0x51;
                s[1] = i as u8;
                let sk = dregg_types::SigningKey::from_bytes(&s);
                let pk = sk.public_key();
                (sk, pk)
            })
            .collect();
        let members: Vec<dregg_types::PublicKey> = kps.iter().map(|(_, pk)| *pk).collect();
        let pq: Vec<_> = (0..3)
            .map(|i| {
                let mut s = [0u8; 32];
                s[0] = 0x52;
                s[1] = i as u8;
                MlDsaSigningKey::from_seed(&s)
            })
            .collect();
        let fed_id = dregg_federation::derive_federation_id_with_epoch(&members, 0);

        let root = AttestedRoot {
            merkle_root: [7u8; 32],
            note_tree_root: None,
            nullifier_set_root: None,
            height: 42,
            timestamp: 1_700_000_042,
            blocklace_block_id: Some([9u8; 32]),
            finality_round: Some(42),
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: 2,
            federation_id: FederationId(fed_id),
            receipt_stream_root: None,
        };
        let message = root.signing_message();

        let make = |idxs: &[usize]| -> Vec<HybridQuorumSig> {
            idxs.iter()
                .map(|&i| HybridQuorumSig {
                    pubkey: kps[i].1,
                    signature: dregg_types::sign(&kps[i].0, &message),
                    ml_dsa_pubkey: pq[i].0.0.to_vec(),
                    pq_signature: pq[i].1.sign(&message).expect("ml-dsa sign"),
                })
                .collect()
        };

        // Honest 2-of-3 hybrid cross-fed quorum verifies (BOTH halves).
        assert!(
            verify_hybrid_quorum_sigs(&make(&[0, 1]), &message, &members, 2),
            "honest hybrid cross-fed quorum must verify"
        );

        // TEETH: forge the ML-DSA half, keep a VALID ed25519 half → REJECT.
        let mut forged = make(&[0, 1]);
        forged[0].pq_signature[0] ^= 0xFF;
        assert!(
            !verify_hybrid_quorum_sigs(&forged, &message, &members, 2),
            "forged ML-DSA half must reject even with a valid ed25519 half"
        );

        // TEETH: missing (empty) PQ half → REJECT.
        let mut missing = make(&[0, 1]);
        missing[1].pq_signature = Vec::new();
        assert!(
            !verify_hybrid_quorum_sigs(&missing, &message, &members, 2),
            "missing ML-DSA half must reject"
        );

        // Non-member fully-valid hybrid signer → REJECT.
        let mut outs = [0u8; 32];
        outs[0] = 0xEE;
        let outsider_sk = dregg_types::SigningKey::from_bytes(&outs);
        let (out_pq_pk, out_pq_sk) = MlDsaSigningKey::from_seed(&[0xEF; 32]);
        let outsider = vec![HybridQuorumSig {
            pubkey: outsider_sk.public_key(),
            signature: dregg_types::sign(&outsider_sk, &message),
            ml_dsa_pubkey: out_pq_pk.0.to_vec(),
            pq_signature: out_pq_sk.sign(&message).expect("ml-dsa sign"),
        }];
        assert!(
            !verify_hybrid_quorum_sigs(&outsider, &message, &members, 1),
            "non-member hybrid signer must reject"
        );
    }

    // V1-FLOOR (prover-gated): both silver-captp tests first COMMIT a handoff-cert exercise
    // through the MCP tool, which under the v1 floor gates the commit on the standalone DREG proof
    // (`require_effect_vm_proof`). Under `prover` that v1 standalone proof is retired so the
    // handoff tool returns `proof_generation_failed` instead of committing; the cross-fed bundle
    // export they assert is downstream of that commit. They run under `--no-default-features`. (The
    // rotated cross-fed witnessed-receipt path is exercised by `silver_captp_*` at the verifiable-
    // bundle layer + the executor rotated WR path.)
    #[cfg(not(feature = "prover"))]
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

    #[cfg(not(feature = "prover"))] // v1-floor handoff commit gate (see the export test above)
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

    // (Deleted) `forged_proof_bytes_fail_to_deserialize`: a `not(feature = "prover")`
    // V1-FLOOR test whose sole purpose was pinning the DREG-magic v1 `StarkProof` wire
    // format via the legacy hand-STARK `proof_from_bytes` gate. That hand-STARK engine and
    // its wire format are retired; forged-proof rejection is now covered by the
    // descriptor-IR2 verify path (`verify_vm_descriptor2`) and the `*_emit_gate` tests.

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

    /// The new query tools are wired end-to-end: registered (dispatch + defs +
    /// metadata) AND return the right shape against a real ledger.
    #[tokio::test]
    async fn list_cells_surfaces_the_agent_cell() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let agent_cell = {
            let s = state.read().await;
            hex_encode(agent_cell_of(&s.cclerk).as_bytes())
        };
        let result = dispatch_tool("dregg_list_cells", serde_json::json!({}), &state).await;
        let j = extract_json(&result);
        let cells = j["cells"].as_array().expect("cells array");
        assert!(
            cells
                .iter()
                .any(|c| c["cell_id"].as_str() == Some(agent_cell.as_str())),
            "list_cells must surface the in-ledger agent cell; got {cells:?}"
        );
        // The agent cell is an ordinary cell (not a trustline/channel/sovereign).
        let entry = cells
            .iter()
            .find(|c| c["cell_id"].as_str() == Some(agent_cell.as_str()))
            .unwrap();
        assert_eq!(entry["kind"].as_str(), Some("cell"));
    }

    #[tokio::test]
    async fn cap_graph_defaults_to_agent_cell_and_returns_edges_shape() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let agent_cell = {
            let s = state.read().await;
            hex_encode(agent_cell_of(&s.cclerk).as_bytes())
        };
        // No cell_id ⇒ the node's own agent cell.
        let result = dispatch_tool("dregg_get_cap_graph", serde_json::json!({}), &state).await;
        let j = extract_json(&result);
        assert_eq!(j["cell_id"].as_str(), Some(agent_cell.as_str()));
        assert_eq!(j["found"].as_bool(), Some(true));
        assert!(j["edges"].is_array(), "edges must be an array");
        assert!(j["edge_count"].is_u64(), "edge_count must be present");
    }

    /// A non-organ cell is correctly REFUSED by the organ-status tools (the
    /// self-authenticating VK check rejects it), with an actionable error.
    #[tokio::test]
    async fn trustline_status_rejects_a_plain_cell() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let agent_cell = {
            let s = state.read().await;
            hex_encode(agent_cell_of(&s.cclerk).as_bytes())
        };
        let result = dispatch_tool(
            "dregg_get_trustline_status",
            serde_json::json!({ "trustline_cell": agent_cell }),
            &state,
        )
        .await;
        assert_eq!(
            result.is_error,
            Some(true),
            "a plain agent cell is not a trustline and must be refused"
        );
        let sc = result.structured_content.expect("actionable error payload");
        assert!(sc.get("error").is_some() && sc.get("hint").is_some());
    }

    /// The four new read tools require only the `read` scope (never write/admin)
    /// — so an orienting agent can survey the world with a read-only cap.
    #[test]
    fn new_query_tools_are_read_scoped_and_grouped() {
        for t in [
            "dregg_list_cells",
            "dregg_get_cap_graph",
            "dregg_get_trustline_status",
            "dregg_get_channel_status",
        ] {
            assert_eq!(tool_required_scope(t), "read", "{t} must be read-scoped");
            assert_eq!(tool_group(t), "orient", "{t} must be in the orient group");
            assert!(tool_annotations(t).read_only_hint, "{t} must be read-only");
        }
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

    /// The ontology resource exposes a self-consistent effect catalog: a
    /// non-empty effect list whose length matches the advertised `effect_count`.
    /// (The exact count is generator-owned — `ontology-catalog.generated.json` —
    /// so this pins the INVARIANT, not a magic number that drifts every time the
    /// kernel grows an effect.)
    #[tokio::test]
    async fn ontology_resource_effect_catalog_is_self_consistent() {
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
        let effects = catalog["effects"].as_array().expect("effects array");
        assert!(
            !effects.is_empty(),
            "ontology must advertise at least one effect"
        );
        assert_eq!(
            catalog["effect_count"].as_u64(),
            Some(effects.len() as u64),
            "advertised effect_count must match the effects array length",
        );
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
