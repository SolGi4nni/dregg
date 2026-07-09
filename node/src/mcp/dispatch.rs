//! `mcp::dispatch` — split out of the former monolithic `mcp.rs` (pure module move).

use super::*;

/// Derive the node's deterministic MCP-cap ISSUER keypair from its cipherclerk.
///
/// The node issues tools-access biscuits under this key. It is a one-way,
/// domain-separated derivation of the cipherclerk's signing key, so it is stable
/// across restarts and never exposes the raw identity key. The biscuit cover the
/// executor verifies is anchored in this issuer's public key (recorded as the
/// authority cell's `verification_key`), so only the node can mint a credential
/// the gate will accept.
pub(super) fn mcp_cap_issuer_keypair(
    cclerk: &AgentCipherclerk,
) -> dregg_token::biscuit_auth::KeyPair {
    let seed = cclerk.derive_symmetric_key("dregg-mcp-cap-issuer-v1");
    let private = dregg_token::biscuit_auth::PrivateKey::from_bytes(
        &seed,
        dregg_token::biscuit_auth::Algorithm::Ed25519,
    )
    .expect("32-byte ed25519 seed yields a valid biscuit private key");
    dregg_token::biscuit_auth::KeyPair::from(&private)
}

/// The node's MCP-cap issuer public key (the trust anchor the executor checks).
pub(super) fn mcp_cap_issuer_pubkey(cclerk: &AgentCipherclerk) -> [u8; 32] {
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
pub(super) fn mcp_authority_cell(node_pk: &[u8; 32], issuer_pubkey: &[u8; 32]) -> dregg_cell::Cell {
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
#[allow(dead_code)] // Retained MCP cap-minting helper for the tools/call gate (not yet wired).
pub(super) fn mint_tool_cap(
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
pub(super) fn parse_presented_cap(
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
pub(super) struct McpCapContext {
    pub(super) enforce: bool,
    pub(super) issuer_pubkey: [u8; 32],
    pub(super) authority_cell: dregg_cell::Cell,
    pub(super) federation_id: [u8; 32],
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
    pub(super) block_height: u64,
}

impl McpCapContext {
    pub(super) async fn snapshot(state: &NodeState) -> Self {
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
    pub(super) fn cap_covers_tool(
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
    pub(super) fn tool_invocable(
        &self,
        presented: Option<&dregg_turn::Authorization>,
        tool: &str,
    ) -> bool {
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
pub(super) async fn enforce_tool_cap(
    tool: &str,
    arguments: &Value,
    state: &NodeState,
) -> Result<(), String> {
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

pub(super) async fn dispatch_tool(name: &str, params: Value, state: &NodeState) -> McpToolResult {
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
        "dregg_list_cells" => tool_list_cells(&params, state).await,
        "dregg_get_cap_graph" => tool_get_cap_graph(&params, state).await,
        "dregg_get_trustline_status" => tool_get_trustline_status(&params, state).await,
        "dregg_get_channel_status" => tool_get_channel_status(&params, state).await,
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
        // Trustlines (ORGANS §1 — the bilateral line of credit)
        "dregg_extend_trustline" => tool_extend_trustline(&params, state).await,
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
