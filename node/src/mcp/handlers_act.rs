//! `mcp::handlers_act` — split out of the former monolithic `mcp.rs` (pure module move).

use super::*;

pub(super) async fn tool_create_agent(params: &Value, state: &NodeState) -> McpToolResult {
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
        // THE EPOCH: balances are SIGNED (i64); a freshly created agent is an
        // ORDINARY cell (non-negative) — checked conversion, never `as`.
        let cell = dregg_cell::Cell::with_balance(
            pk_bytes,
            [0u8; 32],
            i64::try_from(initial_balance).unwrap_or(i64::MAX),
        );
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

pub(super) async fn tool_authorize(params: &Value, state: &NodeState) -> McpToolResult {
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

pub(super) async fn tool_submit_turn(params: &Value, state: &NodeState) -> McpToolResult {
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

    // Execute the turn locally — THROUGH THE ONE producer gate (#171), so the
    // generic MCP submit ingress runs on the SAME authoritative state producer as
    // a consensus-finalized turn (`blocklace_sync::execute_finalized_turn`) or a
    // pg-queued one (`submit_queue_drainer`): under producer mode (default ON) the
    // VERIFIED Lean executor is authoritative for the swap-safe covered set and the
    // Rust `TurnExecutor` is the demoted differential reference. Previously this
    // surface called `executor.execute` directly, leaving Rust authoritative on the
    // MCP path — the remaining Stage-0 seam this closes.
    let federation_id = s.federation_id;
    let mut executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    executor.set_local_federation_id(federation_id);
    executor.set_executor_signing_key(s.cclerk.gossip_signing_key().to_bytes());
    let lean_producer_enabled = s.lean_producer_enabled;
    let exec_result = crate::executor_setup::execute_via_producer(
        &executor,
        &turn,
        &mut s.ledger,
        lean_producer_enabled,
    );

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

pub(super) async fn tool_post_intent(params: &Value, state: &NodeState) -> McpToolResult {
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

pub(super) async fn tool_fulfill_intent(params: &Value, state: &NodeState) -> McpToolResult {
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
        return McpToolResult::error(format!(
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

    // The retired hand-STARK `PredicateProof` is gone; intent's fulfillment now carries the bridge's
    // descriptor-backed `BridgePredicateProof`. This simple MCP flow attaches none (guarded above),
    // so the empty vec's element type is inferred from the `FulfillmentWithPredicates` field.
    let predicate_proofs = vec![];

    let fulfillment_with_preds = dregg_intent::fulfillment::FulfillmentWithPredicates {
        base: base_fulfillment,
        predicate_proofs,
        state_root,
        state_root_block: current_height,
    };

    // Execute the fulfillment payment through the VERIFIED settle path (same edge as the
    // `/intents/fulfill` API handler): the value-moving leg folds through the verified
    // per-asset transition, cross-checked against the REAL Lean executor export
    // `dregg_record_kernel_step` (Lean unconditional on native). Fail-closed — no
    // fallback to the legacy `dregg_turn::TurnExecutor`.
    let result = dregg_intent::fulfillment::execute_fulfillment_flow_verified(
        &intent,
        &fulfillment_with_preds,
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

pub(super) async fn tool_make_sovereign(params: &Value, state: &NodeState) -> McpToolResult {
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

pub(super) async fn tool_debit_shared_resource(params: &Value, state: &NodeState) -> McpToolResult {
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
// Trustline tools (ORGANS §1 — the bilateral line of credit)
// =============================================================================

/// `dregg_extend_trustline` — drive the trustline birth lifecycle in-process
/// against the node's authoritative executor (the same path the
/// `/trustline/open` HTTP route uses). "Extend a holder a line of N" births a
/// per-line cell, escrows the full line from this node's agent cell (the
/// funded birth), grants the holder their line capability, and opens it.
pub(super) async fn tool_extend_trustline(params: &Value, state: &NodeState) -> McpToolResult {
    let holder = match params.get("holder").and_then(|v| v.as_str()) {
        Some(h) => h.to_string(),
        None => return McpToolResult::error("missing required parameter: holder"),
    };
    let line = match params.get("line").and_then(|v| v.as_u64()) {
        Some(l) => l,
        None => return McpToolResult::error("missing required parameter: line (integer)"),
    };
    let salt = params
        .get("salt")
        .and_then(|v| v.as_str())
        .map(|s| s.to_string());

    let req = crate::trustline_service::OpenRequest { holder, line, salt };
    let mut s = state.write().await;
    match crate::trustline_service::open_trustline(&mut s, req).await {
        Ok(resp) => McpToolResult::json(&serde_json::json!({
            "trustline": resp.trustline,
            "issuer": resp.issuer,
            "holder": resp.holder,
            "line": resp.line,
            "escrow": resp.escrow,
            "coordinator_remaining": resp.coordinator_remaining,
            "turn_hashes": resp.turn_hashes,
            "note": "Trustline opened (ORGANS §1 birth edge): the line is escrowed and granted to the holder as a capability. The holder draws/repays against it; settlement redeems drawn value as a conserving transfer.",
        })),
        Err(e) => McpToolResult::actionable_error(
            format!("trustline open refused: {}", e.detail()),
            "ensure the node is unlocked, the holder cell exists in the ledger, and the agent \
             cell is funded for the line + fees; vary `salt` if a line to this holder already \
             exists",
        ),
    }
}

// =============================================================================
// Gallery tools
// =============================================================================

pub(super) async fn tool_place_bid(params: &Value, state: &NodeState) -> McpToolResult {
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
pub(super) async fn tool_captp_deliver(params: &Value, state: &NodeState) -> McpToolResult {
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
pub(super) async fn tool_bilateral_action(params: &Value, state: &NodeState) -> McpToolResult {
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
                provenance: dregg_cell::derivation::cap_provenance(
                    &(from_cell),
                    (0),
                    &dregg_cell::derivation::mint_provenance(),
                    &[0u8; 32],
                ),
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

    // THE EPOCH: balances are SIGNED (i64); the VM pre-state tuples are u64.
    // Both sides are ORDINARY cells (non-negative) — checked conversion.
    let from_pre = s.ledger.get(&from_cell).map(|c| {
        (
            u64::try_from(c.state.balance()).unwrap_or(0),
            c.state.nonce(),
        )
    });
    let to_pre = s.ledger.get(&to_cell).map(|c| {
        (
            u64::try_from(c.state.balance()).unwrap_or(0),
            c.state.nonce(),
        )
    });

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
        match dregg_turn_prover::aggregate_bilateral_prover::prove_aggregated_bundle(
            &turn, &entries,
        ) {
            Ok(bundle) => {
                // Self-check: the bundle must verify (real outer STARK verify).
                match dregg_turn_prover::aggregate_bilateral_prover::verify_aggregated_bundle(
                    &bundle,
                ) {
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
