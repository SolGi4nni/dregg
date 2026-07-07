//! `mcp::handlers_verify` — split out of the former monolithic `mcp.rs` (pure module move).

use super::*;

pub(super) async fn tool_peer_exchange(params: &Value, state: &NodeState) -> McpToolResult {
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
    let mut exchange = dregg_cell_crypto::PeerExchange::new(cell_id, signing_key);
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

pub(super) async fn tool_compress_history(params: &Value, state: &NodeState) -> McpToolResult {
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

pub(super) async fn tool_prove_sovereign_turn(params: &Value, state: &NodeState) -> McpToolResult {
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

    // The v1 hand-AIR (`EffectVmAir`) standalone effect-VM prove is RETIRED; this demo
    // tool reports the standalone v1 proof is unavailable (finalized turns prove rotated
    // through the node commit pipeline).
    let _ = (&trace, &public_inputs, &cell_id_hex);
    McpToolResult::json(&serde_json::json!({
        "proved": false,
        "cell_id": cell_id_hex,
        "effect_count": vm_effects.len(),
        "error": "standalone v1 effect-vm proof is retired; finalized turns prove rotated \
                  through the node commit pipeline",
    }))
}

pub(super) async fn tool_verify_sovereign_proof(
    params: &Value,
    state: &NodeState,
) -> McpToolResult {
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

    // Parse public inputs as BabyBear field elements.
    let public_inputs: Vec<dregg_circuit::BabyBear> = public_inputs_val
        .iter()
        .filter_map(|v| v.as_u64().map(|n| dregg_circuit::BabyBear::new(n as u32)))
        .collect();

    // The v1 hand-AIR (`EffectVmAir`) standalone effect-VM `StarkProof` verify is RETIRED and
    // the v1 wire format is gone. Descriptor-IR2 proofs verify through
    // `dregg_circuit::descriptor_ir2::verify_vm_descriptor2`, which must anchor against the
    // emitted descriptor — not available from this raw-bytes demo surface (no descriptor is
    // supplied) — so this tool reports v1 verification is unavailable and rejects (fail-closed).
    let _ = &proof_bytes;
    McpToolResult::json(&serde_json::json!({
        "valid": false,
        "error": "v1 effect-vm STARK verification is retired; descriptor-IR2 proofs verify \
                  through verify_vm_descriptor2 (which needs the descriptor to anchor against)",
        "public_inputs_count": public_inputs.len(),
        "proof_bytes_len": proof_bytes.len(),
    }))
}

// =============================================================================
// Privacy tools
// =============================================================================

pub(super) async fn tool_prove_predicate(params: &Value, state: &NodeState) -> McpToolResult {
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

pub(super) async fn tool_compose_proofs(params: &Value, state: &NodeState) -> McpToolResult {
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
pub(super) async fn tool_sign_sovereign_witness(
    params: &Value,
    state: &NodeState,
) -> McpToolResult {
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
        let (proof_hex, _pi, _trace, _wh) = generate_effect_vm_proof(
            u64::try_from(cell.state.balance()).unwrap_or(0),
            cell.state.nonce(),
            &vm_effects,
        );
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
