//! `mcp::proof` — split out of the former monolithic `mcp.rs` (pure module move).

use super::*;

/// 32-byte-widening helper (effect-vm-hash-widen lane, 2026-05-28): the
/// EffectVM `GrantCapability.cap_entry` param is now `[BabyBear; 8]`. These
/// MCP construction sites carry a SCALAR cap-slot index (not a 32-byte hash),
/// so we anchor it in limb[0] — which drives the AIR's cap_root advance — and
/// leave the high limbs zero. This is byte-for-byte equivalent to the prior
/// single-felt binding, now in the widened 8-limb shape.
pub(super) fn grant_cap_entry_8(scalar: u32) -> [dregg_circuit::BabyBear; 8] {
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
pub(super) fn parse_effect_json(value: &Value) -> Result<dregg_turn::Effect, String> {
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
pub(super) fn build_forest_with_effects(
    target: CellId,
    effects: Vec<dregg_turn::Effect>,
) -> CallForest {
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
///
/// `turn_nonce` must be the nonce the enclosing turn is submitted under
/// (`dregg-action-sig-v3` binds it into the signing message; callers here
/// stamp `turn.nonce = cclerk.receipt_chain_length()`).
pub(super) fn build_signed_forest(
    target: CellId,
    effects: Vec<dregg_turn::Effect>,
    cclerk: &dregg_sdk::AgentCipherclerk,
    federation_id: &[u8; 32],
    turn_nonce: u64,
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
    let msg = dregg_turn::TurnExecutor::compute_signing_message(&action, federation_id, turn_nonce);
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
pub(super) struct EffectVmProofMaterial {
    pub(super) proof_hex: String,
    pub(super) public_inputs: Vec<u64>,
    pub(super) trace_rows: Vec<Vec<u32>>,
    pub(super) witness_hash_hex: String,
}

impl EffectVmProofMaterial {
    pub(super) fn into_parts(self) -> (String, Vec<u64>, Vec<Vec<u32>>, String) {
        (
            self.proof_hex,
            self.public_inputs,
            self.trace_rows,
            self.witness_hash_hex,
        )
    }

    pub(super) fn proof_json(&self) -> serde_json::Value {
        serde_json::Value::String(self.proof_hex.clone())
    }

    pub(super) fn trace_json(&self) -> serde_json::Value {
        serde_json::to_value(&self.trace_rows).unwrap_or(serde_json::Value::Null)
    }

    pub(super) fn witness_hash_json(&self) -> serde_json::Value {
        serde_json::Value::String(self.witness_hash_hex.clone())
    }
}

pub(super) fn witnessed_receipt_from_effect_material(
    receipt: dregg_turn::TurnReceipt,
    proof: &EffectVmProofMaterial,
) -> Option<dregg_turn::WitnessedReceipt> {
    let mut public_inputs: Vec<u32> = proof.public_inputs.iter().map(|x| *x as u32).collect();
    let needed = dregg_circuit::effect_vm::pi::ACTIVE_BASE_COUNT
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
    // The v1 hand-AIR (`EffectVmAir`) receipt-bound WR proof is RETIRED. The per-receipt
    // attestation is the rotated finalized-turn proof produced by the node's async prove
    // pool; this inline-trace v1 WR is a v1-only artifact, so the helper yields `None`
    // (the receipt still commits; its rotated attestation arrives separately).
    let _ = (&trace, &public_input_felts, &public_inputs, receipt);
    None
}

pub(super) fn project_effects_for_mcp(
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

pub(super) fn require_pre_state(
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

pub(super) fn require_local_cell_for_commit(
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

pub(super) fn require_effect_cells_for_commit(
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
pub(super) fn require_effect_vm_proof(
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
pub(super) fn generate_effect_vm_proof(
    initial_balance: u64,
    initial_nonce: u64,
    vm_effects: &[dregg_circuit::effect_vm::Effect],
) -> (String, Vec<u64>, Vec<Vec<u32>>, String) {
    match try_generate_effect_vm_proof(initial_balance, initial_nonce, vm_effects) {
        Ok(material) => material.into_parts(),
        Err(e) => panic!("{e}"),
    }
}

pub(super) fn try_generate_effect_vm_proof(
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
    // The v1 hand-AIR (`EffectVmAir`) standalone effect-VM proof material is RETIRED.
    // Finalized turns prove rotated through the node's commit pipeline; this standalone
    // v1 material is no longer produced.
    let _ = (&trace, &public_inputs);
    Err(
        "standalone v1 effect-vm proof material is retired (finalized turns prove rotated \
         through the node commit pipeline)"
            .to_string(),
    )
}

// =============================================================================
// JSON-RPC types
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
pub(super) fn schedule_projected_wr(
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
    if pi.len() < p::ACTIVE_BASE_COUNT {
        pi.resize(p::ACTIVE_BASE_COUNT, BabyBear::ZERO);
    }

    let (th, eg, actor_nonce, prev) = dregg_turn::TurnExecutor::compute_turn_identity_pi(turn);
    pi[p::TURN_HASH_BASE..p::TURN_HASH_BASE + p::TURN_HASH_LEN]
        .copy_from_slice(&th[..p::TURN_HASH_LEN]);
    pi[p::EFFECTS_HASH_GLOBAL_BASE..p::EFFECTS_HASH_GLOBAL_BASE + p::EFFECTS_HASH_GLOBAL_LEN]
        .copy_from_slice(&eg[..p::EFFECTS_HASH_GLOBAL_LEN]);
    pi[p::ACTOR_NONCE] = BabyBear::new((actor_nonce & 0x7FFF_FFFF) as u32);
    pi[p::PREVIOUS_RECEIPT_HASH_BASE..p::PREVIOUS_RECEIPT_HASH_BASE + p::PREVIOUS_RECEIPT_HASH_LEN]
        .copy_from_slice(&prev[..p::PREVIOUS_RECEIPT_HASH_LEN]);

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
    let mut wr = dregg_turn::WitnessedReceipt::from_components(
        receipt.clone(),
        hex_decode_var(&material.proof_hex).unwrap_or_default(),
        pi_u32,
        if trace_bb.is_empty() {
            None
        } else {
            Some(trace_bb.as_slice())
        },
    );
    // ROTATED-WR PRODUCER (ROTATION-CUTOVER §EXEC.3): carry the decoupled 49-felt schedule
    // block NATIVELY so the aggregator's `build_inner_rows_v2` can consume it WITHOUT the
    // >=204-wide v1 PI a rotated WR (38/39-PI) does not have. `schedule_block_for_cell` produces
    // the same block `schedule_block_from_inner_pi` would project from a full v1 PI; the field is
    // `serde(default)`, so it round-trips through the DWR1 artifact and is ignored by every legacy
    // consumer. CG-3 in-circuit rejects a divergent block, so the honest construction is safe.
    wr.bilateral_schedule =
        Some(dregg_turn::bilateral_schedule::schedule_block_for_cell(turn, cell_id).to_vec());
    wr
}

/// Translate a turn-domain `Effect` into a single Effect-VM `Effect`.
/// Covers all AIR-side variants:
/// - `SetField` → `VmEffect::SetField`
/// - `Transfer` → `VmEffect::Transfer` (debit side, direction=1)
/// - `EmitEvent` → `VmEffect::EmitEvent` (BLAKE3 topic + payload, per #110)
///
/// Returns `None` for variants without an AIR-side analog (IncrementNonce,
/// GrantCapability, RevokeCapability, CreateCell, etc.).
pub(super) fn project_setfield_to_vm(
    effect: &dregg_turn::Effect,
) -> Option<dregg_circuit::effect_vm::Effect> {
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
pub(super) fn ensure_cell_in_ledger(
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
        // THE EPOCH: balances are SIGNED (i64); the VM pre-state tuple is u64.
        // These are ORDINARY cells (non-negative) — checked conversion.
        Some(c) => (
            u64::try_from(c.state.balance()).unwrap_or(0),
            c.state.nonce(),
        ),
        None => (0, 0),
    }
}
