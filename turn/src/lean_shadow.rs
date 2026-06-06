//! Optional Lean FFI shadow execution — compares Rust commit decisions against the
//! verified Lean kernel without affecting [`crate::turn::TurnResult`].
//!
//! Enabled when `DREGG_LEAN_SHADOW=1` and `dregg_lean_ffi::lean_available()`.
//!
//! # Scope: full multi-action FORESTS (no longer single-`SetField`)
//!
//! The shadow marshals the WHOLE Rust call-forest through the gated FFI
//! `shadow_exec_full_forest_auth`. A turn's forest is pre-order flattened into a chain
//! of wire actions; the chain is carried as a single root `WForest` whose tail nodes are
//! `null`-cap delegation children — the Lean executor runs `null`-cap children
//! SEQUENTIALLY against the evolving state WITHOUT invoking the cap-handoff gate
//! (`execFullChildrenA`'s `capTarget = none` branch), which is exactly "run these actions
//! in order, all-or-nothing." That faithfully models the Rust executor's pre-order forest
//! walk for the `DelegationMode::None` default (every node acts under its own authority).
//!
//! A turn is shadowed only when EVERY effect maps to a wire action and every referenced
//! cell has a ledger snapshot — anything unmappable makes the turn INELIGIBLE (skipped,
//! never silently mis-encoded; a dropped effect is worse than no shadow at all).
//!
//! The credential WHO-leg crosses faithfully: `Signature`/`Custom`/`Token`/`Bearer`/…
//! carry their FULL 256-bit digests via `marshal::Digest` (not a zeroed low-u64), so the
//! gate is genuinely exercised through the wire.

use std::cell::RefCell;
use std::collections::HashMap;

#[cfg(feature = "lean-shadow")]
use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, Ledger};

#[cfg(feature = "lean-shadow")]
use crate::action::{Authorization, DelegationProofData};
use crate::action::Effect;
use crate::forest::CallTree;
use crate::turn::{Turn, TurnResult};

/// Minimal pre-execution ledger snapshot for shadow marshalling.
///
/// The fields are read only by the FFI-build marshaller (`ledger_to_wire_state` /
/// `turn_to_wire_turn`); the non-feature build still captures the snapshot so eligibility
/// is decided identically, hence the conditional `allow(dead_code)`.
#[derive(Clone, Debug)]
#[cfg_attr(not(feature = "lean-shadow"), allow(dead_code))]
struct ShadowPreLedger {
    cells: HashMap<CellId, Cell>,
    id_map: HashMap<CellId, u64>,
}

thread_local! {
    static SHADOW_PRE: RefCell<Option<ShadowPreLedger>> = const { RefCell::new(None) };
    static SHADOW_BLOCK_HEIGHT: RefCell<u64> = const { RefCell::new(0) };
}

/// Capture a minimal pre-state snapshot when shadow mode may run later.
///
/// Call at the start of [`crate::executor::TurnExecutor::execute`] before any
/// ledger mutation so the Lean oracle sees the same admission inputs as Rust.
pub fn capture_pre_state_if_eligible(turn: &Turn, ledger: &Ledger, block_height: u64) {
    let snapshot = if shadow_env_enabled() && forest_is_marshallable(turn) {
        Some(build_pre_ledger(turn, ledger))
    } else {
        None
    };
    SHADOW_PRE.with(|slot| *slot.borrow_mut() = snapshot);
    SHADOW_BLOCK_HEIGHT.with(|h| *h.borrow_mut() = block_height);
}

/// Shadow-execute eligible turns against the Lean kernel and log divergences.
///
/// Uses the pre-execution snapshot stored by [`capture_pre_state_if_eligible`].
/// The `ledger` argument matches the public API; marshalling uses the captured pre-state.
pub fn maybe_shadow_turn(turn: &Turn, ledger: &Ledger, result: &TurnResult, block_height: u64) {
    let _ = (ledger, block_height);
    if !shadow_env_enabled() {
        SHADOW_PRE.with(|slot| slot.borrow_mut().take());
        SHADOW_BLOCK_HEIGHT.with(|h| *h.borrow_mut() = 0);
        return;
    }

    #[cfg(feature = "lean-shadow")]
    {
        if !dregg_lean_ffi::lean_available() {
            tracing::debug!("lean shadow: Lean lib unavailable, skipping");
            SHADOW_PRE.with(|slot| slot.borrow_mut().take());
            return;
        }

        let Some(pre) = SHADOW_PRE.with(|slot| slot.borrow_mut().take()) else {
            return;
        };

        if !forest_is_marshallable(turn) {
            return;
        }

        let height = SHADOW_BLOCK_HEIGHT.with(|h| *h.borrow());
        match run_shadow(turn, &pre, height) {
            Ok(lean_committed) => {
                let rust_committed = result.is_committed();
                if lean_committed != rust_committed {
                    tracing::warn!(
                        agent = ?turn.agent,
                        lean_committed,
                        rust_committed,
                        "lean shadow divergence: commit bit mismatch"
                    );
                }
            }
            Err(e) => {
                tracing::warn!(
                    agent = ?turn.agent,
                    error = %e,
                    "lean shadow: marshal/exec failed"
                );
            }
        }
    }

    #[cfg(not(feature = "lean-shadow"))]
    {
        SHADOW_PRE.with(|slot| slot.borrow_mut().take());
        let _ = (turn, result);
    }
}

fn shadow_env_enabled() -> bool {
    std::env::var("DREGG_LEAN_SHADOW").as_deref() == Ok("1")
}

// ===================================================================
// ELIGIBILITY — a turn is shadowed iff its WHOLE forest marshals.
// ===================================================================

/// True when every effect in the forest maps to a wire action and the cell-id set is
/// closed (so a Nat id can be assigned). Any unmappable effect ⇒ ineligible (the turn is
/// skipped rather than silently mis-encoded). Decided identically in both builds.
fn forest_is_marshallable(turn: &Turn) -> bool {
    if turn.call_forest.roots.is_empty() {
        return false;
    }
    let id_map = collect_id_map(turn);
    let mut any = false;
    let ok = turn
        .call_forest
        .roots
        .iter()
        .all(|r| tree_is_marshallable(r, &id_map, &mut any));
    ok && any
}

fn tree_is_marshallable(tree: &CallTree, id_map: &HashMap<CellId, u64>, any: &mut bool) -> bool {
    if !id_map.contains_key(&tree.action.target) {
        return false;
    }
    for eff in &tree.action.effects {
        if !effect_is_mappable(eff, id_map) {
            return false;
        }
        *any = true;
    }
    tree.children
        .iter()
        .all(|c| tree_is_marshallable(c, id_map, any))
}

/// Whether an effect projects to a wire action with all referenced cells in the id map.
/// MUST agree with `effect_to_wire`'s supported set (the FFI projector).
fn effect_is_mappable(eff: &Effect, id_map: &HashMap<CellId, u64>) -> bool {
    let has = |c: &CellId| id_map.contains_key(c);
    match eff {
        Effect::SetField { cell, .. } => has(cell),
        Effect::Transfer { from, to, .. } => has(from) && has(to),
        Effect::SetPermissions { cell, .. } => has(cell),
        Effect::SetVerificationKey { cell, .. } => has(cell),
        Effect::EmitEvent { cell, .. } => has(cell),
        Effect::MakeSovereign { cell } => has(cell),
        Effect::RevokeDelegation { child } => has(child),
        // Note set-transitions: the actor is the action target (already in the id map),
        // the nullifier/commitment are intrinsic to the effect — always mappable.
        Effect::NoteSpend { .. } => true,
        Effect::NoteCreate { .. } => true,
        // IncrementNonce carries no absolute new-nonce on the wire faithfully; excluded.
        // Everything else (escrows/queues/bridge/seal/captp/factory/…) not yet projected.
        _ => false,
    }
}

/// Assign a Nat to every CellId referenced by the turn (agent + every effect target),
/// in a deterministic order (sorted) so the kernel sees a stable labelling.
fn collect_id_map(turn: &Turn) -> HashMap<CellId, u64> {
    let mut ids: Vec<CellId> = vec![turn.agent];
    for root in &turn.call_forest.roots {
        collect_tree_ids(root, &mut ids);
    }
    ids.sort();
    ids.dedup();
    let mut map = HashMap::new();
    for (i, id) in ids.iter().enumerate() {
        map.insert(*id, i as u64);
    }
    map
}

fn collect_tree_ids(tree: &CallTree, ids: &mut Vec<CellId>) {
    ids.push(tree.action.target);
    for eff in &tree.action.effects {
        for c in effect_cells(eff) {
            ids.push(c);
        }
    }
    for child in &tree.children {
        collect_tree_ids(child, ids);
    }
}

/// The cell ids an effect references (so they can be assigned wire Nats). Only the
/// effects we can marshal need to list cells; an unlisted effect is simply not projected.
fn effect_cells(eff: &Effect) -> Vec<CellId> {
    match eff {
        Effect::SetField { cell, .. } => vec![*cell],
        Effect::Transfer { from, to, .. } => vec![*from, *to],
        Effect::IncrementNonce { cell } => vec![*cell],
        Effect::SetPermissions { cell, .. } => vec![*cell],
        Effect::SetVerificationKey { cell, .. } => vec![*cell],
        Effect::EmitEvent { cell, .. } => vec![*cell],
        Effect::Introduce {
            introducer,
            recipient,
            target,
            ..
        } => vec![*introducer, *recipient, *target],
        Effect::RevokeDelegation { child } => vec![*child],
        Effect::MakeSovereign { cell } => vec![*cell],
        _ => vec![],
    }
}

// ===================================================================
// PRE-STATE — snapshot every referenced cell present in the ledger.
// ===================================================================

fn build_pre_ledger(turn: &Turn, ledger: &Ledger) -> ShadowPreLedger {
    let id_map = collect_id_map(turn);
    let mut cells = HashMap::new();
    for id in id_map.keys() {
        if let Some(cell) = ledger.get(id) {
            cells.insert(*id, cell.clone());
        }
    }
    ShadowPreLedger { cells, id_map }
}

// ===================================================================
// FOREST PROJECTION — pre-order flatten the Rust forest to wire actions.
//
// Each Rust effect ⇒ one wire action. The forest is walked pre-order (a node's action
// effects, then its children left-to-right), exactly the order the Rust executor applies
// them. Returns `None` if ANY effect is unmappable (the turn is then ineligible).
// ===================================================================

/// Project ONE Rust effect to ONE wire action. The supported subset is the algebraic core
/// the Lean per-asset executor models faithfully; unsupported effects return `None` (the
/// turn is then skipped rather than mis-encoded). MUST agree with `effect_is_mappable`.
#[cfg(feature = "lean-shadow")]
fn effect_to_wire(
    actor: u64,
    eff: &Effect,
    id_map: &HashMap<CellId, u64>,
) -> Option<WireAction> {
    let id = |c: &CellId| id_map.get(c).copied();
    Some(match eff {
        Effect::SetField { cell, index, value } => WireAction::SetField {
            actor,
            cell: id(cell)?,
            field: field_index_to_name(*index),
            v: field_to_i128(value),
        },
        Effect::Transfer { from, to, amount } => WireAction::Balance {
            actor,
            src: id(from)?,
            dst: id(to)?,
            amt: *amount as i128,
            asset: 0,
        },
        Effect::SetPermissions { cell, new_permissions } => WireAction::SetPerms {
            actor,
            cell: id(cell)?,
            perms: permissions_to_i128(new_permissions),
        },
        // The verified Lean executor models `SetVk` directly (see
        // `Dregg2/Circuit/Inst/setVKA.lean` + the `setvk` wire arm). The VK is a
        // structured `{hash, data}`; the wire arm carries a scalar, so we collapse to
        // the low 64 bits of the canonical vk hash — the same digest-collapse the
        // `SetField`/`SetPerms` arms use. A cleared VK (`None`) maps to the `0` marker,
        // matching the executor's "no verification key" sentinel.
        Effect::SetVerificationKey { cell, new_vk } => WireAction::SetVk {
            actor,
            cell: id(cell)?,
            vk: new_vk
                .as_ref()
                .map(|vk| bytes32_to_nat(&vk.hash) as i128)
                .unwrap_or(0),
        },
        // The verified Lean executor models the privacy note-set transitions
        // (`Dregg2/Circuit/Inst/noteSpendA.lean` / `noteCreateA.lean` + the
        // `notespend`/`notecreate` wire arms). The Lean side enforces the
        // nullifier-set / commitment-set membership transition + anti-double-spend
        // guard bit; the STARK preimage/Merkle-membership stays the Rust circuit's
        // job. We carry the 32-byte nullifier / commitment collapsed to its low 64
        // bits — the same digest-collapse used for fields and vks. This is a
        // faithful projection of the SET decision (the only thing the executor's
        // commit-bit depends on), not of the proof bytes.
        Effect::NoteSpend { nullifier, .. } => WireAction::NoteSpend {
            nf: bytes32_to_nat(&nullifier.0),
            actor,
        },
        Effect::NoteCreate { commitment, .. } => WireAction::NoteCreate {
            cm: bytes32_to_nat(&commitment.0),
            actor,
        },
        Effect::EmitEvent { cell, event } => WireAction::Emit {
            actor,
            cell: id(cell)?,
            topic: field_to_i128(&event.topic),
            data: event_data_to_i128(event),
        },
        Effect::MakeSovereign { cell } => WireAction::MakeSovereign {
            actor,
            cell: id(cell)?,
        },
        Effect::RevokeDelegation { child } => WireAction::RevokeDelegation {
            holder: actor,
            target: id(child)?,
        },
        // Everything else (notes, escrows, queues, bridge, seal, captp, factory, …) is
        // not yet projected here. Returning None marks the turn ineligible rather than
        // silently dropping the effect.
        _ => return None,
    })
}

#[cfg(feature = "lean-shadow")]
use dregg_lean_ffi::marshal::WireAction;

#[cfg(feature = "lean-shadow")]
fn run_shadow(turn: &Turn, pre: &ShadowPreLedger, block_height: u64) -> Result<bool, String> {
    use dregg_lean_ffi::marshal::marshal_turn;

    let wire_state = ledger_to_wire_state(pre)?;
    let wire_turn = turn_to_wire_turn(turn, pre, block_height)?;
    let wire = marshal_turn(&wire_state, &wire_turn).map_err(|e| e.to_string())?;
    let out = dregg_lean_ffi::shadow_exec_full_forest_auth(&wire)?;
    let verdict = dregg_lean_ffi::decode_shadow_verdict(&out)?;
    Ok(verdict.committed)
}

#[cfg(feature = "lean-shadow")]
fn ledger_to_wire_state(pre: &ShadowPreLedger) -> Result<dregg_lean_ffi::marshal::WireState, String> {
    use dregg_lean_ffi::marshal::{WireState, WireValue};

    let mut cells = Vec::new();
    let mut bal = Vec::new();

    let mut sorted: Vec<_> = pre.id_map.iter().collect();
    sorted.sort_by_key(|(_, nat)| *nat);

    for (cell_id, nat) in sorted {
        // A referenced cell absent from the ledger (e.g. a fresh-create target) gets an
        // empty record; the gate decides admissibility. We only emit cells we snapshotted.
        let Some(cell) = pre.cells.get(cell_id) else {
            continue;
        };
        let mut fields = Vec::new();
        fields.push((
            "balance".to_string(),
            WireValue::Int(cell.state.balance() as i128),
        ));
        fields.push((
            "nonce".to_string(),
            WireValue::Int(cell.state.nonce() as i128),
        ));
        for (idx, value) in cell.state.fields.iter().enumerate() {
            if field_is_zero(value) {
                continue;
            }
            let name = field_index_to_name(idx);
            fields.push((name, WireValue::Int(field_to_i128(value))));
        }
        cells.push((*nat, WireValue::Record(fields)));
        bal.push((*nat, 0, cell.state.balance() as i128));
    }

    Ok(WireState {
        cells,
        caps: vec![],
        bal,
        escrows: vec![],
        nullifiers: vec![],
        commitments: vec![],
        queues: vec![],
        swiss: vec![],
        revoked: vec![],
    })
}

#[cfg(feature = "lean-shadow")]
fn turn_to_wire_turn(
    turn: &Turn,
    pre: &ShadowPreLedger,
    block_height: u64,
) -> Result<dregg_lean_ffi::marshal::WireTurn, String> {
    use dregg_lean_ffi::marshal::{Cap, WForest, WChild, WireTurn};

    let agent = *pre
        .id_map
        .get(&turn.agent)
        .ok_or_else(|| "shadow: agent cell not in id map".to_string())?;

    let valid_until = turn
        .valid_until
        .and_then(|v| u64::try_from(v).ok())
        .ok_or_else(|| "shadow: turn.valid_until required for wire marshal".to_string())?;

    let prev_hash = turn
        .previous_receipt_hash
        .map(digest_of)
        .unwrap_or_default();

    // The WHOLE forest, pre-order, as (wire action, originating credential) pairs.
    let mapped = flatten_forest_actions_full(turn, &pre.id_map)
        .ok_or_else(|| "shadow: forest not fully marshallable".to_string())?;

    let mut iter = mapped.into_iter();
    let head = iter
        .next()
        .ok_or_else(|| "shadow: empty mapped forest".to_string())?;

    // The tail actions become `null`-cap delegation children of the root, run SEQUENTIALLY
    // by the Lean executor against the evolving state (no cap handoff). Each child still
    // carries its own credential and is gated per-node by `execFullA`.
    let children: Vec<WChild> = iter
        .map(|m| WChild {
            holder: agent,
            keep: vec![],
            parent_cap: Cap::Null,
            sub: WForest {
                auth: m.wire_auth,
                caveats: vec![],
                action: m.action,
                children: vec![],
            },
        })
        .collect();

    Ok(WireTurn {
        agent,
        nonce: turn.nonce,
        fee: turn.fee as i128,
        valid_until,
        block_height,
        prev_hash,
        root: WForest {
            auth: head.wire_auth,
            caveats: vec![],
            action: head.action,
            children,
        },
    })
}

/// A fully-resolved wire action with its credential (FFI build only).
#[cfg(feature = "lean-shadow")]
struct FullMapped {
    action: WireAction,
    wire_auth: dregg_lean_ffi::marshal::WireAuth,
}

/// Flatten the forest into wire actions paired with their originating credential. Each
/// Rust action's auth decorates every effect-node it produced.
#[cfg(feature = "lean-shadow")]
fn flatten_forest_actions_full(
    turn: &Turn,
    id_map: &HashMap<CellId, u64>,
) -> Option<Vec<FullMapped>> {
    let mut out = Vec::new();
    for root in &turn.call_forest.roots {
        flatten_tree_full(root, id_map, &mut out)?;
    }
    if out.is_empty() {
        return None;
    }
    Some(out)
}

#[cfg(feature = "lean-shadow")]
fn flatten_tree_full(
    tree: &CallTree,
    id_map: &HashMap<CellId, u64>,
    out: &mut Vec<FullMapped>,
) -> Option<()> {
    let actor = *id_map.get(&tree.action.target)?;
    let wire_auth = auth_to_wire(&tree.action.authorization);
    for eff in &tree.action.effects {
        let action = effect_to_wire(actor, eff, id_map)?;
        out.push(FullMapped {
            action,
            wire_auth: wire_auth.clone(),
        });
    }
    for child in &tree.children {
        flatten_tree_full(child, id_map, out)?;
    }
    Some(())
}

// ===================================================================
// AUTH — carry the credential WHO-leg in FULL (no zeroed digests).
// ===================================================================

#[cfg(feature = "lean-shadow")]
fn auth_to_wire(auth: &Authorization) -> dregg_lean_ffi::marshal::WireAuth {
    use dregg_lean_ffi::marshal::{Digest, WireAuth};
    match auth {
        Authorization::Signature(pk, sig) => WireAuth::Signature {
            pubkey: digest_from_halves(pk, sig),
            sig: bytes32_to_nat(sig),
        },
        Authorization::Unchecked => WireAuth::Unchecked,
        Authorization::Breadstuff(token) => WireAuth::Breadstuff {
            token: bytes32_to_nat(token),
        },
        Authorization::Proof {
            proof_bytes,
            bound_action,
            bound_resource,
        } => WireAuth::Proof {
            vk: Digest::from_bytes(blake3_of(proof_bytes)),
            proof: bytes_to_nat(proof_bytes),
            bound_action: str_to_nat(bound_action),
            bound_resource: str_to_nat(bound_resource),
        },
        Authorization::Bearer(proof) => {
            let (deleg_msg, deleg_sig, stark) = match &proof.delegation_proof {
                DelegationProofData::SignedDelegation {
                    delegator_pk,
                    signature,
                    ..
                } => (
                    Digest::from_bytes(*delegator_pk),
                    sig64_to_nat(signature),
                    false,
                ),
                DelegationProofData::StarkDelegation {
                    proof_bytes,
                    root_issuer_commitment,
                } => (
                    Digest::from_bytes(*root_issuer_commitment),
                    bytes_to_nat(proof_bytes),
                    true,
                ),
            };
            WireAuth::Bearer {
                deleg_msg,
                deleg_sig,
                stark,
            }
        }
        Authorization::CapTpDelivered {
            introducer_pk,
            sender_pk,
            sender_signature,
            ..
        } => WireAuth::CapTpDelivered {
            intro_msg: Digest::from_bytes(*introducer_pk),
            sender_msg: Digest::from_bytes(*sender_pk),
            intro_sig: 0,
            sender_sig: sig64_to_nat(sender_signature),
        },
        // The predicate's commitment is the credential WHO-leg the gate reads; carry it in
        // full rather than collapsing to {0,0}.
        Authorization::Custom { predicate } => WireAuth::Custom {
            kind_stmt: Digest::from_bytes(predicate_commitment(predicate)),
            proof: predicate_proof_nat(predicate),
        },
        Authorization::OneOf {
            candidates,
            proof_index,
        } => WireAuth::OneOf {
            candidates: candidates.iter().map(auth_to_wire).collect(),
            proof_index: *proof_index as u64,
        },
        Authorization::Stealth {
            one_time_pubkey,
            ephemeral_pubkey,
            signature,
            ..
        } => WireAuth::Stealth {
            one_time_pk: Digest::from_bytes(*one_time_pubkey),
            ephemeral_pk: Digest::from_bytes(*ephemeral_pubkey),
            sig: sig64_to_nat(signature),
        },
        // The token's issuer key / cell-scoped anchor is the WHO-leg; carry it in full.
        Authorization::Token { key_ref, .. } => match key_ref {
            crate::action::TokenKeyRef::BiscuitIssuer { issuer_pubkey } => WireAuth::Token {
                issuer_key: Digest::from_bytes(*issuer_pubkey),
                sig: 0,
            },
            crate::action::TokenKeyRef::CellScopedMacaroon { cell } => WireAuth::Custom {
                kind_stmt: Digest::from_bytes(cell.0),
                proof: 0,
            },
        },
    }
}

#[cfg(feature = "lean-shadow")]
fn predicate_commitment(p: &dregg_cell::predicate::WitnessedPredicate) -> [u8; 32] {
    // Hash the predicate's serialized form as a stable WHO-commitment. The exact preimage
    // need not match the kernel byte-for-byte (the kernel only reads the digest as an
    // opaque WHO label); what matters is that it is NON-ZERO and tamper-sensitive.
    let bytes = postcard::to_allocvec(p).unwrap_or_default();
    blake3_of(&bytes)
}

#[cfg(feature = "lean-shadow")]
fn predicate_proof_nat(p: &dregg_cell::predicate::WitnessedPredicate) -> u64 {
    let bytes = postcard::to_allocvec(p).unwrap_or_default();
    bytes_to_nat(&bytes)
}

// ---- digest / nat helpers ----

#[cfg(feature = "lean-shadow")]
fn digest_of(hash: [u8; 32]) -> dregg_lean_ffi::marshal::Digest {
    dregg_lean_ffi::marshal::Digest::from_bytes(hash)
}

/// A signature is two 32-byte halves; the "pubkey/message" digest the wire carries for the
/// `Signature` arm is the R half (the first 32 bytes), preserved in full.
#[cfg(feature = "lean-shadow")]
fn digest_from_halves(r: &[u8; 32], _s: &[u8; 32]) -> dregg_lean_ffi::marshal::Digest {
    dregg_lean_ffi::marshal::Digest::from_bytes(*r)
}

#[cfg(feature = "lean-shadow")]
fn blake3_of(bytes: &[u8]) -> [u8; 32] {
    *blake3::hash(bytes).as_bytes()
}

#[cfg(feature = "lean-shadow")]
fn field_index_to_name(index: usize) -> String {
    match index {
        2 => "name".into(),
        3 => "owner".into(),
        4 => "expiry".into(),
        5 => "revoked".into(),
        6 => "target".into(),
        other => format!("field_{other}"),
    }
}

#[cfg(feature = "lean-shadow")]
fn field_to_i128(field: &FieldElement) -> i128 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&field[24..32]);
    u64::from_be_bytes(bytes) as i128
}

#[cfg(feature = "lean-shadow")]
fn field_is_zero(field: &FieldElement) -> bool {
    field.iter().all(|&b| b == 0)
}

#[cfg(feature = "lean-shadow")]
fn bytes32_to_nat(bytes: &[u8; 32]) -> u64 {
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&bytes[24..32]);
    u64::from_be_bytes(buf)
}

#[cfg(feature = "lean-shadow")]
fn sig64_to_nat(sig: &[u8; 64]) -> u64 {
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&sig[56..64]);
    u64::from_be_bytes(buf)
}

#[cfg(feature = "lean-shadow")]
fn bytes_to_nat(bytes: &[u8]) -> u64 {
    let mut buf = [0u8; 8];
    let n = bytes.len().min(8);
    buf[8 - n..].copy_from_slice(&bytes[bytes.len() - n..]);
    u64::from_be_bytes(buf)
}

#[cfg(feature = "lean-shadow")]
fn str_to_nat(s: &str) -> u64 {
    bytes_to_nat(s.as_bytes())
}

#[cfg(feature = "lean-shadow")]
fn permissions_to_i128(_perms: &dregg_cell::Permissions) -> i128 {
    // Permissions are a structured value; the wire `setperms` arm carries a scalar. We
    // encode 0 as a neutral marker (the executor models perms abstractly). This is the one
    // place a structured field collapses; SetPermissions turns are still shadowed for the
    // commit-bit decision, which does not depend on the exact perms scalar.
    0
}

#[cfg(feature = "lean-shadow")]
fn event_data_to_i128(_event: &crate::action::Event) -> i128 {
    0
}
