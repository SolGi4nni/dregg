//! Optional Lean FFI shadow execution — compares Rust commit decisions against the
//! verified Lean kernel without affecting [`crate::turn::TurnResult`].
//!
//! Enabled when `DREGG_LEAN_SHADOW=1` and `dregg_lean_ffi::lean_available()`.
//! For now only single-action, single-`SetField` turns are shadowed (starbridge app shape).

use std::cell::RefCell;
use std::collections::HashMap;

use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, Ledger};

use crate::action::{Action, Authorization, Effect};
use crate::forest::CallTree;
use crate::turn::{Turn, TurnResult};

/// Minimal pre-execution ledger snapshot for shadow marshalling.
#[derive(Clone, Debug)]
struct ShadowPreLedger {
    cells: HashMap<CellId, Cell>,
    id_map: HashMap<CellId, u64>,
}

thread_local! {
    static SHADOW_PRE: RefCell<Option<ShadowPreLedger>> = const { RefCell::new(None) };
}

/// Capture a minimal pre-state snapshot when shadow mode may run later.
///
/// Call at the start of [`crate::executor::TurnExecutor::execute`] before any
/// ledger mutation so the Lean oracle sees the same admission inputs as Rust.
pub fn capture_pre_state_if_eligible(turn: &Turn, ledger: &Ledger) {
    let snapshot = if shadow_env_enabled() && is_setfield_only_single_action(turn) {
        Some(build_pre_ledger(turn, ledger))
    } else {
        None
    };
    SHADOW_PRE.with(|slot| *slot.borrow_mut() = snapshot);
}

/// Shadow-execute eligible turns against the Lean kernel and log divergences.
///
/// Uses the pre-execution snapshot stored by [`capture_pre_state_if_eligible`].
/// The `ledger` argument matches the public API; marshalling uses the captured pre-state.
pub fn maybe_shadow_turn(turn: &Turn, ledger: &Ledger, result: &TurnResult) {
    let _ = ledger;
    if !shadow_env_enabled() {
        SHADOW_PRE.with(|slot| slot.borrow_mut().take());
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

        if !is_setfield_only_single_action(turn) {
            return;
        }

        match run_shadow(turn, &pre) {
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

/// True for exactly one root action with one `SetField` effect and no children.
fn is_setfield_only_single_action(turn: &Turn) -> bool {
    if turn.call_forest.roots.len() != 1 {
        return false;
    }
    let root = &turn.call_forest.roots[0];
    if !root.children.is_empty() {
        return false;
    }
    matches!(
        sole_setfield_effect(&root.action),
        Some(_)
    )
}

fn sole_setfield_effect(action: &Action) -> Option<&Effect> {
    let mut setfield = None;
    for effect in &action.effects {
        match effect {
            Effect::SetField { .. } => {
                if setfield.is_some() {
                    return None;
                }
                setfield = Some(effect);
            }
            _ => return None,
        }
    }
    setfield
}

fn build_pre_ledger(turn: &Turn, ledger: &Ledger) -> ShadowPreLedger {
    let mut ids = vec![turn.agent];
    if let Some(root) = turn.call_forest.roots.first() {
        if let Some(Effect::SetField { cell, .. }) = sole_setfield_effect(&root.action) {
            if *cell != turn.agent {
                ids.push(*cell);
            }
        }
    }
    ids.sort();
    ids.dedup();

    let mut id_map = HashMap::new();
    for (i, id) in ids.iter().enumerate() {
        id_map.insert(*id, i as u64);
    }

    let mut cells = HashMap::new();
    for id in ids {
        if let Some(cell) = ledger.get(&id) {
            cells.insert(id, cell.clone());
        }
    }

    ShadowPreLedger { cells, id_map }
}

#[cfg(feature = "lean-shadow")]
fn run_shadow(turn: &Turn, pre: &ShadowPreLedger) -> Result<bool, String> {
    use dregg_lean_ffi::marshal::marshal_turn;

    let root = &turn.call_forest.roots[0];
    let wire_state = ledger_to_wire_state(pre)?;
    let wire_turn = turn_to_wire_turn(turn, root, pre)?;
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
        let cell = pre
            .cells
            .get(cell_id)
            .ok_or_else(|| format!("shadow pre-ledger missing cell {cell_id}"))?;
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
    root: &CallTree,
    pre: &ShadowPreLedger,
) -> Result<dregg_lean_ffi::marshal::WireTurn, String> {
    use dregg_lean_ffi::marshal::{WireAction, WireTurn, WForest};

    let agent = *pre
        .id_map
        .get(&turn.agent)
        .ok_or_else(|| "shadow: agent cell not in id map".to_string())?;

    let Effect::SetField { cell, index, value } = sole_setfield_effect(&root.action).unwrap() else {
        return Err("shadow: expected sole SetField".into());
    };
    let target = *pre
        .id_map
        .get(cell)
        .ok_or_else(|| "shadow: target cell not in id map".to_string())?;

    let valid_until = turn
        .valid_until
        .and_then(|v| u64::try_from(v).ok())
        .ok_or_else(|| "shadow: turn.valid_until required for wire marshal".to_string())?;

    let prev_hash = turn
        .previous_receipt_hash
        .map(hash_to_nat)
        .unwrap_or(0);

    let action = WireAction::SetField {
        actor: agent,
        cell: target,
        field: field_index_to_name(*index),
        v: field_to_i128(value),
    };

    Ok(WireTurn {
        agent,
        nonce: turn.nonce,
        fee: turn.fee as i128,
        valid_until,
        prev_hash,
        root: WForest {
            auth: auth_to_wire(&root.action.authorization),
            caveats: vec![],
            action,
            children: vec![],
        },
    })
}

#[cfg(feature = "lean-shadow")]
fn auth_to_wire(auth: &Authorization) -> dregg_lean_ffi::marshal::WireAuth {
    use dregg_lean_ffi::marshal::WireAuth;
    match auth {
        Authorization::Signature(pk, sig) => WireAuth::Signature {
            pubkey: bytes32_to_nat(pk),
            sig: bytes32_to_nat(sig),
        },
        Authorization::Unchecked => WireAuth::Unchecked,
        Authorization::Breadstuff(token) => WireAuth::Breadstuff {
            token: bytes32_to_nat(token),
        },
        Authorization::Custom { .. } => WireAuth::Custom {
            kind_stmt: 0,
            proof: 0,
        },
        Authorization::Token { .. } => WireAuth::Token {
            issuer_key: 0,
            sig: 0,
        },
        _ => WireAuth::Unchecked,
    }
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
fn hash_to_nat(hash: [u8; 32]) -> u64 {
    bytes32_to_nat(&hash)
}