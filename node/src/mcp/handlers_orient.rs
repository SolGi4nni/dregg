//! `mcp::handlers_orient` — split out of the former monolithic `mcp.rs` (pure module move).

use super::*;

pub(super) async fn tool_get_status(state: &NodeState) -> McpToolResult {
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

pub(super) async fn tool_check_capabilities(state: &NodeState) -> McpToolResult {
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

pub(super) async fn tool_read_cell(params: &Value, state: &NodeState) -> McpToolResult {
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

/// A short, agent-legible label for an `AuthRequired` permission requirement.
pub(super) fn auth_required_label(a: &dregg_cell::permissions::AuthRequired) -> &'static str {
    use dregg_cell::permissions::AuthRequired as A;
    match a {
        A::None => "none",
        A::Signature => "signature",
        A::Proof => "proof",
        A::Either => "signature-or-proof",
        A::Impossible => "impossible",
        A::Custom { .. } => "custom-predicate",
    }
}

/// `dregg_list_cells` — paginate over the cells the node holds in its local
/// ledger. The ledger is the agent's MAP of the world it can act on: every
/// grant/transfer/exercise target must already be a cell here. A read-only,
/// idempotent survey — no authority beyond `read`.
///
/// Pagination follows the same cursor convention as resources/list: an opaque
/// `cursor` (a decimal offset) + a `limit` (default `MCP_PAGE_SIZE`). The
/// result carries `next_cursor` when more cells remain.
pub(super) async fn tool_list_cells(params: &Value, state: &NodeState) -> McpToolResult {
    let s = state.read().await;

    let start = params
        .get("cursor")
        .and_then(|v| v.as_str())
        .and_then(|c| c.parse::<usize>().ok())
        .unwrap_or(0);
    let limit = params
        .get("limit")
        .and_then(|v| v.as_u64())
        .map(|n| (n as usize).clamp(1, 200))
        .unwrap_or(MCP_PAGE_SIZE);

    // Stable order: sort by cell id so pagination is deterministic across calls.
    let mut all: Vec<(dregg_cell::CellId, &dregg_cell::Cell)> =
        s.ledger.iter().map(|(id, c)| (*id, c)).collect();
    all.sort_by_key(|a| a.0.0);
    let total = all.len();

    let page: Vec<Value> = all
        .iter()
        .skip(start)
        .take(limit)
        .map(|(id, c)| {
            let is_trustline = crate::trustline_service::trustline_terms_of(c).is_some();
            let is_channel = crate::channels_service::channel_terms_of(c).is_some();
            let kind = if is_trustline {
                "trustline"
            } else if is_channel {
                "channel"
            } else if s.ledger.is_sovereign(id) {
                "sovereign"
            } else {
                "cell"
            };
            serde_json::json!({
                "cell_id": hex_encode(id.as_bytes()),
                "balance": c.state.balance(),
                "nonce": c.state.nonce(),
                "capability_count": c.capabilities.len(),
                "kind": kind,
            })
        })
        .collect();

    let next = next_cursor(start, page.len(), total);

    McpToolResult::json(&serde_json::json!({
        "cells": page,
        "total": total,
        "returned": page.len(),
        "next_cursor": next,
    }))
}

/// `dregg_get_cap_graph` — the OUTGOING capability edges held by a cell: which
/// targets it can reach, under what permission, with what facet/expiry. This is
/// the ocap reachability map an agent needs to plan delegation/exercise without
/// blindly probing. Read-only.
///
/// Defaults to the node's OWN agent cell when `cell_id` is omitted — the most
/// common question ("what can *I* reach?").
pub(super) async fn tool_get_cap_graph(params: &Value, state: &NodeState) -> McpToolResult {
    let s = state.read().await;

    let cell_id = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => dregg_cell::CellId(b),
            Err(_) => {
                return McpToolResult::actionable_error(
                    "invalid hex for cell_id",
                    "pass a 64-hex-char cell id, or omit cell_id to read your own agent cell",
                );
            }
        },
        None => agent_cell_of(&s.cclerk),
    };

    let cell = match s.ledger.get(&cell_id) {
        Some(c) => c,
        None => {
            return McpToolResult::json(&serde_json::json!({
                "cell_id": hex_encode(cell_id.as_bytes()),
                "found": false,
                "edges": [],
            }));
        }
    };

    let edges: Vec<Value> = cell
        .capabilities
        .iter()
        .map(|cap| {
            serde_json::json!({
                "target": hex_encode(cap.target.as_bytes()),
                "slot": cap.slot,
                "permissions": auth_required_label(&cap.permissions),
                "expires_at": cap.expires_at,
                "faceted": cap.allowed_effects.is_some(),
            })
        })
        .collect();

    McpToolResult::json(&serde_json::json!({
        "cell_id": hex_encode(cell_id.as_bytes()),
        "found": true,
        "edge_count": edges.len(),
        "edges": edges,
    }))
}

/// `dregg_get_trustline_status` (ORGANS §1) — read the self-authenticating
/// position of a trustline cell: its line ceiling, the directional parties
/// (issuer→holder), the collateral mode, and the escrow currently backing the
/// line (the cell's own balance). Self-authenticating: a cell is a trustline
/// IFF its installed program VK re-derives from its own term registers, so this
/// never trusts a tamper-able slot to decide what is a trustline. Read-only.
pub(super) async fn tool_get_trustline_status(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id = match params.get("trustline_cell").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => dregg_cell::CellId(b),
            Err(_) => {
                return McpToolResult::actionable_error(
                    "invalid hex for trustline_cell",
                    "pass the 64-hex-char id of a trustline cell (see dregg_list_cells, kind=trustline)",
                );
            }
        },
        None => return McpToolResult::error("missing required parameter: trustline_cell"),
    };

    let s = state.read().await;
    let cell = match s.ledger.get(&cell_id) {
        Some(c) => c,
        None => {
            return McpToolResult::actionable_error(
                format!("cell {} not in ledger", hex_encode(cell_id.as_bytes())),
                "list cells with dregg_list_cells to find a live trustline",
            );
        }
    };

    let (terms, collateral) = match crate::trustline_service::trustline_terms_of(cell) {
        Some(tc) => tc,
        None => {
            return McpToolResult::actionable_error(
                format!(
                    "cell {} is not a trustline (program VK does not re-derive from its terms)",
                    hex_encode(cell_id.as_bytes())
                ),
                "use dregg_list_cells and look for kind=trustline",
            );
        }
    };

    let escrow = u64::try_from(cell.state.balance()).unwrap_or(0);
    let collateral_label = match collateral {
        dregg_cell::blueprint::TrustlineCollateral::FullReserve => "fullReserve",
        dregg_cell::blueprint::TrustlineCollateral::PureCredit => "pureCredit",
    };

    McpToolResult::json(&serde_json::json!({
        "trustline_cell": hex_encode(cell_id.as_bytes()),
        "is_trustline": true,
        "line": terms.line,
        "issuer": hex_encode(&terms.issuer),
        "holder": hex_encode(&terms.holder),
        "collateral": collateral_label,
        "escrow_balance": escrow,
    }))
}

/// `dregg_get_channel_status` (ORGANS §4) — read the self-authenticating terms
/// of a channel-group cell: its governance admin key and group tag. A cell is a
/// channel IFF its installed program VK re-derives from its own term registers.
/// Read-only. (Live membership/epoch/key-commit are program-state in private
/// slots; this surface reports the immutable group identity.)
pub(super) async fn tool_get_channel_status(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id = match params.get("channel_cell").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => dregg_cell::CellId(b),
            Err(_) => {
                return McpToolResult::actionable_error(
                    "invalid hex for channel_cell",
                    "pass the 64-hex-char id of a channel cell (see dregg_list_cells, kind=channel)",
                );
            }
        },
        None => return McpToolResult::error("missing required parameter: channel_cell"),
    };

    let s = state.read().await;
    let cell = match s.ledger.get(&cell_id) {
        Some(c) => c,
        None => {
            return McpToolResult::actionable_error(
                format!("cell {} not in ledger", hex_encode(cell_id.as_bytes())),
                "list cells with dregg_list_cells to find a live channel",
            );
        }
    };

    let terms = match crate::channels_service::channel_terms_of(cell) {
        Some(t) => t,
        None => {
            return McpToolResult::actionable_error(
                format!(
                    "cell {} is not a channel group (program VK does not re-derive from its terms)",
                    hex_encode(cell_id.as_bytes())
                ),
                "use dregg_list_cells and look for kind=channel",
            );
        }
    };

    McpToolResult::json(&serde_json::json!({
        "channel_cell": hex_encode(cell_id.as_bytes()),
        "is_channel": true,
        "admin": hex_encode(&terms.admin),
        "tag": hex_encode(&terms.tag),
    }))
}

/// Render a `CellProgram` into a JSON value that exposes its kind and
/// (for predicate programs) the full structured `StateConstraint` list.
///
/// This is the slot-caveat surface on the MCP read path: callers can
/// discover what invariants the cell's program enforces on every turn
/// without having to peek into postcard bytes.
pub(super) fn describe_cell_program(program: &dregg_cell::CellProgram) -> serde_json::Value {
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

pub(super) async fn tool_get_receipt_chain(params: &Value, state: &NodeState) -> McpToolResult {
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

pub(super) async fn tool_verify_provenance(params: &Value, state: &NodeState) -> McpToolResult {
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

    // ⚑ `factory_match` IS GONE (2026-07-30). It reported a boolean that was a pure
    // function of whether the caller passed a parameter, on a tool titled "Verify Cell
    // Provenance":
    //
    //   * `expected_factory_vk` ABSENT  -> `true`. Nothing was checked; the tool said
    //     "match".
    //   * `expected_factory_vk` PRESENT -> `false`, ALWAYS. It built the comparison from
    //     `Provenance::from_factory(vk, None, 0)`, which hard-sets
    //     `derivation_param_hash: None` (`cell/src/factory.rs:788`), and
    //     `verify_derivation` returns `false` on that arm (`:812-818`). It also passed a
    //     CELL ID where the parameter is `cell_program_vk`, so even with a param hash it
    //     would compare a derived child VK against an identifier.
    //
    // Zero provenance information in either direction. The honest reason is that this node
    // STORES no provenance record — nothing in the ledger or cell state carries a
    // `Provenance` — so the two inputs a real derivation check needs (the cell's committed
    // program VK and the factory's derivation parameter hash) are not available here at
    // all. The tool now says that instead of emitting a boolean that reads as a verdict.
    let derivation_check = match expected_factory {
        None => serde_json::json!({
            "ran": false,
            "reason": "no expected_factory_vk supplied — nothing to check against. This is \
                       NOT a match: absence of a check is not a passing check.",
        }),
        Some(hex) => match hex_decode(hex) {
            Err(_) => serde_json::json!({
                "ran": false,
                "reason": "expected_factory_vk is not 64 hex chars",
            }),
            Ok(_) => serde_json::json!({
                "ran": false,
                "reason": "this node holds NO provenance record for any cell: neither the \
                           ledger nor the cell state stores a `Provenance`, so the cell's \
                           committed program VK and the factory's derivation_param_hash — \
                           both inputs to ChildVkStrategy::derive_child_vk — are unavailable. \
                           A derivation check cannot be run here, and this tool will not \
                           report one it did not run.",
            }),
        },
    };

    McpToolResult::json(&serde_json::json!({
        "cell_id": cell_id_hex,
        // Renamed from `has_provenance`, which measured only "this cell id is in my local
        // ledger" while its name promised a provenance record was found.
        "known_to_this_node": is_hosted || is_sovereign,
        "is_sovereign": is_sovereign,
        "is_hosted": is_hosted,
        "factory_derivation_verified": false,
        "factory_derivation_check": derivation_check,
        "note": if is_sovereign {
            "Cell is sovereign (commitment-only registration). Its FACTORY PROVENANCE is \
             NOT verified — see factory_derivation_check."
        } else if is_hosted {
            "Cell is hosted (full state in federation). Its FACTORY PROVENANCE is NOT \
             verified — see factory_derivation_check."
        } else {
            "Cell not found in ledger."
        },
    }))
}

// =============================================================================
// Effect VM tools
// =============================================================================

pub(super) async fn tool_get_blocklace_status(state: &NodeState) -> McpToolResult {
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

pub(super) async fn tool_get_constitution(state: &NodeState) -> McpToolResult {
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

pub(super) async fn tool_check_resource_budget(params: &Value, state: &NodeState) -> McpToolResult {
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

pub(super) async fn tool_list_auctions(_params: &Value, state: &NodeState) -> McpToolResult {
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
