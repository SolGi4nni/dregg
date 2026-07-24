//! Layer 1: Causal Chaining.
//!
//! Every turn a node produces includes hash-pointers to the latest turns it has seen.
//! This creates a DAG of happened-before relationships. Any node can verify
//! "turn T2 happened after turn T1" by following the hash links.
//!
//! No global ordering needed — just local causal consistency.
//!
//! Production nodes use `dregg_types::CausalDag` directly (re-exported below).
//! `CausalTurn`, `CausalLedger`, and `CausalTurnBuilder` have been deleted —
//! they were not used outside of tests. See Block 4 of the 2026-05-24 cleanup.

use crate::error::CoordError;

// Re-export the shared CausalDag from dregg-types.
pub use dregg_types::CausalDag;

// ─── Verified happened-before (STRONG-FORM swap) ───────────────────────────────

/// Decide `ancestor` happened-before `descendant` on a `CausalDag`. The AUTHORITATIVE verdict is the
/// verified Lean causal-order gate (`Dregg2.Exec.DistributedExports::dregg_coord_causal_order` =
/// `CausalOrder.happenedBefore` decided via `hbBool`), routed through the [`crate::verified_gate`]
/// seam — so the causal layer inherits the partial-order guarantees (`hb_irrefl` / `hb_trans` /
/// `hb_asymm`) by construction.
///
/// FAIL CLOSED: when the verified gate is unavailable (no gate registered / archive lacks the export
/// / an endpoint is absent from the DAG / a wire error), this returns `false` — "not ordered" — the
/// conservative verdict, rather than silently running the native `CausalDag::happened_before` decider
/// on the live path. A production node MUST install the `dregg-exec-lean` gate for a positive
/// happened-before verdict. (`CausalDag::happened_before` remains available as the DAG's own method
/// and is exercised directly by the `coord_diff.rs` differential against the Lean partial order; it is
/// simply no longer the fallback decider here.)
///
/// The DAG is interned to the gate's wire by assigning each turn a small `id` = its position in
/// `topological_order()` (a deterministic linear extension of happened-before, so a dep always
/// carries a strictly-smaller id — the insertion-order discipline the Lean DAG `wf` expects), then
/// emitting `"G=<id:deps|...>;a=<id>;b=<id>"`. The Lean `hbBool` is the transitive closure of the same
/// dependency edges.
pub fn verified_happened_before(
    dag: &CausalDag,
    ancestor: &[u8; 32],
    descendant: &[u8; 32],
) -> bool {
    // Route-through-or-fail-closed: only a positive verdict from the verified Lean gate orders the
    // pair; anything else (gate unavailable / endpoint absent / wire error) is treated as unordered.
    lean_happened_before(dag, ancestor, descendant).unwrap_or(false)
}

/// Query the verified Lean causal-order gate `dregg_coord_causal_order` through the
/// [`crate::verified_gate`] seam. Returns `Some(verdict)` when the gate ran, or `None` when it is
/// unavailable (no gate registered — every FFI-free target / archive lacks the export / either
/// endpoint absent from the DAG) — in which case [`verified_happened_before`] FAILS CLOSED to
/// `false` (not-ordered), never a native decision.
fn lean_happened_before(
    dag: &CausalDag,
    ancestor: &[u8; 32],
    descendant: &[u8; 32],
) -> Option<bool> {
    use std::collections::HashMap;

    let gate = crate::verified_gate::gate()?;
    if !gate.distributed_exports_available() {
        return None;
    }
    // Intern: id = topological position (a linear extension of happened-before, so deps always carry
    // a strictly-smaller id — exactly the insertion-order discipline the Lean DAG `wf` expects).
    let order = dag.topological_order();
    let id_of: HashMap<[u8; 32], usize> = order.iter().enumerate().map(|(i, h)| (*h, i)).collect();
    let a_id = *id_of.get(ancestor)?;
    let b_id = *id_of.get(descendant)?;

    let entries: Vec<String> = order
        .iter()
        .map(|h| {
            let id = id_of[h];
            let mut deps: Vec<usize> = dag
                .deps_of(h)
                .map(|ds| ds.iter().filter_map(|d| id_of.get(d).copied()).collect())
                .unwrap_or_default();
            deps.sort_unstable();
            let deps_str = deps
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join(",");
            format!("{id}:{deps_str}")
        })
        .collect();
    let wire = format!("G={};a={a_id};b={b_id}", entries.join("|"));
    gate.happened_before(&wire)
}

// ─── CoordError conversion ────────────────────────────────────────────────────

/// Convert a `dregg_types::CausalError` into a `CoordError`.
impl From<dregg_types::CausalError> for CoordError {
    fn from(err: dregg_types::CausalError) -> Self {
        match err {
            dregg_types::CausalError::MissingDeps { turn_hash, missing } => {
                CoordError::MissingDependency {
                    turn_hash,
                    dep_hash: missing.into_iter().next().unwrap_or([0; 32]),
                }
            }
            dregg_types::CausalError::Duplicate(hash) => CoordError::DuplicateTurn { hash },
        }
    }
}
