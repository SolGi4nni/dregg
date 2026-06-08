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

/// Decide `ancestor` happened-before `descendant` on a `CausalDag`, STRONG-FORM swap: when the
/// verified Lean causal-order gate is linked (`--features lean-gate`,
/// `Dregg2.Exec.DistributedExports::dregg_coord_causal_order` = `CausalOrder.happenedBefore` decided
/// via `hbBool`), the AUTHORITATIVE verdict comes from the verified Lean — so the causal layer
/// inherits the partial-order guarantees (`hb_irrefl` / `hb_trans` / `hb_asymm`) by construction. The
/// native `CausalDag::happened_before` stays as the DIFFERENTIAL sibling and the fallback when the
/// archive is not linked / the gate is unavailable.
///
/// The DAG is interned to the gate's wire by assigning each turn a small `id` = its position in
/// `topological_order()` (a deterministic linear extension of happened-before, so a dep always
/// carries a strictly-smaller id — the insertion-order discipline the Lean DAG `wf` expects), then
/// emitting `"G=<id:deps|...>;a=<id>;b=<id>"`. The Lean `hbBool` is the transitive closure of the same
/// dependency edges, so the interned verdict equals the native one (the differential checks this).
pub fn verified_happened_before(
    dag: &CausalDag,
    ancestor: &[u8; 32],
    descendant: &[u8; 32],
) -> bool {
    let native = dag.happened_before(ancestor, descendant);
    match lean_happened_before(dag, ancestor, descendant) {
        Some(verified) => verified,
        // Gate unavailable (feature off / archive not linked / endpoint absent) ⇒ native decides.
        None => native,
    }
}

/// Query the verified Lean causal-order gate `dregg_coord_causal_order`. Returns `Some(verdict)` when
/// the gate ran, or `None` when it is unavailable (feature off / archive lacks the export / either
/// endpoint absent from the DAG) so [`verified_happened_before`] falls back to the native Rust.
/// Built `--features lean-gate`; a stub returning `None` otherwise.
#[cfg(feature = "lean-gate")]
fn lean_happened_before(dag: &CausalDag, ancestor: &[u8; 32], descendant: &[u8; 32]) -> Option<bool> {
    use std::collections::HashMap;

    if !dregg_lean_ffi::distributed_exports_available() {
        return None;
    }
    // Intern: id = topological position (a linear extension of happened-before, so deps always carry
    // a strictly-smaller id — exactly the insertion-order discipline the Lean DAG `wf` expects).
    let order = dag.topological_order();
    let id_of: HashMap<[u8; 32], usize> =
        order.iter().enumerate().map(|(i, h)| (*h, i)).collect();
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
    dregg_lean_ffi::verified_happened_before(&wire).ok()
}

/// Stub when the `lean-gate` feature is off: the verified gate is unavailable, so the native Rust
/// `CausalDag::happened_before` decides. Referenced unconditionally in [`verified_happened_before`].
#[cfg(not(feature = "lean-gate"))]
fn lean_happened_before(
    _dag: &CausalDag,
    _ancestor: &[u8; 32],
    _descendant: &[u8; 32],
) -> Option<bool> {
    None
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
