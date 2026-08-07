//! Pipeline execution: batched turns with EventualRef/PipelinedSend resolution.

use std::collections::HashMap;

use dregg_cell::{CellId, Ledger};

use crate::action::Effect;
use crate::eventual::{EventualRef, Pipeline, PipelineError, TurnOutput};
use crate::turn::{Turn, TurnReceipt, TurnResult};

use super::TurnExecutor;

/// A resolution table mapping (turn_hash, output_slot) to concrete outputs.
pub type ResolutionTable = HashMap<([u8; 32], u32), TurnOutput>;

/// Resolve a `TurnOutput` to a concrete `CellId`.
///
/// - `CreatedCell` → the created cell's ID
/// - `GrantedCapability` → the target cell that received the capability
/// - `StateUpdate` → the cell whose state was updated
/// - `CreatedNote` → cannot be resolved to a CellId (returns error)
fn resolve_output_to_cell_id(
    output: &TurnOutput,
    eventual_ref: &EventualRef,
) -> Result<CellId, PipelineError> {
    match output {
        TurnOutput::CreatedCell { cell } => Ok(*cell),
        TurnOutput::GrantedCapability { target, .. } => Ok(*target),
        TurnOutput::StateUpdate { cell, .. } => Ok(*cell),
        TurnOutput::CreatedNote { .. } => Err(PipelineError::UnresolvedRef {
            eventual_ref: eventual_ref.clone(),
            reason: "CreatedNote output cannot be resolved to a CellId".to_string(),
        }),
    }
}

/// Resolve all `PipelinedSend` effects in a turn's call forest using the resolution table.
///
/// Each `PipelinedSend { target: EventualRef, action }` is resolved by:
/// 1. Looking up the EventualRef in the resolution table to get a concrete CellId
/// 2. Replacing the PipelinedSend effect with the inner action's effects,
///    re-targeted to the resolved CellId
/// 3. Adding the inner action as a new root in the call forest
///
/// Returns the resolved turn, or a PipelineError if resolution fails.
fn resolve_turn(turn: &Turn, table: &ResolutionTable) -> Result<Turn, PipelineError> {
    let mut resolved_turn = turn.clone();
    let mut new_roots: Vec<crate::forest::CallTree> = Vec::new();

    for root in &mut resolved_turn.call_forest.roots {
        resolve_tree_effects(root, table, &mut new_roots)?;
    }

    // Append any newly created roots from resolved PipelinedSend effects.
    for new_root in new_roots {
        resolved_turn.call_forest.roots.push(new_root);
    }

    Ok(resolved_turn)
}

/// Recursively resolve PipelinedSend effects in a call tree.
///
/// PipelinedSend effects are removed from the current tree's action and their
/// inner actions are added as new roots (with the resolved target).
///
/// Placeholder convention: if the inner action's target is `CellId::from_bytes([0u8; 32])`,
/// it is replaced with the resolved CellId. Similarly, effects referencing the
/// placeholder are rewritten to use the resolved CellId.
fn resolve_tree_effects(
    tree: &mut crate::forest::CallTree,
    table: &ResolutionTable,
    new_roots: &mut Vec<crate::forest::CallTree>,
) -> Result<(), PipelineError> {
    let mut remaining_effects: Vec<Effect> = Vec::new();

    for effect in std::mem::take(&mut tree.action.effects) {
        match effect {
            Effect::PipelinedSend {
                ref target,
                ref action,
            } => {
                // Resolve the EventualRef to a concrete CellId.
                let output = resolve_eventual_ref(target, table)?;
                let resolved_cell_id = resolve_output_to_cell_id(output, target)?;

                // Create a new action with the resolved target.
                let placeholder = CellId::from_bytes([0u8; 32]);
                let mut resolved_action = action.as_ref().clone();

                // If the inner action's target is the placeholder, replace it.
                if resolved_action.target == placeholder {
                    resolved_action.target = resolved_cell_id;
                }

                // Rewrite placeholder CellIds in effects.
                rewrite_effect_targets(
                    &mut resolved_action.effects,
                    &placeholder,
                    &resolved_cell_id,
                );

                // Add as a new root action in the forest.
                new_roots.push(crate::forest::CallTree::new(resolved_action));
            }
            other => {
                remaining_effects.push(other);
            }
        }
    }

    tree.action.effects = remaining_effects;

    // Recurse into children.
    for child in &mut tree.children {
        resolve_tree_effects(child, table, new_roots)?;
    }

    Ok(())
}

/// Rewrite placeholder CellIds in effects with the resolved concrete CellId.
///
/// This allows PipelinedSend inner actions to use `CellId::from_bytes([0u8; 32])`
/// as a placeholder meaning "the cell resolved from the EventualRef". After resolution,
/// all occurrences of the placeholder are replaced with the actual CellId.
fn rewrite_effect_targets(effects: &mut [Effect], placeholder: &CellId, resolved: &CellId) {
    for effect in effects.iter_mut() {
        match effect {
            Effect::SetField { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::Transfer { from, to, .. } => {
                if from == placeholder {
                    *from = *resolved;
                }
                if to == placeholder {
                    *to = *resolved;
                }
            }
            Effect::GrantCapability { from, to, cap } => {
                if from == placeholder {
                    *from = *resolved;
                }
                if to == placeholder {
                    *to = *resolved;
                }
                if cap.target == *placeholder {
                    cap.target = *resolved;
                }
            }
            Effect::RevokeCapability { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::EmitEvent { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::IncrementNonce { cell } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::SetPermissions { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::SetVerificationKey { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::RotatePqIdentity { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::SetProgram { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::Introduce {
                introducer,
                recipient,
                target,
                ..
            } => {
                if introducer == placeholder {
                    *introducer = *resolved;
                }
                if recipient == placeholder {
                    *recipient = *resolved;
                }
                if target == placeholder {
                    *target = *resolved;
                }
            }

            // ExerciseViaCapability: recurse into inner_effects for rewriting.
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                rewrite_effect_targets(inner_effects, placeholder, resolved);
            }
            // CapTP variants have mutable CellId fields (target, bearer):
            Effect::Refusal { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::CellSeal { target, .. } => {
                if target == placeholder {
                    *target = *resolved;
                }
            }
            Effect::CellUnseal { target } => {
                if target == placeholder {
                    *target = *resolved;
                }
            }
            Effect::CellDestroy { target, .. } => {
                if target == placeholder {
                    *target = *resolved;
                }
            }
            Effect::Burn { target, .. } => {
                if target == placeholder {
                    *target = *resolved;
                }
            }
            Effect::Mint { target, .. } => {
                if target == placeholder {
                    *target = *resolved;
                }
            }
            Effect::AttenuateCapability { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            // ReceiptArchive carries an ArchivalAttestation that pins
            // its own cell_id; rewriting it would invalidate the
            // attestation's hash. Submitters must construct the
            // attestation with the resolved CellId already in place.
            Effect::ReceiptArchive { .. } => {}
            // Promise: rewrite the holding cell. (The committed `wake` turn's
            // agent is fixed at construction — a placeholder would corrupt the
            // hole-id hash, so we do not rewrite into it.)
            Effect::Promise { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            // Notify: rewrite sender/recipient.
            Effect::Notify { from, to, .. } => {
                if from == placeholder {
                    *from = *resolved;
                }
                if to == placeholder {
                    *to = *resolved;
                }
            }
            // React's `pending_id` is a NULLIFIER (a hole-id), not a CellId, and
            // the carried `wake`/proof are content-addressed — nothing to rewrite.
            Effect::React { .. } => {}
            // No CellId fields to rewrite (or birth effects whose ids are derived).
            Effect::CreateCell { .. }
            | Effect::CreateHybridCell { .. }
            | Effect::NoteSpend { .. }
            | Effect::NoteCreate { .. }
            | Effect::BridgeMint { .. }
            | Effect::PipelinedSend { .. }
            | Effect::SpawnWithDelegation { .. }
            | Effect::RefreshDelegation { .. }
            | Effect::RevokeDelegation { .. }
            | Effect::MakeSovereign { .. }
            // ShieldedTransfer carries only nullifiers / commitments / proofs —
            // no CellId fields to rewrite.
            | Effect::ShieldedTransfer { .. }
            // Shield carries only values / a nullifier / a commitment / proofs —
            // no CellId fields to rewrite.
            | Effect::Shield { .. }
            // Custom's `cell` is a concrete, pre-registered SOVEREIGN cell (a
            // custom transition is only admissible on the proof-carrying sovereign
            // path against an already-registered commitment) — never a pipeline
            // output placeholder, so there is nothing to resolve here.
            | Effect::Custom { .. }
            | Effect::CreateCellFromFactory { .. } => {} // These effects don't have mutable CellId fields needing rewrite:
        }
    }
}
/// Execute a batch of turns against a ledger in topological order.
///
/// **This is the only pipeline entry point.** Before executing each turn, any
/// `PipelinedSend` effects are resolved using the resolution table (built from outputs of
/// previously-committed turns). Turns can reference outputs of earlier turns via
/// `EventualRef` (OutputRef), and the batch executor resolves them in causal order.
///
/// Each turn's `depends_on` hashes are verified against the set of committed
/// receipt hashes within this batch. If a turn declares a dependency on a hash
/// that hasn't been committed, the turn is rejected.
///
/// When `pipeline.atomic` is set, ANY failure rolls the whole batch back to the
/// pre-batch ledger image and every result is reported as failed.
///
/// ⚑ Both of those sentences used to be true of only one of TWO near-identical entry
/// points. `execute_pipeline_result` (deleted 2026-08-05) was a zero-caller copy that
/// **omitted the `depends_on` verification above** while being the only function that
/// honored `pipeline.atomic` — so the live entry silently ignored `atomic`, and the
/// variant that implemented it silently dropped a check. Both halves are folded in here;
/// there is now one pipeline executor and it does both.
pub fn execute_pipeline(
    pipeline: Pipeline,
    ledger: &mut Ledger,
    executor: &TurnExecutor,
) -> Vec<Result<TurnReceipt, PipelineError>> {
    let n = pipeline.turns.len();
    if n == 0 {
        return vec![];
    }

    let topo_order = match pipeline.topological_order() {
        Ok(order) => order,
        Err(cycle) => {
            return vec![Err(PipelineError::Cycle(cycle)); n];
        }
    };

    // Atomic batches keep the pre-batch ledger image so a single failure can restore it.
    let ledger_snapshot = if pipeline.atomic {
        Some(ledger.clone())
    } else {
        None
    };

    let mut results: Vec<Option<Result<TurnReceipt, PipelineError>>> = vec![None; n];
    let mut failed: Vec<bool> = vec![false; n];
    let mut resolution_table: ResolutionTable = HashMap::new();
    // Track committed turn hashes for depends_on verification.
    let mut committed_hashes: std::collections::HashSet<[u8; 32]> =
        std::collections::HashSet::new();

    // Pre-compute turn hashes for resolution table keying.
    let turn_hashes: Vec<[u8; 32]> = pipeline.turns.iter().map(|t| t.hash()).collect();

    for &idx in &topo_order {
        // Check explicit dependency edges (from add_dependency).
        let deps = pipeline.dependencies_of(idx);
        let mut dep_failed = None;
        for dep_idx in &deps {
            if failed[*dep_idx] {
                dep_failed = Some(*dep_idx);
                break;
            }
        }

        if let Some(failed_dep) = dep_failed {
            failed[idx] = true;
            results[idx] = Some(Err(PipelineError::DependencyFailed {
                failed_index: failed_dep,
                dependent_index: idx,
            }));
            continue;
        }

        // Verify depends_on hashes: all must be committed within this batch.
        let turn = &pipeline.turns[idx];
        let mut depends_on_unmet = false;
        for dep_hash in &turn.depends_on {
            if !committed_hashes.contains(dep_hash) {
                let dep_idx_opt = turn_hashes.iter().position(|h| h == dep_hash);
                if let Some(dep_idx) = dep_idx_opt {
                    failed[idx] = true;
                    results[idx] = Some(Err(PipelineError::DependencyFailed {
                        failed_index: dep_idx,
                        dependent_index: idx,
                    }));
                } else {
                    failed[idx] = true;
                    results[idx] = Some(Err(PipelineError::MissingDependency {
                        turn_index: idx,
                        missing_hash: *dep_hash,
                    }));
                }
                depends_on_unmet = true;
                break;
            }
        }
        if depends_on_unmet {
            continue;
        }

        // Resolve EventualRefs in this turn before executing it.
        let mut resolved_turn = match resolve_turn(turn, &resolution_table) {
            Ok(t) => t,
            Err(e) => {
                failed[idx] = true;
                results[idx] = Some(Err(e));
                continue;
            }
        };

        // P0-3: auto-chain previous_receipt_hash from the executor's per-agent
        // head when the turn doesn't already specify one. Pipeline turns are
        // commonly assembled before knowing the receipt-chain head, so the
        // pipeline executor fills it in here. Turns that explicitly set
        // `previous_receipt_hash` are NOT overridden -- the explicit value
        // will be checked against the head and rejected if mismatched.
        if resolved_turn.previous_receipt_hash.is_none() {
            if let Some(prev) = executor.get_last_receipt_hash(&resolved_turn.agent) {
                resolved_turn.previous_receipt_hash = Some(prev);
            }
        }

        let result = executor.execute(&resolved_turn, ledger);

        match result {
            TurnResult::Committed { receipt, .. } => {
                committed_hashes.insert(turn_hashes[idx]);
                let outputs = extract_turn_outputs(&resolved_turn, ledger);
                let turn_hash = turn_hashes[idx];
                for (slot, output) in outputs.into_iter().enumerate() {
                    resolution_table.insert((turn_hash, slot as u32), output);
                }
                results[idx] = Some(Ok(receipt));
            }
            TurnResult::Rejected { reason, .. } => {
                failed[idx] = true;
                results[idx] = Some(Err(PipelineError::TurnExecutionFailed {
                    index: idx,
                    reason: format!("{}", reason),
                }));
            }
            TurnResult::Expired | TurnResult::Pending => {
                failed[idx] = true;
                results[idx] = Some(Err(PipelineError::TurnExecutionFailed {
                    index: idx,
                    reason: "conditional turn not resolved in batch context".to_string(),
                }));
            }
        }
    }

    // Atomic batch, any failure: restore the pre-batch ledger and report every turn as
    // failed — a turn whose effects were just rolled back did not commit, so returning its
    // receipt would name a state that no longer exists.
    if pipeline.atomic && failed.iter().any(|f| *f) {
        if let Some(snap) = ledger_snapshot {
            *ledger = snap;
        }
        let mut rolled: Vec<Result<TurnReceipt, PipelineError>> = Vec::with_capacity(n);
        for (i, slot) in results.iter_mut().enumerate() {
            match slot.take() {
                Some(Err(e)) => rolled.push(Err(e)),
                _ => rolled.push(Err(PipelineError::TurnExecutionFailed {
                    index: i,
                    reason: "atomic rollback".to_string(),
                })),
            }
        }
        return rolled;
    }

    results
        .into_iter()
        .map(|r| r.unwrap_or(Err(PipelineError::Empty)))
        .collect()
}

/// Extract outputs from a committed turn's effects for the resolution table.
///
/// Output slots are assigned deterministically: effects are enumerated by DFS traversal
/// of the call forest (root 0 first, depth-first through children, then root 1, etc.).
/// Within each action node, effects are enumerated in declaration order. Only effects
/// that produce externally-referenceable outputs (CreateCell, GrantCapability, SetField,
/// NoteCreate, SpawnWithDelegation) receive a slot number.
fn extract_turn_outputs(turn: &Turn, ledger: &Ledger) -> Vec<TurnOutput> {
    let mut outputs = Vec::new();
    for root in &turn.call_forest.roots {
        extract_tree_outputs(root, ledger, &mut outputs);
    }
    outputs
}

fn extract_tree_outputs(
    tree: &crate::forest::CallTree,
    ledger: &Ledger,
    outputs: &mut Vec<TurnOutput>,
) {
    for effect in &tree.action.effects {
        match effect {
            crate::action::Effect::CreateCell {
                public_key,
                token_id,
                ..
            } => {
                let cell_id = dregg_cell::CellId::derive_raw(public_key, token_id);
                outputs.push(TurnOutput::CreatedCell { cell: cell_id });
            }
            crate::action::Effect::CreateHybridCell {
                public_key,
                token_id,
                ..
            } => {
                let cell_id = dregg_cell::CellId::derive_raw(public_key, token_id);
                outputs.push(TurnOutput::CreatedCell { cell: cell_id });
            }
            crate::action::Effect::GrantCapability { to, .. } => {
                let slot = if let Some(cell) = ledger.get(to) {
                    cell.capabilities.len().saturating_sub(1) as u32
                } else {
                    0
                };
                outputs.push(TurnOutput::GrantedCapability { target: *to, slot });
            }
            crate::action::Effect::SetField { cell, index, value } => {
                outputs.push(TurnOutput::StateUpdate {
                    cell: *cell,
                    field: *index,
                    hash: *value,
                });
            }
            crate::action::Effect::NoteCreate { commitment, .. } => {
                outputs.push(TurnOutput::CreatedNote {
                    commitment: commitment.0,
                });
            }
            crate::action::Effect::SpawnWithDelegation {
                child_public_key,
                child_token_id,
                ..
            } => {
                let cell_id = dregg_cell::CellId::derive_raw(child_public_key, child_token_id);
                outputs.push(TurnOutput::CreatedCell { cell: cell_id });
            }
            _ => {}
        }
    }
    for child in &tree.children {
        extract_tree_outputs(child, ledger, outputs);
    }
}

/// Resolve an EventualRef against the resolution table.
pub fn resolve_eventual_ref<'a>(
    eventual_ref: &crate::eventual::EventualRef,
    table: &'a ResolutionTable,
) -> Result<&'a TurnOutput, PipelineError> {
    table
        .get(&(eventual_ref.source_turn, eventual_ref.output_slot))
        .ok_or_else(|| PipelineError::UnresolvedRef {
            eventual_ref: eventual_ref.clone(),
            reason: "output slot not found in resolution table".to_string(),
        })
}
