//! **THE EXECUTOR-DRIVE SEAM CLOSED — a document edit runs through the genuine
//! [`dregg_turn::TurnExecutor`], so it is cap-gated, finalized, and journaled.**
//! (DOCUMENT-LANGUAGE.md §3.3 per-region edit caps, §4.3 dregg-native.)
//!
//! [`crate::doccell::DocCell::edit`] desugars an [`Op`] to genuine
//! [`Effect::SetField`] writes and assembles the [`TurnReceipt`] *directly* — so
//! it bypasses the executor's permission gate, capability consumption, and the
//! `LedgerJournal`. That is the self-sovereign authoring path (the receipt's
//! `finality` is honestly `Tentative`). This module closes that seam: an edit
//! is built into a real [`dregg_turn::Turn`] and run through
//! [`TurnExecutor::execute`], the **sole entry point for ledger state
//! mutations**. The edit therefore goes through the *real* spine:
//!
//! - **Cap-gated.** The author is a distinct *editor cell*; the document is a
//!   separate *region cell*. A `SetField` whose target (the region cell) is not
//!   the actor (the editor) triggers the executor's
//!   [`check_cross_cell_permission`] gate — the editor must hold a c-list
//!   capability to the region cell, or the effect is **refused in-band** with
//!   [`TurnError::CapabilityNotHeld`] (NOT a panic). This is the seam where
//!   per-region edit caps (DOCUMENT-LANGUAGE §3.3's `{view, comment, edit,
//!   admin}`) become enforceable: an editor that lacks the region cap cannot
//!   edit that region.
//! - **Finalized.** The executor's single-node commit path produces a receipt
//!   with [`Finality::Final`] (NOT `Tentative`) — driving through the real
//!   executor *is* the finality upgrade.
//! - **Journaled.** The executor walks its `LedgerJournal` (rollback on any
//!   effect failure), meters computrons, advances the agent's nonce and
//!   receipt-chain head — the full `simulate → commit` spine, not a hand-rolled
//!   receipt.
//!
//! ## The projection: the document rides the cell's committed `fields_map`
//!
//! The executor's `apply_set_field` heap arm writes `set_field_ext(key)` for any
//! `key >= STATE_SLOTS` — the cell's committed overflow map (`fields_map`,
//! digested into `fields_root`, which the canonical state commitment absorbs).
//! So the executor-driven projection lays the document's atoms / edges / fields
//! into that map under a flat key
//! [`field_key`]` = STATE_SLOTS + ((collection as u64) << 32) | (key as u64)`.
//! Distinct `(collection, key)` heap addresses get distinct field keys (the same
//! injective scheme [`crate::project_graph`] uses, lifted past the 16 fixed
//! register slots), so the document commitment is the genuine `fields_root` the
//! executor writes — a light client trusts the same root the executor moves.
//!
//! ## What remains (the federation/finality tail, named honestly)
//!
//! The executor commits on a *single node* (`Finality::Final` is the solo-mode
//! commit). True BFT quorum / federation finality (multiple nodes validating the
//! same turn, a quorum certificate) is the node-layer's job and is NOT exercised
//! here — `dregg-doc` drives the executor, not a federation. The receipt is a
//! genuine finalized single-node receipt; the cross-node quorum is the remaining
//! tail.

use crate::patch::Patch;
use crate::substrate::to_heap_map as project_graph;
use dregg_cell::{
    AuthRequired, Cell, CellId, Ledger, Permissions, STATE_SLOTS,
    compute_canonical_state_commitment,
};
use dregg_turn::{
    ActionBuilder, ComputronCosts, Effect, TurnBuilder, TurnError, TurnExecutor, TurnReceipt,
    TurnResult,
};

/// Map a document heap address `(collection, key)` to the flat committed-map key
/// the executor's `set_field_ext` arm writes. Lifted past the fixed
/// `STATE_SLOTS` register file so it lands in `fields_map` (digested into
/// `fields_root`), and bijective in `(collection, key)`.
pub fn field_key(collection: u32, key: u32) -> u64 {
    STATE_SLOTS as u64 + (((collection as u64) << 32) | (key as u64))
}

/// A document driven through the REAL [`TurnExecutor`].
///
/// Owns a [`Ledger`] holding the *region cell* (the document, committed over its
/// `fields_root`) and the *editor cell* (the author identity). An edit is built
/// into a genuine [`dregg_turn::Turn`] and run through [`TurnExecutor::execute`]
/// — cap-gated, finalized, journaled. The witness [`crate::graph::DocGraph`] is
/// kept in lockstep only on a *committed* edit; a refused edit leaves the
/// document untouched (the executor rolled the ledger back, and we roll the
/// witness graph back too).
pub struct ExecutorDrivenDoc {
    ledger: Ledger,
    executor: TurnExecutor,
    /// The document cell — the edit's target; committed over its `fields_root`.
    region: CellId,
    /// The author/editor cell — the turn's agent; holds (or lacks) the cap to
    /// `region` that gates the edit.
    editor: CellId,
    /// The in-crate witness graph the patch algebra reads (merge, content,
    /// blame). Kept in lockstep with the region cell's committed map.
    graph: crate::graph::DocGraph,
    /// The receipt-chain head (the executor advances it per agent; we mirror it
    /// so sequential edits chain).
    chain_head: Option<[u8; 32]>,
    /// The editor's nonce: the executor advances it on commit; the next turn
    /// must carry it.
    nonce: u64,
}

impl ExecutorDrivenDoc {
    /// Open a fresh executor-driven document.
    ///
    /// `editor_holds_region_cap` controls the per-region edit cap: when `true`
    /// the editor is granted a c-list capability to the region cell (so edits
    /// commit); when `false` the editor lacks it (so edits are REFUSED by the
    /// executor's cap gate — the unauthorized-region case).
    pub fn new(editor_seed: u8, region_seed: u8, editor_holds_region_cap: bool) -> Self {
        let mut ledger = Ledger::new();

        // The region cell (the document). Its `set_state` permission is `None`
        // (open): the cap gate — not a signature — is the per-region authority,
        // so a cross-cell editor with the cap commits and one without is
        // refused at the cap check (before any signature lattice).
        //
        // The cell is created already holding the EMPTY-DOCUMENT projection (the
        // ROOT sentinel leaf) in its committed `fields_map` — genesis state, NOT
        // an edit. This is the projection of `DocGraph::new()`, so the
        // commitment-matches-projection invariant holds from genesis (and a
        // rolled-back refused edit lands back on this consistent genesis).
        let mut region_cell = open_region_cell(region_seed);
        seed_empty_document(&mut region_cell);
        let region = region_cell.id();

        // The editor cell (the author). Open permissions so the turn-level auth
        // passes; the cap to `region` (or its absence) is the real gate.
        let mut editor_cell = open_editor_cell(editor_seed, 1_000_000);
        if editor_holds_region_cap {
            // The per-region EDIT capability: a c-list entry granting access to
            // the region cell. `has_access_including_delegation_at` reads this
            // in `check_cross_cell_permission`.
            editor_cell.capabilities.grant(region, AuthRequired::None);
        }
        let editor = editor_cell.id();

        ledger.insert_cell(editor_cell).expect("editor insert");
        ledger.insert_cell(region_cell).expect("region insert");

        ExecutorDrivenDoc {
            ledger,
            executor: TurnExecutor::new(ComputronCosts::zero()),
            region,
            editor,
            graph: crate::graph::DocGraph::new(),
            chain_head: None,
            nonce: 0,
        }
    }

    /// The region (document) cell id.
    pub fn region_id(&self) -> CellId {
        self.region
    }

    /// The editor (author) cell id.
    pub fn editor_id(&self) -> CellId {
        self.editor
    }

    /// The witness graph the patch algebra reads.
    pub fn graph(&self) -> &crate::graph::DocGraph {
        &self.graph
    }

    /// The region cell (read-only) — the real substrate object.
    pub fn region_cell(&self) -> &Cell {
        self.ledger.get(&self.region).expect("region present")
    }

    /// The document's commitment: the region cell's real canonical state
    /// commitment (which absorbs `fields_root`, the digest of the document
    /// projection the executor writes).
    pub fn state_commitment(&self) -> [u8; 32] {
        compute_canonical_state_commitment(self.region_cell())
    }

    /// **AN EDIT IS A TURN, DRIVEN THROUGH THE REAL EXECUTOR.**
    ///
    /// Build the patch into a genuine [`dregg_turn::Turn`] (the `SetField`
    /// effects targeting the region cell) and run it through
    /// [`TurnExecutor::execute`]. On success the executor's committed receipt
    /// (finalized, journaled) is returned and the witness graph is advanced; on
    /// refusal the [`TurnError`] is returned and the document is left untouched
    /// (the executor rolled the ledger back; we roll the witness graph back).
    ///
    /// This is the seam where the per-region edit cap is ENFORCED: an editor
    /// without the region cap is refused with [`TurnError::CapabilityNotHeld`].
    pub fn edit(&mut self, patch: Patch) -> Result<TurnReceipt, TurnError> {
        // Snapshot the witness graph so a refusal leaves the document untouched
        // (the executor rolls the ledger back; the witness graph must match).
        let graph_snapshot = self.graph.clone();

        // 1. Apply the patch to the witness graph and compute the committed-map
        //    delta the executor will write (the genuine SetField effects).
        patch.apply(&mut self.graph);
        let effects = self.project_delta_effects();

        if effects.is_empty() {
            // A no-op edit (already at this projection): nothing to drive.
            // Roll the witness graph back to keep it byte-identical to before
            // (apply may have inserted then-superseded structure that projects
            // to the same leaves; the conservative choice is no state change).
            self.graph = graph_snapshot;
            return Err(TurnError::EmptyForest);
        }

        // 2. Build the genuine Turn: agent = editor, one action targeting the
        //    region cell with the SetField effects. `Unchecked` authorization;
        //    the region's open `set_state` passes the turn-level auth, and the
        //    per-region CAP gate (cross-cell `check_cross_cell_permission`) is
        //    the real enforcement at effect-application.
        let mut action =
            ActionBuilder::new_unchecked_for_tests(self.region, "doc_edit", self.editor);
        for e in &effects {
            action = action.effect(e.clone());
        }
        let action = action.build();

        let mut builder = TurnBuilder::new(self.editor, self.nonce);
        builder.add_action(action);
        let mut turn = builder.fee(0).build();
        turn.previous_receipt_hash = self.chain_head;

        // 3. Drive through THE REAL EXECUTOR — the sole entry point for ledger
        //    state mutations (cap gate, journal, nonce/receipt-chain advance).
        match self.executor.execute(&turn, &mut self.ledger) {
            TurnResult::Committed { receipt, .. } => {
                // The executor advanced the editor's nonce + receipt-chain head;
                // mirror them for the next edit.
                self.nonce = self
                    .ledger
                    .get(&self.editor)
                    .map(|c| c.state.nonce())
                    .unwrap_or(self.nonce + 1);
                self.chain_head = Some(receipt.receipt_hash());
                Ok(receipt)
            }
            TurnResult::Rejected { reason, .. } => {
                // In-band refusal (the anti-ghost tooth): the executor rolled
                // the ledger back. Roll the witness graph back to match — the
                // document is exactly as it was before the refused edit.
                self.graph = graph_snapshot;
                Err(reason)
            }
            TurnResult::Expired | TurnResult::Pending => {
                self.graph = graph_snapshot;
                Err(TurnError::EmptyForest)
            }
        }
    }

    /// The receipt-chain head (the genuine `receipt_hash` of the last committed
    /// edit), for chaining / verification.
    pub fn chain_head(&self) -> Option<[u8; 32]> {
        self.chain_head
    }

    /// The invariant: the region cell's committed `fields_map` equals the
    /// canonical projection of the witness graph (lifted into field keys). If
    /// this holds, the document the algebra sees and the commitment the light
    /// client trusts are the same object — the seam is closed *through the
    /// executor*.
    pub fn commitment_matches_projection(&self) -> bool {
        let desired = project_graph(&self.graph);
        let cell = self.region_cell();
        // Every desired leaf is present at its field key.
        for (&(coll, key), &value) in &desired {
            if cell.state.get_field_ext(field_key(coll, key)) != Some(value) {
                return false;
            }
        }
        // No stale document field keys linger (keys at/above STATE_SLOTS that
        // are no longer projected).
        for (&k, _) in cell.state.fields_map.iter() {
            if k >= STATE_SLOTS as u64 {
                // Recover (coll, key) from the flat key; if absent from desired,
                // the cell holds a stale document leaf.
                let flat = k - STATE_SLOTS as u64;
                let coll = (flat >> 32) as u32;
                let key = (flat & 0xFFFF_FFFF) as u32;
                if !desired.contains_key(&(coll, key)) {
                    return false;
                }
            }
        }
        true
    }

    /// Compute the genuine `SetField` effects for the difference between the
    /// witness graph's projection and the region cell's current committed map.
    /// These are the kernel writes the edit performs; the executor applies the
    /// same `set_field_ext` arm they desugar to.
    fn project_delta_effects(&self) -> Vec<Effect> {
        let desired = project_graph(&self.graph);
        let cell = self.region_cell();
        let mut effects = Vec::new();

        // Writes / overwrites.
        for (&(coll, key), &value) in &desired {
            let fk = field_key(coll, key);
            if cell.state.get_field_ext(fk) != Some(value) {
                effects.push(Effect::SetField {
                    cell: self.region,
                    index: fk as usize,
                    value,
                });
            }
        }

        // Removals: a document leaf the cell holds but the document no longer
        // projects. A `SetField` to the zero felt vacates the slot (the
        // executor has no Remove arm for committed-map keys; zeroing is the
        // canonical "empty" leaf — distinct from any real document leaf, which
        // binds provenance and is overwhelmingly non-zero).
        for (&k, _) in cell.state.fields_map.iter() {
            if k >= STATE_SLOTS as u64 {
                let flat = k - STATE_SLOTS as u64;
                let coll = (flat >> 32) as u32;
                let key = (flat & 0xFFFF_FFFF) as u32;
                if !desired.contains_key(&(coll, key)) {
                    effects.push(Effect::SetField {
                        cell: self.region,
                        index: k as usize,
                        value: [0u8; 32],
                    });
                }
            }
        }

        effects
    }
}

/// A region (document) cell with OPEN `set_state`: the per-region edit authority
/// is the c-list cap, not a signature, so the cross-cell cap gate is the real
/// gate.
fn open_region_cell(seed: u8) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[1] = 0xD0; // domain-tag the region pk so it cannot collide with an editor pk
    let mut cell = Cell::with_balance(pk, [0u8; 32], 0);
    cell.permissions = open_permissions();
    cell
}

/// An editor (author) cell with open permissions; the cap to the region (or its
/// absence) is the gate.
fn open_editor_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[1] = 0xED; // domain-tag the editor pk
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// Seed a region cell with the empty-document projection (the `DocGraph::new()`
/// ROOT-sentinel leaf) in its committed `fields_map` — genesis state. Writes the
/// same flat-key leaves [`ExecutorDrivenDoc::edit`] drives through the executor,
/// so the commitment-matches-projection invariant holds from genesis.
fn seed_empty_document(cell: &mut Cell) {
    let empty = project_graph(&crate::graph::DocGraph::new());
    for ((coll, key), value) in empty {
        cell.state.set_field_ext(field_key(coll, key), value);
    }
}

/// Open permissions: no auth required for anything (the cap gate carries the
/// authority).
fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::patch::Op;
    use crate::{AtomId, content};
    use dregg_turn::Finality;

    fn add(seed: u64, content: &str, after: AtomId) -> Op {
        Patch::add(seed, content, after).1
    }

    #[test]
    fn authorized_edit_commits_through_the_executor_with_a_final_receipt() {
        // The editor HOLDS the region cap → the edit drives through the real
        // executor and commits with a FINALIZED (not Tentative) receipt.
        let mut doc = ExecutorDrivenDoc::new(1, 2, /* holds_cap */ true);

        let pre = doc.state_commitment();
        let receipt = doc
            .edit(Patch::by(
                crate::Author(1),
                [add(1, "Hello, ", AtomId::ROOT)],
            ))
            .expect("authorized edit commits");

        // THE FINALITY UPGRADE: the executor's single-node commit yields a REAL
        // finalized receipt — not the direct-assembly path's `Tentative`.
        assert_eq!(
            receipt.finality,
            Finality::Final,
            "driving through the executor finalizes the receipt"
        );

        // The receipt is REAL: the agent is the editor, the pre/post-state
        // hashes are the genuine ledger roots, and the document commitment moved
        // (the executor wrote the projection into `fields_root`).
        assert_eq!(receipt.agent, doc.editor_id());
        assert_ne!(receipt.pre_state_hash, receipt.post_state_hash);
        assert_ne!(doc.state_commitment(), pre, "the edit moved the commitment");
        assert!(receipt.action_count >= 1);

        // The document the algebra sees and the commitment the executor wrote
        // are the same object.
        assert!(doc.commitment_matches_projection());
        assert_eq!(content(doc.graph()).to_marked_string(), "Hello, ");
    }

    #[test]
    fn unauthorized_region_edit_is_refused_by_the_executor_in_band() {
        // The editor LACKS the region cap → the executor's cross-cell cap gate
        // (`check_cross_cell_permission`) REFUSES the edit IN-BAND with
        // CapabilityNotHeld. The anti-ghost tooth: a refused edit is a Result
        // error, NOT a panic, and the document is left untouched.
        let mut doc = ExecutorDrivenDoc::new(1, 2, /* holds_cap */ false);
        let pre = doc.state_commitment();

        let err = doc
            .edit(Patch::by(
                crate::Author(1),
                [add(1, "Hello, ", AtomId::ROOT)],
            ))
            .expect_err("an editor without the region cap is refused");

        match err {
            TurnError::CapabilityNotHeld { actor, target } => {
                assert_eq!(actor, doc.editor_id(), "the editor is the refused actor");
                assert_eq!(target, doc.region_id(), "the region is the gated target");
            }
            other => panic!("expected CapabilityNotHeld, got {other:?}"),
        }

        // The document is UNTOUCHED: the executor rolled the ledger back and the
        // witness graph was rolled back to match — the commitment did not move.
        assert_eq!(
            doc.state_commitment(),
            pre,
            "a refused edit leaves the document commitment untouched"
        );
        assert!(doc.commitment_matches_projection());
        assert_eq!(
            content(doc.graph()).to_marked_string(),
            "",
            "the refused edit's content did not land"
        );
    }

    #[test]
    fn sequential_authorized_edits_chain_through_the_executor() {
        // A second authorized edit chains off the first (the executor's genuine
        // per-agent receipt chain + nonce advance).
        let mut doc = ExecutorDrivenDoc::new(3, 4, true);

        let hello = Patch::add(1, "Hello, ", AtomId::ROOT);
        let r1 = doc
            .edit(Patch::by(crate::Author(1), [hello.1]))
            .expect("first edit commits");
        let r2 = doc
            .edit(Patch::by(crate::Author(1), [add(2, "world.", hello.0)]))
            .expect("second edit commits");

        // The real receipt chain: the second edit links to the first.
        assert_eq!(
            r2.previous_receipt_hash,
            Some(r1.receipt_hash()),
            "the executor chained the second receipt off the first"
        );
        assert_eq!(r2.finality, Finality::Final);
        assert!(doc.commitment_matches_projection());
        assert_eq!(content(doc.graph()).to_marked_string(), "Hello, world.");
    }

    #[test]
    fn the_committed_map_carries_the_document_projection() {
        // The executor wrote the document projection into the region cell's
        // committed `fields_map` (keys lifted past STATE_SLOTS), and the field
        // key is bijective in `(collection, key)`.
        assert_eq!(field_key(0, 0), STATE_SLOTS as u64);
        assert!(field_key(2, 7) >= STATE_SLOTS as u64);
        assert_ne!(field_key(0, 1), field_key(1, 0));

        let mut doc = ExecutorDrivenDoc::new(5, 6, true);
        doc.edit(Patch::by(crate::Author(1), [add(1, "x", AtomId::ROOT)]))
            .expect("edit commits");

        // At least one document leaf lives in the committed map above the
        // register file.
        let cell = doc.region_cell();
        assert!(
            cell.state
                .fields_map
                .keys()
                .any(|&k| k >= STATE_SLOTS as u64),
            "a document leaf landed in the committed fields_map the executor wrote"
        );
    }
}
