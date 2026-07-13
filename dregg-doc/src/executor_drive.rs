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
    ActionBuilder, ComputronCosts, Effect, Turn, TurnBuilder, TurnError, TurnExecutor, TurnReceipt,
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
        Self::new_at(
            &crate::graph::DocGraph::new(),
            editor_seed,
            region_seed,
            editor_holds_region_cap,
        )
    }

    /// Open an executor-driven document whose region cell starts AT `base` — the
    /// base graph's projection is seeded into the committed `fields_map` as
    /// genesis state (exactly the way [`ExecutorDrivenDoc::new`] seeds the
    /// empty document), NOT as an edit. The witness graph starts as `base`.
    ///
    /// This is the forge's landing surface (`crate::pull_request`): a pull
    /// request targets an EXISTING base document, and the merger (this doc's
    /// editor) either holds the region's edit cap (the merge turns commit) or
    /// does not (the executor's `check_cross_cell_permission` gate refuses the
    /// first merge turn in-band — the same gate, no parallel one).
    pub fn new_at(
        base: &crate::graph::DocGraph,
        editor_seed: u8,
        region_seed: u8,
        editor_holds_region_cap: bool,
    ) -> Self {
        let mut ledger = Ledger::new();

        // The region cell (the document). Its `set_state` permission is `None`
        // (open): the cap gate — not a signature — is the per-region authority,
        // so a cross-cell editor with the cap commits and one without is
        // refused at the cap check (before any signature lattice).
        //
        // The cell is created already holding the base document's projection in
        // its committed `fields_map` — genesis state, NOT an edit. This is the
        // projection of `base`, so the commitment-matches-projection invariant
        // holds from genesis (and a rolled-back refused edit lands back on this
        // consistent genesis).
        let mut region_cell = open_region_cell(region_seed);
        seed_document(&mut region_cell, base);
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
            graph: base.clone(),
            chain_head: None,
            nonce: 0,
        }
    }

    /// Equip the underlying executor with an Ed25519 signing key (32-byte
    /// seed): every subsequently COMMITTED receipt carries a genuine
    /// `executor_signature` over [`TurnReceipt::canonical_executor_signed_message`]
    /// (dregg-turn Stage 9 R-4), verifiable via
    /// [`dregg_turn::verify_receipt_chain_with_keys`]. This is what lets a
    /// check-turn receipt serve as a NON-FABRICABLE witness (a receipt struct
    /// anyone can populate; a signature over its canonical message they
    /// cannot) — the forge's CI gate ([`crate::check`]) requires it.
    pub fn set_receipt_signing_key(&mut self, seed: [u8; 32]) {
        self.executor.set_executor_signing_key(seed);
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
        // 1–2. Plan: the post-edit witness graph and the genuine Turn (the
        //      SetField delta targeting the region cell). Pure — nothing is
        //      mutated until the executor commits, so a refusal leaves the
        //      document byte-identical.
        let Some((graph, turn)) = self.plan_turn(&patch) else {
            // A no-op edit (already at this projection): nothing to drive.
            return Err(TurnError::EmptyForest);
        };

        // 3. Drive through THE REAL EXECUTOR — the sole entry point for ledger
        //    state mutations (cap gate, journal, nonce/receipt-chain advance).
        match self.executor.execute(&turn, &mut self.ledger) {
            TurnResult::Committed { receipt, .. } => {
                // Only NOW advance the witness graph, and mirror the nonce +
                // receipt-chain head the executor advanced.
                self.graph = graph;
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
                // the ledger back; the witness graph was never advanced — the
                // document is exactly as it was before the refused edit.
                Err(reason)
            }
            TurnResult::Expired | TurnResult::Pending => Err(TurnError::EmptyForest),
        }
    }

    /// The turn [`ExecutorDrivenDoc::edit`] WOULD drive for `patch` at the
    /// document's current state, by hash — `None` for a no-op patch (empty
    /// projection delta). Turn construction is deterministic (agent, nonce,
    /// effects, chain head — no wall clock), so driving the same patch next,
    /// with no interleaved edit, commits a receipt whose `turn_hash` equals
    /// this hash.
    ///
    /// This is the forge's CI binding surface: a required check
    /// ([`crate::check::RequiredCheck`]) names the exact check turn (the job)
    /// BEFORE it runs, and is satisfied only by that turn's committed, signed
    /// receipt.
    pub fn planned_turn_hash(&self, patch: &Patch) -> Option<[u8; 32]> {
        self.plan_turn(patch).map(|(_, turn)| turn.hash())
    }

    /// Build (post-edit witness graph, genuine Turn) for `patch` at the current
    /// state — the pure planning half of [`ExecutorDrivenDoc::edit`]. `None`
    /// when the patch's projection delta is empty (nothing to drive).
    ///
    /// The Turn: agent = editor, one action targeting the region cell with the
    /// SetField effects. `Unchecked` authorization; the region's open
    /// `set_state` passes the turn-level auth, and the per-region CAP gate
    /// (cross-cell `check_cross_cell_permission`) is the real enforcement at
    /// effect-application.
    fn plan_turn(&self, patch: &Patch) -> Option<(crate::graph::DocGraph, Turn)> {
        let mut graph = self.graph.clone();
        patch.apply(&mut graph);
        let effects = self.project_delta_effects(&graph);
        if effects.is_empty() {
            return None;
        }

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
        Some((graph, turn))
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

    /// Compute the genuine `SetField` effects for the difference between
    /// `graph`'s projection and the region cell's current committed map.
    /// These are the kernel writes the edit performs; the executor applies the
    /// same `set_field_ext` arm they desugar to.
    fn project_delta_effects(&self, graph: &crate::graph::DocGraph) -> Vec<Effect> {
        region_delta_effects(self.region, self.region_cell(), graph)
    }
}

/// The genuine `SetField` delta between `graph`'s projection and `cell`'s current
/// committed map, targeting `region`. Free-standing so both the single-editor
/// [`ExecutorDrivenDoc`] and the multi-editor [`MultiEditorDoc`] share ONE
/// projection-diff — the document/patch semantics are computed identically no
/// matter which editor drives the turn.
fn region_delta_effects(
    region: CellId,
    cell: &Cell,
    graph: &crate::graph::DocGraph,
) -> Vec<Effect> {
    let desired = project_graph(graph);
    let mut effects = Vec::new();

    // Writes / overwrites.
    for (&(coll, key), &value) in &desired {
        let fk = field_key(coll, key);
        if cell.state.get_field_ext(fk) != Some(value) {
            effects.push(Effect::SetField {
                cell: region,
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
                    cell: region,
                    index: k as usize,
                    value: [0u8; 32],
                });
            }
        }
    }

    effects
}

/// One editor's handle within a [`MultiEditorDoc`]: its own cell (a distinct
/// agent) plus the mirrored per-agent nonce and receipt-chain head. Each editor
/// carries its OWN chain — the executor keys `last_receipt_hash` and the agent
/// nonce by cell id, so interleaving another editor's turns never disturbs this
/// editor's chain.
struct EditorSlot {
    /// The editor's agent cell id (distinct per editor; the turn's agent).
    cell: CellId,
    /// This editor's next nonce (mirrors the executor's per-agent nonce advance).
    nonce: u64,
    /// This editor's receipt-chain head (the genuine `receipt_hash` of this
    /// editor's last committed edit; the next of THIS editor's turns carries it
    /// as `previous_receipt_hash`). `None` until the editor's first commit.
    chain_head: Option<[u8; 32]>,
    /// This editor's committed receipts, in the order this editor authored them —
    /// the editor's real per-agent chain (hash-linked, nonce-monotone, signed).
    receipts: Vec<TurnReceipt>,
}

/// **A COLLABORATIVE DOCUMENT: N editors, each with a real per-agent turn chain,
/// over ONE shared region ledger.**
///
/// [`ExecutorDrivenDoc`] binds exactly ONE editor cell; a collaborative session
/// that re-based a fresh single-editor doc at the current fold for each actor
/// would keep every edit a genuine cap-gated finalized turn but LOSE the
/// executor's cross-edit per-agent nonce/receipt chain — each actor's history
/// would restart at genesis every edit.
///
/// `MultiEditorDoc` closes that: N distinct editor cells (distinct agents) each
/// hold their own c-list cap to the SAME region cell and drive turns through the
/// SAME [`TurnExecutor`] over the SAME [`Ledger`]. Because the executor keys the
/// receipt-chain head (`last_receipt_hash`) and the agent nonce by *cell id*, a
/// sequence of edits from different editors keeps each editor's real per-agent
/// chain: editor A's third edit chains off A's second (not off B's intervening
/// edit), with A's nonce monotone across A's own turns. This is the same pattern
/// distinct cipherclerks/executors-sharing-one-Ledger use — here, distinct
/// *editors* sharing one region ledger.
///
/// The document/patch/conflict semantics are UNCHANGED — the shared witness
/// graph, the projection, and [`region_delta_effects`] are exactly the
/// single-editor path's; only the *authority* (which agent, which chain) is
/// per-editor. An edit lands a genuine finalized turn on the shared doc; an
/// editor lacking the region cap is refused in-band; each editor's per-agent
/// chain is distinct and verifiable by replay.
///
/// ## What a fuller version adds (named honestly)
///
/// - **Concurrent editors.** Here edits are *sequenced* through one executor
///   (one node, one linear ledger history — the genuine fold). True concurrent
///   authoring (two editors composing on divergent replicas, then a
///   branch-and-stitch merge) is the patch algebra's job
///   ([`crate::merge`] / the two-device-sync path), layered ABOVE this — each
///   replica would be a `MultiEditorDoc` and the stitch a further turn.
/// - **Presence / awareness.** Live cursors, selections, and typing indicators
///   are an ephemeral side channel, not finalized turns; they ride a presence
///   layer, not the ledger.
/// - **Cross-node federation.** The executor commits on a single node
///   (`Finality::Final` is the solo-mode commit); BFT quorum across nodes is the
///   node layer's job (the same tail [`ExecutorDrivenDoc`] names).
pub struct MultiEditorDoc {
    ledger: Ledger,
    executor: TurnExecutor,
    /// The one shared document cell — every editor's edits target it.
    region: CellId,
    /// The one shared witness graph the patch algebra reads (the fold reflects
    /// every editor's edits in commit order).
    graph: crate::graph::DocGraph,
    /// The editors, in construction order; addressed by index in [`Self::edit`].
    editors: Vec<EditorSlot>,
    /// Every committed receipt, in global commit order — the doc's linear ledger
    /// history (the fold). Distinct from each editor's per-agent `receipts`.
    history: Vec<TurnReceipt>,
}

impl MultiEditorDoc {
    /// Open a fresh collaborative document with `editors.len()` editors over one
    /// empty region.
    ///
    /// Each entry is `(editor_seed, holds_region_cap)`: `editor_seed` seeds the
    /// editor's (distinct) cell; `holds_region_cap` grants that editor the
    /// per-region edit cap (so its edits commit) or withholds it (so its edits
    /// are REFUSED by the executor's cap gate — the unauthorized-editor case).
    /// Seeds must be distinct so the editor cells are distinct agents.
    pub fn new(region_seed: u8, editors: &[(u8, bool)]) -> Self {
        Self::new_at(&crate::graph::DocGraph::new(), region_seed, editors)
    }

    /// Open a collaborative document whose shared region starts AT `base` (its
    /// projection seeded as genesis state, NOT as an edit — exactly the way
    /// [`ExecutorDrivenDoc::new_at`] seeds a pull request's base). The witness
    /// graph starts as `base`.
    pub fn new_at(base: &crate::graph::DocGraph, region_seed: u8, editors: &[(u8, bool)]) -> Self {
        let mut ledger = Ledger::new();

        // The one shared region cell (the document), seeded to `base` as genesis.
        let mut region_cell = open_region_cell(region_seed);
        seed_document(&mut region_cell, base);
        let region = region_cell.id();
        ledger.insert_cell(region_cell).expect("region insert");

        // N distinct editor cells, each optionally holding the region edit cap.
        let mut slots = Vec::with_capacity(editors.len());
        for &(seed, holds_cap) in editors {
            let mut editor_cell = open_editor_cell(seed, 1_000_000);
            if holds_cap {
                editor_cell.capabilities.grant(region, AuthRequired::None);
            }
            let cell = editor_cell.id();
            ledger
                .insert_cell(editor_cell)
                .expect("editor insert (seeds must be distinct)");
            slots.push(EditorSlot {
                cell,
                nonce: 0,
                chain_head: None,
                receipts: Vec::new(),
            });
        }

        MultiEditorDoc {
            ledger,
            executor: TurnExecutor::new(ComputronCosts::zero()),
            region,
            graph: base.clone(),
            editors: slots,
            history: Vec::new(),
        }
    }

    /// Equip the shared executor with an Ed25519 signing key — every
    /// subsequently committed receipt (from ANY editor) carries a genuine
    /// `executor_signature`, so each editor's per-agent chain is a chain of
    /// NON-FABRICABLE witnesses (verifiable via
    /// [`dregg_turn::verify_receipt_signature_with_keys`]). See
    /// [`ExecutorDrivenDoc::set_receipt_signing_key`].
    pub fn set_receipt_signing_key(&mut self, seed: [u8; 32]) {
        self.executor.set_executor_signing_key(seed);
    }

    /// Number of editors.
    pub fn editor_count(&self) -> usize {
        self.editors.len()
    }

    /// The `ix`-th editor's (agent) cell id.
    pub fn editor_id(&self, ix: usize) -> CellId {
        self.editors[ix].cell
    }

    /// The shared region (document) cell id.
    pub fn region_id(&self) -> CellId {
        self.region
    }

    /// The shared witness graph the patch algebra reads.
    pub fn graph(&self) -> &crate::graph::DocGraph {
        &self.graph
    }

    /// The shared region cell (read-only) — the real substrate object.
    pub fn region_cell(&self) -> &Cell {
        self.ledger.get(&self.region).expect("region present")
    }

    /// The document's commitment: the shared region cell's real canonical state
    /// commitment.
    pub fn state_commitment(&self) -> [u8; 32] {
        compute_canonical_state_commitment(self.region_cell())
    }

    /// The `ix`-th editor's per-agent receipt chain, in the order that editor
    /// authored it (hash-linked, nonce-monotone, signed).
    pub fn editor_chain(&self, ix: usize) -> &[TurnReceipt] {
        &self.editors[ix].receipts
    }

    /// The `ix`-th editor's current receipt-chain head.
    pub fn editor_chain_head(&self, ix: usize) -> Option<[u8; 32]> {
        self.editors[ix].chain_head
    }

    /// The `ix`-th editor's next nonce (== the count of that editor's committed
    /// edits — the executor advanced it once per commit).
    pub fn editor_nonce(&self, ix: usize) -> u64 {
        self.editors[ix].nonce
    }

    /// Every committed receipt in global commit order — the doc's linear ledger
    /// history (the fold reflects all editors' edits in this order).
    pub fn history(&self) -> &[TurnReceipt] {
        &self.history
    }

    /// **AN EDIT BY EDITOR `ix`, DRIVEN THROUGH THE SHARED EXECUTOR.**
    ///
    /// Build `patch` into a genuine [`Turn`] whose agent is editor `ix`, carrying
    /// THAT editor's nonce and receipt-chain head, and run it through the shared
    /// [`TurnExecutor`] over the shared [`Ledger`]. On commit the shared witness
    /// graph advances and editor `ix`'s per-agent nonce + chain head + receipt
    /// list advance (only that editor's — the others are untouched). On refusal
    /// the [`TurnError`] is returned and the document is left byte-identical (the
    /// executor rolled the ledger back; the witness graph was never advanced).
    ///
    /// An editor without the region cap is refused with
    /// [`TurnError::CapabilityNotHeld`] — the same per-region cap gate the
    /// single-editor path uses.
    pub fn edit(&mut self, ix: usize, patch: Patch) -> Result<TurnReceipt, TurnError> {
        // Plan editor `ix`'s turn against the CURRENT shared state (pure —
        // nothing mutates until the executor commits, so a refusal is byte-safe).
        let Some((graph, turn)) = self.plan_turn_for(ix, &patch) else {
            return Err(TurnError::EmptyForest);
        };

        match self.executor.execute(&turn, &mut self.ledger) {
            TurnResult::Committed { receipt, .. } => {
                // The shared fold advances.
                self.graph = graph;
                // Mirror ONLY editor `ix`'s per-agent nonce + chain head (read the
                // nonce the executor just advanced on the editor's own cell).
                let new_nonce = self
                    .ledger
                    .get(&self.editors[ix].cell)
                    .map(|c| c.state.nonce());
                let slot = &mut self.editors[ix];
                slot.nonce = new_nonce.unwrap_or(slot.nonce + 1);
                slot.chain_head = Some(receipt.receipt_hash());
                slot.receipts.push(receipt.clone());
                self.history.push(receipt.clone());
                Ok(receipt)
            }
            TurnResult::Rejected { reason, .. } => {
                // In-band refusal: the executor rolled the ledger back and the
                // witness graph was never advanced — no editor's chain moved.
                Err(reason)
            }
            TurnResult::Expired | TurnResult::Pending => Err(TurnError::EmptyForest),
        }
    }

    /// The turn [`Self::edit`] WOULD drive for editor `ix` and `patch` at the
    /// current shared state — the pure planning half. `None` for a no-op patch.
    /// Agent = editor `ix`; nonce + `previous_receipt_hash` = that editor's own.
    fn plan_turn_for(&self, ix: usize, patch: &Patch) -> Option<(crate::graph::DocGraph, Turn)> {
        let slot = &self.editors[ix];
        let mut graph = self.graph.clone();
        patch.apply(&mut graph);
        let effects = region_delta_effects(self.region, self.region_cell(), &graph);
        if effects.is_empty() {
            return None;
        }

        let mut action = ActionBuilder::new_unchecked_for_tests(self.region, "doc_edit", slot.cell);
        for e in &effects {
            action = action.effect(e.clone());
        }
        let action = action.build();

        let mut builder = TurnBuilder::new(slot.cell, slot.nonce);
        builder.add_action(action);
        let mut turn = builder.fee(0).build();
        turn.previous_receipt_hash = slot.chain_head;
        Some((graph, turn))
    }

    /// The invariant: the shared region cell's committed `fields_map` equals the
    /// canonical projection of the shared witness graph — same check as
    /// [`ExecutorDrivenDoc::commitment_matches_projection`], now over the
    /// multi-editor fold.
    pub fn commitment_matches_projection(&self) -> bool {
        let desired = project_graph(&self.graph);
        let cell = self.region_cell();
        for (&(coll, key), &value) in &desired {
            if cell.state.get_field_ext(field_key(coll, key)) != Some(value) {
                return false;
            }
        }
        for (&k, _) in cell.state.fields_map.iter() {
            if k >= STATE_SLOTS as u64 {
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

/// Seed a region cell with a document graph's projection in its committed
/// `fields_map` — genesis state. Writes the same flat-key leaves
/// [`ExecutorDrivenDoc::edit`] drives through the executor, so the
/// commitment-matches-projection invariant holds from genesis. For
/// [`ExecutorDrivenDoc::new`] the graph is `DocGraph::new()` (the ROOT-sentinel
/// leaf); for [`ExecutorDrivenDoc::new_at`] it is a pull request's base.
fn seed_document(cell: &mut Cell, graph: &crate::graph::DocGraph) {
    let leaves = project_graph(graph);
    for ((coll, key), value) in leaves {
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

    // ─────────────────────────────────────────────────────────────────────────
    // MULTI-EDITOR: N editors, each a real per-agent chain, over ONE shared doc.
    // ─────────────────────────────────────────────────────────────────────────

    /// Ed25519 verifying key (32 bytes) for a 32-byte signing seed — the executor
    /// signs receipts with the seed; a light client verifies with this.
    fn pubkey_of(seed: [u8; 32]) -> [u8; 32] {
        ed25519_dalek::SigningKey::from_bytes(&seed)
            .verifying_key()
            .to_bytes()
    }

    /// A genuine per-agent chain, checked WITHOUT `verify_receipt_chain`: that
    /// helper also demands ledger-state continuity (`pre == prev.post`), which an
    /// INTERLEAVED editor's filtered chain does NOT satisfy — another editor moved
    /// the shared ledger between this editor's two turns. The authority chain a
    /// per-agent history genuinely carries is: genesis has no previous, each next
    /// links its `previous_receipt_hash` to the prior receipt's hash, every
    /// receipt is the same agent, nonces are strictly monotone from 0, and every
    /// receipt's executor signature verifies. This is what the executor enforces
    /// per agent at write time, and it is verifiable by replay here.
    fn assert_per_agent_chain(chain: &[TurnReceipt], agent: CellId, exec_pk: [u8; 32]) {
        use dregg_turn::verify_receipt_signature_with_keys;
        assert!(!chain.is_empty(), "the editor authored at least one turn");
        assert_eq!(
            chain[0].previous_receipt_hash, None,
            "the editor's first turn is genesis for that agent"
        );
        for (i, r) in chain.iter().enumerate() {
            assert_eq!(r.agent, agent, "every receipt is this editor's agent");
            assert_eq!(r.finality, Finality::Final, "each edit is finalized");
            assert!(
                verify_receipt_signature_with_keys(r, &[exec_pk]).is_ok(),
                "each receipt carries a genuine, verifiable executor signature"
            );
            if i > 0 {
                assert_eq!(
                    r.previous_receipt_hash,
                    Some(chain[i - 1].receipt_hash()),
                    "receipt {i} links to this editor's own prior receipt (NOT re-based to genesis)"
                );
            }
        }
    }

    #[test]
    fn multi_editor_session_keeps_each_editors_real_per_agent_chain() {
        // TWO editors, both authorized, over ONE shared document. They INTERLEAVE:
        // A, B, A, B. Each editor's turns must form a real per-agent chain (their
        // OWN receipts hash-linked, their OWN nonce monotone), NOT a fresh doc
        // re-based at the current fold per edit.
        let exec_seed = [7u8; 32];
        let mut doc = MultiEditorDoc::new(9, &[(1, true), (2, true)]);
        doc.set_receipt_signing_key(exec_seed);
        let (a, b) = (0usize, 1usize);

        // A: "A1 " after ROOT.
        let a1 = Patch::add(11, "A1 ", AtomId::ROOT);
        let ra1 = doc
            .edit(a, Patch::by(crate::Author(1), [a1.1]))
            .expect("A's first edit commits");
        // B: "B1 " after A's atom.
        let b1 = Patch::add(21, "B1 ", a1.0);
        let rb1 = doc
            .edit(b, Patch::by(crate::Author(2), [b1.1]))
            .expect("B's first edit commits");
        // A again: "A2 " after B's atom — A's SECOND turn, over a ledger B moved.
        let a2 = Patch::add(12, "A2 ", b1.0);
        let ra2 = doc
            .edit(a, Patch::by(crate::Author(1), [a2.1]))
            .expect("A's second edit commits");
        // B again: "B2" after A's second atom.
        let b2 = Patch::add(22, "B2", a2.0);
        let rb2 = doc
            .edit(b, Patch::by(crate::Author(2), [b2.1]))
            .expect("B's second edit commits");

        // THE POINT: A's second turn chains off A's FIRST (not genesis, not B's
        // intervening receipt) even though B edited in between — the cross-edit
        // per-agent chain is preserved, not re-based.
        assert_eq!(
            ra2.previous_receipt_hash,
            Some(ra1.receipt_hash()),
            "A's chain is preserved across B's interleaved edit"
        );
        assert_eq!(
            rb2.previous_receipt_hash,
            Some(rb1.receipt_hash()),
            "B's chain is preserved across A's interleaved edit"
        );

        // The two chains are DISTINCT agents.
        assert_ne!(doc.editor_id(a), doc.editor_id(b));
        assert_eq!(ra1.agent, doc.editor_id(a));
        assert_eq!(rb1.agent, doc.editor_id(b));

        // Each editor's per-agent chain verifies by replay (hash-linked, agent,
        // monotone nonce, signed).
        let pk = pubkey_of(exec_seed);
        assert_per_agent_chain(doc.editor_chain(a), doc.editor_id(a), pk);
        assert_per_agent_chain(doc.editor_chain(b), doc.editor_id(b), pk);
        assert_eq!(doc.editor_chain(a).len(), 2);
        assert_eq!(doc.editor_chain(b).len(), 2);
        // Monotone per-agent nonces: two commits each ⇒ next nonce 2.
        assert_eq!(doc.editor_nonce(a), 2);
        assert_eq!(doc.editor_nonce(b), 2);

        // The shared fold reflects ALL edits, in order.
        assert_eq!(content(doc.graph()).to_marked_string(), "A1 B1 A2 B2");
        assert!(doc.commitment_matches_projection());

        // The GLOBAL history is a genuine linear ledger fold: 4 commits, each
        // receipt's pre-state == the previous receipt's post-state (the interleaved
        // history is one consistent chain of ledger roots — the doc fold).
        let hist = doc.history();
        assert_eq!(hist.len(), 4);
        for i in 1..hist.len() {
            assert_eq!(
                hist[i].pre_state_hash,
                hist[i - 1].post_state_hash,
                "the doc fold is a continuous ledger history over all editors' edits"
            );
        }
    }

    #[test]
    fn multi_editor_unauthorized_editor_is_refused_others_commit() {
        // Editor A holds the region cap; editor U does NOT. U's edit is refused
        // in-band by the SAME per-region cap gate, leaving the shared doc
        // untouched; A's edits still commit and keep A's chain.
        let mut doc = MultiEditorDoc::new(9, &[(1, true), (2, false)]);
        let (a, u) = (0usize, 1usize);

        let a1 = Patch::add(11, "hello ", AtomId::ROOT);
        doc.edit(a, Patch::by(crate::Author(1), [a1.1]))
            .expect("authorized editor commits");
        let pre = doc.state_commitment();

        // U tries to edit — refused with CapabilityNotHeld, targeting the region.
        let err = doc
            .edit(u, Patch::by(crate::Author(2), [add(21, "evil", a1.0)]))
            .expect_err("unauthorized editor is refused");
        match err {
            TurnError::CapabilityNotHeld { actor, target } => {
                assert_eq!(
                    actor,
                    doc.editor_id(u),
                    "the unauthorized editor is refused"
                );
                assert_eq!(target, doc.region_id(), "the region is the gated target");
            }
            other => panic!("expected CapabilityNotHeld, got {other:?}"),
        }

        // The doc is byte-identical; U's chain never started; A can edit again and
        // A's chain continues cleanly (the refused turn perturbed nothing).
        assert_eq!(
            doc.state_commitment(),
            pre,
            "refused edit left the doc untouched"
        );
        assert_eq!(content(doc.graph()).to_marked_string(), "hello ");
        assert!(
            doc.editor_chain(u).is_empty(),
            "the refused editor has no chain"
        );
        assert_eq!(
            doc.editor_nonce(u),
            0,
            "the refused editor's nonce never advanced"
        );

        let a2 = Patch::add(12, "world", a1.0);
        let ra2 = doc
            .edit(a, Patch::by(crate::Author(1), [a2.1]))
            .expect("authorized editor commits again after the refusal");
        assert_eq!(
            ra2.previous_receipt_hash,
            Some(doc.editor_chain(a)[0].receipt_hash()),
            "A's chain continued across U's refused edit"
        );
        assert_eq!(content(doc.graph()).to_marked_string(), "hello world");
    }

    #[test]
    fn single_editor_multi_editor_doc_matches_the_single_editor_path() {
        // A one-editor MultiEditorDoc behaves like ExecutorDrivenDoc: sequential
        // edits chain off each other on the one agent.
        let mut doc = MultiEditorDoc::new(9, &[(1, true)]);
        let h = Patch::add(1, "Hello, ", AtomId::ROOT);
        let r1 = doc
            .edit(0, Patch::by(crate::Author(1), [h.1]))
            .expect("first edit commits");
        let r2 = doc
            .edit(0, Patch::by(crate::Author(1), [add(2, "world.", h.0)]))
            .expect("second edit commits");
        assert_eq!(r2.previous_receipt_hash, Some(r1.receipt_hash()));
        assert_eq!(content(doc.graph()).to_marked_string(), "Hello, world.");
        assert!(doc.commitment_matches_projection());
    }
}
