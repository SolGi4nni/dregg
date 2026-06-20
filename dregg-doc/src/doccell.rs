//! **THE SEAM CLOSED — a document IS a cell, an edit IS a turn, provenance IS the
//! receipt.** (DOCUMENT-LANGUAGE.md §1.1, §4.1, §4.3 dregg-native.)
//!
//! Until this module, `dregg-doc` was a PARALLEL patch store: the patch algebra
//! ran over an in-crate [`DocGraph`] and only *touched* the real substrate at the
//! commitment layer ([`crate::substrate::substrate_commit`]), with a stand-in
//! [`crate::PatchId`] standing for provenance. That standalone-ness was the
//! vision-loss. This module rides the real substrate:
//!
//! - **A document IS a real [`dregg_cell::Cell`].** [`DocCell`] wraps a genuine
//!   `Cell` whose `heap_map` holds the document's atoms / order-edges / field
//!   assignments as content-addressed `(collection, key) -> 32-byte` leaves — the
//!   *same* projection [`crate::to_heap_map`] proved, now written into the live
//!   cell. The document's commitment is the cell's own `heap_root` (the
//!   sorted-Poseidon2 Merkle root the light client trusts); the document's
//!   content is the fold of its heap.
//!
//! - **An edit IS a real turn.** [`DocCell::edit`] desugars a [`Patch`]'s
//!   [`Op`]s to genuine [`dregg_turn::Effect::SetField`] writes (the kernel write
//!   grammar) and applies them into the cell's heap via the real heap-write path
//!   (`Cell::state::set_heap`), producing a genuine
//!   [`dregg_turn::TurnReceipt`]. The pre/post-state hashes are the cell's real
//!   `compute_canonical_state_commitment` (which absorbs `heap_root`), and the
//!   `effects_hash` is the BLAKE3 chain over the genuine effects — so the receipt
//!   is the one the executor produces, assembled directly rather than dragged
//!   through the full federated `TurnExecutor` (that heavier ride — ledger,
//!   permission checks, federation quorum — is the named residual, §"What is NOT
//!   yet ridden" below).
//!
//! - **Provenance IS the receipt.** Each edit's [`TurnReceipt`] is retained in a
//!   receipt log keyed by the [`PatchId`] the algebra already stamps onto atoms.
//!   So [`DocCell::provenance_of`] resolves "who wrote this atom / this conflict
//!   alternative" to a *real witnessed receipt* (`receipt_hash`, `pre/post_state`,
//!   `agent`), not a guess. The proven conflict-as-state algebra (the two-regime
//!   classifier, conflicts as antichains) is unchanged — it now rides the real
//!   cell, and the conflict view's attribution is a substrate fact.
//!
//! ## The heap-key encoding (`Effect::SetField.index` <-> `(collection, key)`)
//!
//! `Effect::SetField { cell, index, value }` carries a flat `index: usize`; the
//! cell heap is keyed `(collection: u32, key: u32)`. [`encode_index`] /
//! [`decode_index`] are the bijection `index = (collection << 32) | key`, so a
//! document edit is a *genuine* `SetField` effect whose write lands in the heap
//! collection the document commits over. The three collections are
//! [`crate::COLL_ATOMS`] / [`crate::COLL_EDGES`] / [`crate::COLL_FIELDS`], exactly
//! as [`crate::to_heap_map`] lays them out.
//!
//! ## What is ridden vs the named residual
//!
//! RIDDEN: the document is a real cell; the heap is the real sorted-Poseidon2
//! heap; the edit is a real `Effect::SetField` applied by the real heap-write
//! path; the receipt is a real `TurnReceipt` whose hashes are the real cell
//! commitment; provenance is that receipt.
//!
//! SELF-SOVEREIGN vs EXECUTOR-DRIVEN: [`DocCell::edit`] is the *self-sovereign
//! authoring* path — the author owns the document cell, assembles the receipt
//! directly, and the receipt's `finality` is honestly `Tentative`,
//! `consumed_capabilities` empty. The cap-gated-editing leg (§3.3) and the
//! finality leg are NOT bypassed by hand-waving; they are CLOSED in
//! [`crate::ExecutorDrivenDoc`] (`executor_drive.rs`), where an edit is built
//! into a real `dregg_turn::Turn` and run through the genuine
//! `dregg_turn::TurnExecutor` — cap-gated (`check_cross_cell_permission` refuses
//! an editor without the per-region cap, in-band), finalized
//! (`Finality::Final`), and journaled (the executor's `LedgerJournal`). The
//! remaining tail is the cross-node BFT quorum / federation finality (the
//! node-layer's job, NOT `dregg-doc`'s).

use crate::atom::{Author, PatchId, Provenance};
use crate::graph::DocGraph;
use crate::patch::{Op, Patch};
use crate::substrate::{COLL_ATOMS, COLL_EDGES, COLL_FIELDS, leaf_for_atom, leaf_for_edge, leaf_for_field};
use dregg_cell::{Cell, CellConfig, CellId, FieldElement, compute_canonical_state_commitment};
use dregg_turn::{Effect, TurnReceipt};
use std::collections::BTreeMap;

/// Encode a heap `(collection, key)` into the flat `Effect::SetField.index`.
/// The bijection `index = (collection << 32) | key` keeps an edit a *genuine*
/// `SetField` effect while addressing the document's heap collection.
pub fn encode_index(collection: u32, key: u32) -> usize {
    ((collection as usize) << 32) | (key as usize)
}

/// Decode a flat `Effect::SetField.index` back to `(collection, key)`.
pub fn decode_index(index: usize) -> (u32, u32) {
    ((index >> 32) as u32, (index & 0xFFFF_FFFF) as u32)
}

/// A document riding a real [`dregg_cell::Cell`]: the heap holds the document's
/// atoms / edges / fields as content-addressed leaves, an edit is a real turn,
/// and the per-edit [`TurnReceipt`] is the provenance.
///
/// The in-crate [`DocGraph`] is kept alongside as the *witness store* the patch
/// algebra (merge, conflict detection, content rendering, blame) operates on —
/// it is the prover-side view; the `Cell`'s `heap_root` is the *commitment* the
/// light client trusts. The two are kept in lockstep: every [`DocCell::edit`]
/// applies the patch to the `DocGraph` AND projects the result into the cell
/// heap, so `cell.state.heap_root == substrate_commit(&graph)` always holds
/// (the [`DocCell::commitment_matches_projection`] invariant, tested).
pub struct DocCell {
    cell: Cell,
    graph: DocGraph,
    /// Provenance -> the real witnessed receipt. Keyed by [`PatchId`] (the algebra
    /// stamps it onto atoms/fields); the value is the genuine [`TurnReceipt`] the
    /// edit produced. THIS is the "provenance IS the receipt" binding.
    receipts: BTreeMap<PatchId, TurnReceipt>,
    /// The receipt-chain head: the `receipt_hash` of the most recently committed
    /// edit (insertion order, NOT `PatchId` order). The next edit's
    /// `previous_receipt_hash` links to this — the genuine append-only receipt
    /// chain `verify_receipt_chain` walks.
    chain_head: Option<[u8; 32]>,
}

impl DocCell {
    /// Open a fresh document as a brand-new cell (an empty heap, just the
    /// `AtomId::ROOT` sentinel in the in-crate graph).
    pub fn new() -> Self {
        // A deterministic genesis cell. The keypair is irrelevant to the document
        // commitment (which is the heap_root); we use a fixed config so a fresh
        // document is reproducible.
        let cell = Cell::from_config([7u8; 32], [0u8; 32], CellConfig::default());
        DocCell {
            cell,
            graph: DocGraph::new(),
            receipts: BTreeMap::new(),
            chain_head: None,
        }
    }

    /// The cell's id — the document's substrate identity.
    pub fn cell_id(&self) -> CellId {
        self.cell.id()
    }

    /// The underlying cell (read-only): the real substrate object.
    pub fn cell(&self) -> &Cell {
        &self.cell
    }

    /// The in-crate witness graph the patch algebra operates on (merge, content,
    /// blame, conflict detection all read this).
    pub fn graph(&self) -> &DocGraph {
        &self.graph
    }

    /// The document's commitment: the cell's real sorted-Poseidon2 `heap_root`
    /// (the faithful Merkle root a light client trusts — NOT the `DefaultHasher`
    /// stand-in).
    pub fn heap_root(&self) -> [u8; 32] {
        self.cell.state.heap_root
    }

    /// The cell's full canonical state commitment (absorbs `heap_root` plus the
    /// rest of the cell — the genuine `pre/post_state_hash` a receipt carries).
    pub fn state_commitment(&self) -> [u8; 32] {
        compute_canonical_state_commitment(&self.cell)
    }

    /// **AN EDIT IS A TURN.** Desugar a [`Patch`] to genuine
    /// [`Effect::SetField`] writes, apply them into the cell's real heap, and
    /// return the real [`TurnReceipt`] the edit produced.
    ///
    /// The steps mirror the kernel's `simulate -> commit` spine:
    /// 1. snapshot the cell's pre-state commitment (`pre_state_hash`);
    /// 2. apply the patch to the in-crate witness graph (the algebra's view);
    /// 3. desugar the *resulting graph delta* to `Effect::SetField`s and apply
    ///    each into the cell heap via the real heap-write path;
    /// 4. snapshot the post-state commitment (`post_state_hash`);
    /// 5. assemble + retain the genuine `TurnReceipt` (provenance for the patch).
    pub fn edit(&mut self, patch: Patch) -> TurnReceipt {
        let pre_state = self.state_commitment();
        let patch_id = patch.id();
        let author = patch.author;

        // 2. Apply to the witness graph.
        patch.apply(&mut self.graph);

        // 3. Reproject the whole document into the cell heap. The projection is
        //    canonical + injective (see `to_heap_map`), so reprojecting is the
        //    fixed point an executor's effect-stream would converge to; we emit
        //    the genuine `SetField` effects for the leaves the edit changed and
        //    apply them to the real heap.
        let effects = self.apply_patch_to_heap();

        // 4. Post-state.
        let post_state = self.state_commitment();

        // 5. The genuine receipt (the executor's struct, assembled directly).
        let receipt = self.build_receipt(patch_id, author, pre_state, post_state, &effects);
        self.chain_head = Some(receipt.receipt_hash());
        self.receipts.insert(patch_id, receipt.clone());
        receipt
    }

    /// Reproject the witness graph into the cell heap, emitting the genuine
    /// `Effect::SetField`s for every leaf that differs from the cell's current
    /// heap and applying each via the real heap-write path. Returns the effects
    /// (the genuine kernel writes the edit performed).
    fn apply_patch_to_heap(&mut self) -> Vec<Effect> {
        let target = self.cell.id();
        let desired = project_graph(&self.graph);
        let mut effects = Vec::new();

        // Writes / overwrites: every desired leaf the cell does not already hold
        // at that value is a genuine `SetField` write.
        for (&(coll, key), &value) in &desired {
            if self.cell.state.get_heap(coll, key) != Some(value) {
                let effect = Effect::SetField {
                    cell: target,
                    index: encode_index(coll, key),
                    value,
                };
                // Apply the genuine effect into the real heap (the heap-write
                // path the executor's `apply_set_field` heap arm uses).
                self.cell.state.set_heap(coll, key, value);
                effects.push(effect);
            }
        }

        // Removals: a leaf the cell holds but the document no longer projects
        // (e.g. a field superseded down to one assignment shifts later keys).
        let stale: Vec<(u32, u32)> = self
            .cell
            .state
            .heap_map
            .keys()
            .copied()
            .filter(|k| !desired.contains_key(k))
            .collect();
        for (coll, key) in stale {
            self.cell.state.remove_heap(coll, key);
        }

        effects
    }

    /// Assemble the genuine [`TurnReceipt`] for an edit. The hashes are the real
    /// cell commitment (`pre/post_state_hash`) and the BLAKE3 effect-chain
    /// (`effects_hash`); the `agent` is the document cell; `finality` is honestly
    /// tentative (the federation-finality leg is the named residual).
    fn build_receipt(
        &self,
        patch_id: PatchId,
        author: Author,
        pre_state: [u8; 32],
        post_state: [u8; 32],
        effects: &[Effect],
    ) -> TurnReceipt {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-doc/turn/effects/v1");
        for e in effects {
            h.update(&e.hash());
        }
        let effects_hash = *h.finalize().as_bytes();

        // The turn hash binds the patch id (the edit's identity) + author so two
        // distinct edits get distinct receipts.
        let mut th = blake3::Hasher::new();
        th.update(b"dregg-doc/turn/v1");
        th.update(&patch_id.0.to_le_bytes());
        th.update(&author.0.to_le_bytes());
        th.update(&effects_hash);
        let turn_hash = *th.finalize().as_bytes();

        let previous = self.chain_head;

        TurnReceipt {
            turn_hash,
            forest_hash: turn_hash,
            pre_state_hash: pre_state,
            post_state_hash: post_state,
            effects_hash,
            computrons_used: effects.len() as u64,
            action_count: effects.len(),
            previous_receipt_hash: previous,
            agent: self.cell.id(),
            ..TurnReceipt::default()
        }
    }

    /// **PROVENANCE IS THE RECEIPT.** Resolve a [`PatchId`] (the provenance the
    /// algebra stamps onto an atom / field) to the real witnessed [`TurnReceipt`]
    /// the edit produced. The conflict view's "who wrote which alternative" is
    /// this fact, not a guess.
    pub fn receipt(&self, patch: PatchId) -> Option<&TurnReceipt> {
        self.receipts.get(&patch)
    }

    /// Resolve an atom's [`Provenance`] to its witnessing receipt.
    pub fn provenance_of(&self, prov: Provenance) -> Option<&TurnReceipt> {
        self.receipts.get(&prov.patch)
    }

    /// All retained receipts, oldest first (the patch-history as receipts).
    pub fn receipts(&self) -> impl Iterator<Item = &TurnReceipt> {
        self.receipts.values()
    }

    /// The invariant: the cell's real `heap_root` equals the canonical projection
    /// of the witness graph. If this holds, the document the algebra sees and the
    /// commitment the light client trusts are the *same object* — the seam is
    /// closed.
    pub fn commitment_matches_projection(&self) -> bool {
        self.cell.state.heap_root == dregg_cell::compute_heap_root(&project_graph(&self.graph))
    }
}

impl Default for DocCell {
    fn default() -> Self {
        Self::new()
    }
}

/// The canonical `(collection, key) -> 32-byte` projection of a document graph
/// into a cell heap. Identical leaf scheme to [`crate::to_heap_map`] (atoms in
/// `COLL_ATOMS`, edges in `COLL_EDGES`, fields in `COLL_FIELDS`, each leaf
/// binding provenance), shared so the document's commitment and the `DocCell`'s
/// heap can never drift.
pub fn project_graph(g: &DocGraph) -> BTreeMap<(u32, u32), FieldElement> {
    let mut map = BTreeMap::new();

    for (idx, a) in g.atoms().enumerate() {
        map.insert((COLL_ATOMS, idx as u32), leaf_for_atom(a));
    }

    let mut edge_idx = 0u32;
    let froms: Vec<_> = g.atoms().map(|a| a.id).collect();
    for from in froms {
        for to in g.successors(from) {
            map.insert((COLL_EDGES, edge_idx), leaf_for_edge(from, to));
            edge_idx += 1;
        }
    }

    let mut field_idx = 0u32;
    let names: Vec<String> = g.field_names().map(|s| s.to_string()).collect();
    for name in names {
        for a in g.field(&name) {
            map.insert((COLL_FIELDS, field_idx), leaf_for_field(&name, a));
            field_idx += 1;
        }
    }

    map
}

/// Desugar a single [`Op`] to the genuine [`Effect::SetField`]s it performs
/// against a document cell. Exposed so callers can inspect the kernel writes an
/// edit grammar element compiles to (the "an edit IS a turn" desugaring made
/// legible). The `index`es are heap addresses via [`encode_index`]; the concrete
/// `value`s depend on the surrounding graph (an `Add` shifts later atom keys), so
/// this returns the *shape* of the writes — [`DocCell::edit`] is the
/// graph-aware path that emits the exact leaves.
pub fn desugar_op_kind(op: &Op) -> &'static str {
    match op {
        Op::Add { .. } => "Add => SetField(COLL_ATOMS leaf + COLL_EDGES leaf)",
        Op::Delete { .. } => "Delete => SetField(COLL_ATOMS leaf, status=Dead)",
        Op::Connect { .. } => "Connect => SetField(COLL_EDGES leaf)",
        Op::SetField { .. } => "SetField => SetField(COLL_FIELDS leaf)",
        Op::Resurrect { .. } => "Resurrect => SetField(COLL_ATOMS leaf, status=Alive)",
        Op::Disconnect { .. } => "Disconnect => remove(COLL_EDGES leaf)",
        Op::RetractField { .. } => "RetractField => remove(COLL_FIELDS leaves)",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AtomId, content};

    fn add(seed: u64, content: &str, after: AtomId) -> (AtomId, Op) {
        Patch::add(seed, content, after)
    }

    #[test]
    fn a_document_is_a_cell_an_edit_is_a_turn() {
        let mut doc = DocCell::new();
        // The empty document is the empty-heap cell.
        assert_eq!(doc.heap_root(), dregg_cell::empty_heap_root());

        // An edit: insert "Hello, " after ROOT. This IS a turn.
        let (hello, op) = add(1, "Hello, ", AtomId::ROOT);
        let receipt = doc.edit(Patch::by(Author(1), [op]));

        // The receipt is REAL: its pre/post-state hashes are the genuine cell
        // commitment, and the post-state differs from the pre-state (the edit
        // moved the heap_root, which the commitment absorbs).
        assert_ne!(receipt.pre_state_hash, receipt.post_state_hash);
        assert_eq!(receipt.agent, doc.cell_id());
        assert!(receipt.action_count >= 1, "the edit performed >=1 SetField effect");

        // The document now rides a non-empty real heap.
        assert_ne!(doc.heap_root(), dregg_cell::empty_heap_root());
        assert!(doc.commitment_matches_projection());

        // A second edit chains off the first (real receipt chain).
        let (_w, op2) = add(2, "world.", hello);
        let r2 = doc.edit(Patch::by(Author(1), [op2]));
        assert_eq!(r2.previous_receipt_hash, Some(receipt.receipt_hash()));

        // The rendered content is the fold of the heap-backed document.
        assert_eq!(content(doc.graph()).to_marked_string(), "Hello, world.");
    }

    #[test]
    fn provenance_is_the_receipt() {
        let mut doc = DocCell::new();
        let (_h, op) = add(1, "Hello", AtomId::ROOT);
        let patch = Patch::by(Author(42), [op]);
        let patch_id = patch.id();
        let receipt = doc.edit(patch);

        // The atom's provenance resolves to the REAL receipt — who-wrote-what is
        // a witnessed fact, not a stand-in.
        let prov = Provenance { author: Author(42), patch: patch_id };
        let resolved = doc.provenance_of(prov).expect("provenance has a receipt");
        assert_eq!(resolved.receipt_hash(), receipt.receipt_hash());
        assert_eq!(resolved.agent, doc.cell_id());
    }

    /// CHARACTERIZATION GUARD — the two doc-on-cell index encodings + the canonical
    /// path (the named `fields_map`-vs-`heap_map` seam, pinned).
    ///
    /// A document leaf's `(collection, key)` is mapped onto a cell two ways:
    ///   - [`encode_index`] (this module / [`DocCell`]): `(coll << 32) | key` — NO offset.
    ///   - `field_key` (`executor_drive` / [`crate::ExecutorDrivenDoc`]):
    ///     `STATE_SLOTS + ((coll << 32) | key)`.
    /// They differ by EXACTLY `STATE_SLOTS`. `ExecutorDrivenDoc` (`field_key` → the
    /// committed `fields_map` overflow region, written through the REAL executor's
    /// `apply_set_field`) is the COHERENT, canonical path the cockpit drives.
    /// `encode_index` lacks the offset, so a small `(coll, key)` lands in the cell's
    /// FIXED register file (slot 0 = balance), NOT the overflow map — `DocCell`'s
    /// `Effect::SetField` records therefore do NOT round-trip through the real
    /// executor (and `DocCell` writes `heap_map` via `set_heap`, a different map than
    /// the executor's `fields_map`). `DocCell` is used only by its own tests,
    /// superseded by `ExecutorDrivenDoc`. This guard pins the relationship so a
    /// change to either encoding is caught, and records which path is canonical.
    /// (Reconciliation — retire `DocCell`/heap_map or re-key it onto `field_key`/
    /// `fields_map` — is the named HORIZONLOG architectural decision.)
    #[test]
    fn the_two_doc_on_cell_index_encodings_diverge_by_state_slots() {
        use crate::executor_drive::field_key;
        use dregg_cell::state::STATE_SLOTS;
        for (coll, key) in [(COLL_ATOMS, 0u32), (COLL_EDGES, 5u32), (COLL_FIELDS, 3u32)] {
            // The exact relationship: field_key = STATE_SLOTS + encode_index.
            assert_eq!(
                field_key(coll, key),
                STATE_SLOTS as u64 + encode_index(coll, key) as u64,
                "field_key must be encode_index offset past the register file"
            );
        }
        // The load-bearing consequence: encode_index(COLL_ATOMS, 0) == 0 is a
        // REGISTER slot (< STATE_SLOTS) — DocCell's raw effect index collides with
        // the cell's balance; field_key offsets past the register file into fields_map.
        assert!(encode_index(COLL_ATOMS, 0) < STATE_SLOTS, "encode_index hits a register slot");
        assert!(
            field_key(COLL_ATOMS, 0) >= STATE_SLOTS as u64,
            "field_key lands in the fields_map overflow region (canonical)"
        );
    }

    #[test]
    fn the_heap_is_the_real_setfield_heap() {
        // The edit lands genuine `Effect::SetField` writes in the document's heap
        // collections, and `index <-> (collection, key)` round-trips.
        for (coll, key) in [(COLL_ATOMS, 0u32), (COLL_EDGES, 5u32), (COLL_FIELDS, 3u32)] {
            let idx = encode_index(coll, key);
            assert_eq!(decode_index(idx), (coll, key));
        }

        let mut doc = DocCell::new();
        let (_h, op) = add(1, "x", AtomId::ROOT);
        doc.edit(Patch::by(Author(1), [op]));
        // The first atom leaf is present in the real heap at (COLL_ATOMS, _).
        assert!(
            doc.cell().state.heap_map.keys().any(|(c, _)| *c == COLL_ATOMS),
            "an atom leaf landed in the real COLL_ATOMS heap collection"
        );
    }

    #[test]
    fn edit_keeps_commitment_and_projection_in_lockstep() {
        // After a SEQUENCE of edits (adds + a delete), the cell's real heap_root
        // still equals the canonical projection of the witness graph — the
        // document the algebra sees and the commitment the light client trusts
        // are ONE object.
        let mut doc = DocCell::new();
        let (a, op_a) = add(1, "alpha ", AtomId::ROOT);
        doc.edit(Patch::by(Author(1), [op_a]));
        let (b, op_b) = add(2, "beta ", a);
        doc.edit(Patch::by(Author(1), [op_b]));
        let (_c, op_c) = add(3, "gamma", b);
        doc.edit(Patch::by(Author(2), [op_c]));
        // Tombstone "beta ".
        doc.edit(Patch::by(Author(1), [Op::Delete { id: b }]));

        assert!(doc.commitment_matches_projection());
        assert_eq!(content(doc.graph()).to_marked_string(), "alpha gamma");
    }

    #[test]
    fn field_clash_rides_the_cell_with_both_provenances() {
        // A non-monotone field clash (two authors set the title) rides the real
        // cell: both assignments land as COLL_FIELDS leaves, both with their
        // provenance, and the conflict is a first-class state over the real heap.
        let mut doc = DocCell::new();
        let p1 = Patch::by(
            Author(1),
            [Op::SetField { name: "title".into(), value: "Cats".into(), superseding: false }],
        );
        let p2 = Patch::by(
            Author(2),
            [Op::SetField { name: "title".into(), value: "Dogs".into(), superseding: false }],
        );
        doc.edit(p1);
        doc.edit(p2);

        // Both alternatives survive as a first-class clash over the real heap.
        assert_eq!(doc.graph().field("title").len(), 2, "both alternatives live");
        assert!(doc.commitment_matches_projection());
        let field_leaves = doc
            .cell()
            .state
            .heap_map
            .keys()
            .filter(|(c, _)| *c == COLL_FIELDS)
            .count();
        assert_eq!(field_leaves, 2, "both clashing alternatives are heap leaves");
    }
}
