//! **The document-collaboration surface, in the tab** — the Pijul/conflicts-as-objects
//! flow (fork → diverge → stitch → a first-class conflict → resolve → publish), node-less,
//! over an in-tab verified executor.
//!
//! This is the wasm realization of the native desktop doc-collab flow (`deos-js`'s
//! `program_doc`, riding `dregg-doc`): a document is a **graph of alive/dead content atoms**
//! ([`dregg_doc::DocGraph`]); an edit is a **patch**; concurrent edits reconcile by **merge**,
//! the categorical **pushout** ([`dregg_doc::merge`]); and a **conflict** — two live,
//! mutually-unordered alternatives — is a *first-class STATE* the document carries
//! ([`dregg_doc::ConflictRegion`]), each alternative attributed to who wrote it, resolved by a
//! later patch ([`dregg_doc::resolutions_for`]), never a merge failure.
//!
//! `mozjs`/gpui can't link on wasm32 so we don't carry the native `program_doc`/cockpit here —
//! but the patch theory IS dependency-free and the umem-heap ride is pure `dregg-cell` (both in
//! the wasm graph), so [`DocCollabWorld`] re-expresses the SAME flow over its own in-tab cell:
//!
//! 1. **fork** — a doc-cell (agent 0) carries a base document, published to its umem-heap;
//! 2. **diverge** — two authors (alice, bob) branch off the shared tail and each append a line;
//! 3. **stitch** — `merge` the two branches = the pushout; a first-class [`ConflictRegion`]
//!    surfaces (the antichain), **held off-heap** — the committed umem boundary still equals the
//!    base; the conflict is rendered as a `ViewNode` ConflictView (alternatives side-by-side,
//!    attributed) via [`Self::view_tree_json`] / [`Self::view_html`];
//! 4. **resolve** — a one-click [`dregg_doc::ResolutionChoice`] (keep-one / order-both) collapses
//!    the conflict; the merged document is **published to the doc-cell's umem-heap as a real
//!    verified turn** ([`Self::publish`]): the resolved graph is projected into the cell's
//!    heap and the boundary `heap_root` resealed (the umem boundary — there is NO kernel
//!    heap-write effect, so this is the same off-executor reseal the native `DocHeapCell` ride
//!    uses, `turn/src/journal.rs` "awaiting the live heap-writing effect"), THEN a real cap-gated
//!    verified `SetField + IncrementNonce` turn over the in-tab executor binds the new boundary
//!    root as the receipted publish (the turn's recorded post-state commitment includes the
//!    freshly-resealed `heap_root`, limb 28).
//!
//! No kernel effect is added — the one extra fact (the boundary moved) rides the SAME
//! `SetField`/`IncrementNonce` the kernel already enforces, plus the off-executor umem reseal the
//! substrate already commits. The anti-forge tooth survives onto the real root: forging an
//! alternative's author or dropping an alternative changes `substrate_commit`, so a light client
//! cannot be shown a conflict that hides or forges an alternative
//! (`dregg-doc/src/substrate.rs`).

use std::collections::{BTreeMap, HashSet};

use wasm_bindgen::prelude::*;

use dregg_turn::{Effect, TurnResult};

use crate::runtime::DreggRuntime;

use deos_view::{parse_view_tree, render_html};
use dregg_doc::{
    AtomId, Author, ConflictRegion, Doc, DocGraph, Granularity, History, Patch, Rendered,
    ResolutionChoice, content, merge, resolutions_for, substrate_commit, to_heap_map,
};

/// The model slot the publish turn writes the document's umem boundary root into — a
/// high USER slot, disjoint from the kernel-reserved escrow/queue roots (`fields[3]`/`fields[4]`)
/// and the inspector's authorship slot (14). The witnessed value is the sorted-Poseidon2
/// `heap_root` commitment of the published document.
const PUBLISH_SLOT: usize = 20;

/// The fee (computrons) each publish turn meters against the doc-cell.
const PUBLISH_FEE: u64 = 10_000;

/// The two diverging authors + the resolver.
const ALICE: Author = Author(1);
const BOB: Author = Author(2);

/// The base document's shared opening line — every reading shares this clean prefix.
const BASE_LINE: &str = "A dreggverse document is a patch-theoretic object.\n";
/// Alice's divergent append (after the shared tail).
const ALICE_LINE: &str = "Alice: independent patches commute.\n";
/// Bob's divergent append (after the SAME shared tail — concurrent ⇒ an antichain).
const BOB_LINE: &str = "Bob: merge is the categorical pushout.\n";

/// The in-tab document-collaboration surface. One `DocCollabWorld` owns one runtime with one
/// **doc-cell** (agent 0) whose committed umem-heap `heap_root` IS the published document's
/// commitment. It drives the WHOLE Pijul flow — fork → diverge → stitch → a first-class conflict
/// → resolve → publish — node-less, every publish a REAL cap-gated verified turn over the
/// embedded executor leaving a receipt.
#[wasm_bindgen]
pub struct DocCollabWorld {
    rt: DreggRuntime,
    /// The shared (published) history — the FORK point both authors branch off.
    base: History,
    /// The anchor atom both divergent branches append after (the base's tail).
    tail: AtomId,
    /// The PUBLISHED document graph — the one bound by the doc-cell's committed umem boundary.
    published: DocGraph,
    /// The stitched merge carrying a first-class conflict, **held off-heap** until resolved.
    /// `None` once published (no pending conflict).
    merged: Option<DocGraph>,
    /// The resolution menu for the pending conflict (the buttons' `resolve` arg indexes this).
    choices: Vec<ResolutionChoice>,
}

#[wasm_bindgen]
impl DocCollabWorld {
    /// Mint a fresh doc-cell on its own embedded executor, seed the base document, and
    /// **publish it to the umem-heap** (the fork point). The doc-cell is agent 0 (single-custody,
    /// `AuthRequired::None` holder — the posture a card gets), funded so a metered publish turn
    /// has a source. The base is published via a REAL verified turn, so the genesis boundary
    /// itself leaves a receipt.
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<DocCollabWorld, JsError> {
        let mut rt = DreggRuntime::new();
        rt.try_create_agent("doc", 1_000_000)
            .map_err(|e| JsError::new(&e))?;

        // The base history: one shared line. Its tail atom anchors the later divergence.
        let mut base = History::new();
        let (tail, op) = Patch::add(1, BASE_LINE, AtomId::ROOT);
        base.commit(Patch::by(Author::SYSTEM, [op]));
        let published = base.replay();

        let mut world = DocCollabWorld {
            rt,
            base,
            tail,
            published,
            merged: None,
            choices: Vec::new(),
        };
        // Publish the base to the doc-cell's umem-heap as a real verified turn (the fork point).
        let g = world.published.clone();
        world.publish(&g).map_err(|e| JsError::new(&e))?;
        Ok(world)
    }

    /// The doc-cell's id (hex) — the document's sovereignty boundary, the agent of its turns.
    #[wasm_bindgen(js_name = cellId)]
    pub fn cell_id(&self) -> String {
        crate::bindings::hex_encode(&self.rt.agents[0].cell_id.0)
    }

    /// The document's commitment: the doc-cell's committed umem-heap boundary `heap_root` (hex).
    /// After a publish this equals `substrate_commit(published)` — the sorted-Poseidon2 root a
    /// light client trusts. It MOVES on every publish (a new resolved document → a new boundary).
    #[wasm_bindgen(js_name = commitmentHex)]
    pub fn commitment_hex(&self) -> String {
        let cell_id = self.rt.agents[0].cell_id;
        let root = self
            .rt
            .ledger
            .get(&cell_id)
            .map(|c| c.state.heap_root.to_bytes32())
            .unwrap_or([0u8; 32]);
        crate::bindings::hex_encode(&root)
    }

    /// The committed-receipt count — the audit tape length (one per published boundary, incl. the
    /// genesis base publish). Proves a publish was a real verified turn, not a local poke.
    #[wasm_bindgen(js_name = receiptCount)]
    pub fn receipt_count(&self) -> usize {
        self.rt.receipts.len()
    }

    /// True iff a stitched merge is currently carrying an unresolved conflict (held off-heap).
    #[wasm_bindgen(js_name = hasConflict)]
    pub fn has_conflict(&self) -> bool {
        self.merged
            .as_ref()
            .map(|g| content(g).has_conflict())
            .unwrap_or(false)
    }

    /// **The invariant: the doc-cell's committed umem boundary EQUALS the canonical projection of
    /// the published document.** When this holds, the document the algebra sees and the boundary
    /// the light client trusts are the same umem (the membership/anti-forge guarantee bites).
    #[wasm_bindgen(js_name = boundaryMatchesProjection)]
    pub fn boundary_matches_projection(&self) -> bool {
        let cell_id = self.rt.agents[0].cell_id;
        let Some(cell) = self.rt.ledger.get(&cell_id) else {
            return false;
        };
        cell.state.heap_root.to_bytes32() == substrate_commit(&self.published)
    }

    /// The pending conflict's alternatives as JSON (`[{author, text}]`) — what the ConflictView
    /// attributes side-by-side. Empty when there is no pending conflict.
    #[wasm_bindgen(js_name = alternativesJson)]
    pub fn alternatives_json(&self) -> String {
        use serde_json::json;
        let rows: Vec<serde_json::Value> = self
            .pending_region()
            .map(|r| {
                r.alternatives
                    .iter()
                    .map(|a| {
                        json!({
                            "author": author_name(a.provenance.author),
                            "text": a.text.trim_end_matches('\n'),
                        })
                    })
                    .collect()
            })
            .unwrap_or_default();
        json!(rows).to_string()
    }

    /// The current PUBLISHED document's rendered text (the resolved reading) — the clean content
    /// bound by the umem boundary.
    #[wasm_bindgen(js_name = publishedText)]
    pub fn published_text(&self) -> String {
        content(&self.published).to_marked_string()
    }

    /// **THE DOCUMENT VIEW-TREE** — the `{kind, props, children}` JSON the web renderer
    /// (`deos-view::parse_view_tree`) consumes. When a conflict is held it is a ConflictView
    /// (the clean prefix, the two alternatives attributed side-by-side, and a resolution `Button`
    /// per [`ResolutionChoice`]); when published it is the clean resolved document plus the umem
    /// boundary readout and a `stitch` affordance.
    #[wasm_bindgen(js_name = viewTreeJson)]
    pub fn view_tree_json(&self) -> String {
        self.build_view_tree().to_string()
    }

    /// **THE RENDERED HTML FRAGMENT** — `view_tree_json` walked through the SAME gpui-free web
    /// renderer (`deos-view::render_html`) the cockpit's web projection bakes. The live page sets
    /// this as the doc container's `innerHTML`, re-rendering WHOLESALE after every affordance
    /// (the tree SHAPE changes: the ConflictView collapses to the clean published document — a
    /// slot-repaint would not suffice).
    #[wasm_bindgen(js_name = viewHtml)]
    pub fn view_html(&self) -> String {
        match parse_view_tree(&self.view_tree_json()) {
            Ok(tree) => render_html(&tree, &[]),
            Err(e) => format!("<pre class=\"deos-text\">view-tree error: {e}</pre>"),
        }
    }

    /// **The affordance wire** — the web renderer fires `data-turn`/`data-arg` here:
    /// - `stitch` — diverge the two authors off the shared tail and merge (the pushout); a
    ///   first-class conflict surfaces, held off-heap.
    /// - `resolve` (`arg` = a [`ResolutionChoice`] index) — collapse the conflict with that
    ///   choice's ready patch and **publish** the merged document to the umem-heap as a real
    ///   verified turn.
    /// Any other affordance errors (the native `FireError::Unknown`).
    pub fn fire(&mut self, turn: &str, arg: i32) -> Result<(), JsError> {
        match turn {
            "stitch" => self.stitch().map_err(|e| JsError::new(&e)),
            "resolve" => self.resolve(arg as usize).map_err(|e| JsError::new(&e)),
            other => Err(JsError::new(&format!("unknown affordance: {other}"))),
        }
    }

    // ── internals ───────────────────────────────────────────────────────────────────────

    /// The pending conflict region (the first conflict in the held merge), if any.
    fn pending_region(&self) -> Option<ConflictRegion> {
        let merged = self.merged.as_ref()?;
        content(merged).conflicts().next().cloned()
    }

    /// **STITCH** — diverge alice and bob off the shared base tail (each appends a line at the
    /// SAME anchor → a concurrent antichain) and `merge` the two branches (the categorical
    /// pushout). The merged graph carries a first-class [`ConflictRegion`]; it is **held off-heap**
    /// (the committed umem boundary still equals the published base) and the resolution menu is
    /// cached. Idempotent re-stitch is a no-op-ish reset to the same held conflict.
    fn stitch(&mut self) -> Result<(), String> {
        let base_graph = self.base.replay();
        // Two authors append a distinct line after the shared tail — concurrent ⇒ an antichain.
        let a = Patch::by(ALICE, [Patch::add(2, ALICE_LINE, self.tail).1]).apply_to(&base_graph);
        let b = Patch::by(BOB, [Patch::add(3, BOB_LINE, self.tail).1]).apply_to(&base_graph);
        let merged = merge(&a, &b);

        let rendered = content(&merged);
        let region = rendered.conflicts().next().ok_or_else(|| {
            "stitch produced no conflict (the branches did not diverge)".to_string()
        })?;
        // The resolver is alice; the choices are ready patches (keep-each / order-both).
        self.choices = resolutions_for(&merged, region, ALICE);
        self.merged = Some(merged);
        Ok(())
    }

    /// **RESOLVE + PUBLISH** — apply resolution choice `idx`'s ready patch to the held merge
    /// (collapsing the conflict) and publish the resolved document to the doc-cell's umem-heap as
    /// a real verified turn.
    fn resolve(&mut self, idx: usize) -> Result<(), String> {
        let merged = self
            .merged
            .as_ref()
            .ok_or_else(|| "no pending conflict to resolve (stitch first)".to_string())?;
        let choice = self
            .choices
            .get(idx)
            .ok_or_else(|| format!("resolution choice {idx} out of range"))?;
        let resolved = choice.patch.apply_to(merged);
        // The resolution must genuinely collapse the conflict (the algebra guarantees it; assert
        // the post-state is clean so a buggy choice is surfaced, never silently published).
        if content(&resolved).has_conflict() {
            return Err("the chosen resolution did not collapse the conflict".to_string());
        }
        self.publish(&resolved)?;
        self.published = resolved;
        self.merged = None;
        self.choices.clear();
        Ok(())
    }

    /// **PUBLISH `graph` to the doc-cell's umem-heap as a real verified turn.**
    ///
    /// (1) Reproject the document into the doc-cell's umem-heap and reseal the boundary
    ///     `heap_root` (off-executor — there is no kernel heap-write effect; this is the same
    ///     reseal the native `DocHeapCell` ride uses). The cell's committed umem boundary now
    ///     EQUALS `substrate_commit(graph)`, binding every atom/edge/field leaf (the anti-forge
    ///     tooth: both alternatives of any conflict are bound in the root).
    /// (2) Commit a REAL cap-gated verified turn — `SetField(PUBLISH_SLOT, boundary_root)` +
    ///     `IncrementNonce` — over the in-tab executor. The executor recomputes the cell's
    ///     state commitment, which now includes the freshly-resealed `heap_root` (limb 28), so
    ///     the receipt genuinely witnesses the published boundary. A rejected turn is surfaced.
    fn publish(&mut self, graph: &DocGraph) -> Result<(), String> {
        publish_doc_graph(&mut self.rt, 0, graph)
    }

    /// Build the document view-tree JSON value for the current state (ConflictView vs published).
    fn build_view_tree(&self) -> serde_json::Value {
        use serde_json::json;

        let mut children: Vec<serde_json::Value> = Vec::new();

        if let Some(region) = self.pending_region() {
            // ── THE CONFLICT VIEW — a stitched merge holding a first-class conflict ──────────
            children.push(json!({ "kind": "text", "props": { "text": "Document collaboration — a stitched merge (the pushout)" } }));
            // The clean shared prefix (the published reading, still the committed boundary).
            children.push(
                json!({ "kind": "text", "props": { "text": clean_prefix(&self.published) } }),
            );
            children.push(json!({
                "kind": "text",
                "props": { "text": "⚠ conflict: two authors edited concurrently — a first-class state, held OFF the umem-heap until resolved." }
            }));

            // The alternatives, attributed, SIDE BY SIDE (one column per alternative).
            let columns: Vec<serde_json::Value> = region
                .alternatives
                .iter()
                .map(|a| {
                    json!({
                        "kind": "vstack",
                        "props": {},
                        "children": [
                            { "kind": "text", "props": { "text": format!("✎ {}", author_name(a.provenance.author)) } },
                            { "kind": "text", "props": { "text": a.text.trim_end_matches('\n').to_string() } }
                        ]
                    })
                })
                .collect();
            children.push(json!({ "kind": "row", "props": {}, "children": columns }));

            // One resolution Button per ready ChoIce — a click collapses the conflict + publishes.
            children.push(json!({ "kind": "text", "props": { "text": "Resolve (publishes the merged document to the umem-heap as a verified turn):" } }));
            let mut buttons: Vec<serde_json::Value> = Vec::new();
            for (i, c) in self.choices.iter().enumerate() {
                buttons.push(json!({
                    "kind": "button",
                    "props": { "label": c.label.clone(), "on_click": { "turn": "resolve", "arg": i as i64 } }
                }));
            }
            children.push(json!({ "kind": "vstack", "props": {}, "children": buttons }));
        } else {
            // ── THE PUBLISHED DOCUMENT — the resolved reading bound by the umem boundary ─────
            children.push(json!({ "kind": "text", "props": { "text": "Document — published to the umem-heap ✓" } }));
            children.push(json!({ "kind": "text", "props": { "text": content(&self.published).to_marked_string() } }));
            children.push(json!({
                "kind": "text",
                "props": { "text": format!("umem boundary (heap_root): {}…", short_hex(&self.commitment_hex())) }
            }));
            children.push(json!({
                "kind": "text",
                "props": { "text": format!("verified publish turns (receipts): {}", self.receipt_count()) }
            }));
            children.push(json!({
                "kind": "button",
                "props": { "label": "stitch a concurrent divergence", "on_click": { "turn": "stitch", "arg": 0 } }
            }));
        }

        json!({ "kind": "vstack", "props": {}, "children": children })
    }
}

/// The shared clean prefix of the published document (the reading both branches forked from).
fn clean_prefix(published: &DocGraph) -> String {
    let r: Rendered = content(published);
    r.to_marked_string()
}

/// A short author display name (mirrors `dregg_doc`'s resolution-label mapping).
fn author_name(a: Author) -> String {
    match a.0 {
        0 => "system".to_string(),
        1 => "alice".to_string(),
        2 => "bob".to_string(),
        other => format!("author {other:x}"),
    }
}

/// First 12 hex chars of a hex string (the legible umem-boundary readout).
fn short_hex(hex: &str) -> String {
    hex.chars().take(12).collect()
}

/// **PUBLISH `graph` to a doc-cell's umem-heap as a real verified turn** — the shared
/// publish path both the conflict-resolution surface ([`DocCollabWorld`]) and the free-text
/// editing surface ([`DocTextWorld`]) ride. See [`DocCollabWorld::publish`] for the two-step
/// semantics (off-executor umem reseal, then a cap-gated `SetField(PUBLISH_SLOT) +
/// IncrementNonce` verified turn binding the new boundary root as the receipted publish).
/// FAIL-CLOSED: a rejected or non-committed turn returns `Err`, never a silent success.
fn publish_doc_graph(
    rt: &mut DreggRuntime,
    agent_idx: usize,
    graph: &DocGraph,
) -> Result<(), String> {
    let cell_id = rt.agents[agent_idx].cell_id;
    let boundary: [u8; 32] = substrate_commit(graph);

    // (1) Off-executor umem reseal: the doc-cell's heap IS the document projection.
    let heap: BTreeMap<(u32, u32), [u8; 32]> = to_heap_map(graph);
    {
        let cell = rt
            .ledger
            .get_mut(&cell_id)
            .ok_or_else(|| "doc-cell vanished from the ledger".to_string())?;
        cell.state.heap_map = heap;
        cell.state.reseal_heap_root();
        // The boundary the executor will now commit equals the canonical projection.
        debug_assert_eq!(cell.state.heap_root.to_bytes32(), boundary);
    }

    // (2) The real verified turn: bind the new umem boundary root as the receipted publish.
    let effects = vec![
        Effect::SetField {
            cell: cell_id,
            index: PUBLISH_SLOT as u64,
            value: boundary,
        },
        Effect::IncrementNonce { cell: cell_id },
    ];
    match rt.execute_turn_for_agent(agent_idx, effects, PUBLISH_FEE) {
        TurnResult::Committed { .. } => Ok(()),
        TurnResult::Rejected { reason, at_action } => Err(format!(
            "publish turn rejected: {reason} (at {at_action:?})"
        )),
        other => Err(format!("publish turn not committed: {other:?}")),
    }
}

// ═════════════════════════════════════════════════════════════════════════════════════════
//  FREE-TEXT DOCUMENT EDITING — the person types prose; each edit is a real patch → verified turn
// ═════════════════════════════════════════════════════════════════════════════════════════

/// The wasm-side engine for **free-text document editing**: a person types/edits prose and each
/// edit becomes a real [`dregg_doc::Patch`] against the current document (via [`Doc::edit`]'s
/// token-LCS diff → the MINIMAL `Add`/`Delete` patch, never a full rewrite — kept tokens reuse
/// their existing atom ids), applied to the patch-[`History`], then published as a real cap-gated
/// verified turn resealing the doc-cell's umem boundary. This is the wasm realization of the
/// goal's "keyed reconciler / DOM-schema editing": a `<dregg-doc>`'s buffer text is diffed into a
/// patch here, exactly as a conflict resolution is — a stranger can check the receipt.
///
/// It reuses `dregg-doc`'s diff/commit/merge WHOLESALE (no new patch logic): [`Doc::edit`] for the
/// edit → patch step, [`dregg_doc::merge`] for concurrent reconciliation (disjoint edits commute
/// clean; a genuine same-span edit surfaces a first-class [`ConflictRegion`]), and the same
/// [`publish_doc_graph`] verified-turn path [`DocCollabWorld`] uses. Word [`Granularity`] is the
/// default so prose edits produce fine-grained, minimal patches.
#[wasm_bindgen]
pub struct DocTextWorld {
    rt: DreggRuntime,
    /// The editable document — a patch-[`History`] authored by typing text. Each
    /// [`Self::apply_text_edit`] diffs the new text against this and commits the minimal patch.
    doc: Doc,
    /// The editing author stamped onto inserted atoms (provenance flows as usual).
    author: Author,
    /// The last PUBLISHED document graph — the one the doc-cell's committed umem boundary binds.
    /// Updated on [`Self::publish_edit`]; unpublished edits are NOT yet bound (the boundary lags,
    /// as it should, until the edit is published as a verified turn).
    published: DocGraph,
}

/// The summary an [`Self::apply_text_edit`] returns: how the minimal patch moved the atom graph.
struct EditSummary {
    /// Fresh atoms the edit inserted (new ids, never in the pre-edit graph).
    atoms_added: usize,
    /// Previously-alive atoms the edit tombstoned (LCS deletions).
    atoms_tombstoned: usize,
    /// The document's rendered text after the edit.
    text: String,
}

#[wasm_bindgen]
impl DocTextWorld {
    /// Mint a fresh doc-cell on its own embedded executor, seed the document with `initial_text`
    /// (authored by `author_id`, at word [`Granularity`]), and **publish it to the umem-heap** as
    /// a real verified turn (the genesis boundary). Subsequent [`Self::apply_text_edit`]s diff
    /// against this and [`Self::publish_edit`] reseals the boundary.
    #[wasm_bindgen(constructor)]
    pub fn new(initial_text: String, author_id: u32) -> Result<DocTextWorld, JsError> {
        let mut rt = DreggRuntime::new();
        rt.try_create_agent("doc", 1_000_000)
            .map_err(|e| JsError::new(&e))?;

        let author = Author(author_id as u64);
        let mut doc = Doc::new(Granularity::Word);
        // Seed the initial prose (a diff from the empty document = one Add per token).
        doc.edit(author, &initial_text);
        let published = doc.history().replay();

        let mut world = DocTextWorld {
            rt,
            doc,
            author,
            published,
        };
        // Publish the seed to the doc-cell's umem-heap as a real verified turn (the genesis point).
        let g = world.published.clone();
        publish_doc_graph(&mut world.rt, 0, &g).map_err(|e| JsError::new(&e))?;
        Ok(world)
    }

    /// **APPLY A FREE-TEXT EDIT** — the person edited the prose to `new_text`. Diff it against the
    /// current document ([`Doc::edit`]'s token-LCS at word granularity), produce the MINIMAL
    /// `Add`/`Delete` [`Patch`], and commit it to the history. The inserted atoms carry the
    /// editing author's provenance. Returns a JSON summary
    /// `{ "atoms_added", "atoms_tombstoned", "text" }` — the counts prove the edit is a minimal
    /// patch (a word replaced ⇒ one atom added + one tombstoned, the surrounding words KEPT by
    /// their existing atom ids), NOT a full rewrite. The boundary does NOT move until
    /// [`Self::publish_edit`].
    #[wasm_bindgen(js_name = applyTextEdit)]
    pub fn apply_text_edit(&mut self, new_text: String) -> String {
        use serde_json::json;
        let s = self.edit_internal(&new_text);
        json!({
            "atoms_added": s.atoms_added,
            "atoms_tombstoned": s.atoms_tombstoned,
            "text": s.text,
        })
        .to_string()
    }

    /// **PUBLISH THE EDIT** — reseal the doc-cell's umem boundary `heap_root =
    /// substrate_commit(current document)` and commit a real cap-gated verified turn (the SAME
    /// publish path a conflict resolution uses). A free-text edit thus lands as a verified turn a
    /// stranger can check. Returns a JSON receipt `{ "receiptCount", "commitmentHex" }`.
    /// FAIL-CLOSED: a rejected publish turn returns an error, never a silent success.
    #[wasm_bindgen(js_name = publishEdit)]
    pub fn publish_edit(&mut self) -> Result<String, JsError> {
        use serde_json::json;
        self.publish_internal().map_err(|e| JsError::new(&e))?;
        Ok(json!({
            "receiptCount": self.rt.receipts.len(),
            "commitmentHex": self.commitment_hex(),
        })
        .to_string())
    }

    /// The current document's rendered text (the post-edit state the JS reconciler reads).
    #[wasm_bindgen(js_name = currentText)]
    pub fn current_text(&self) -> String {
        self.doc.text()
    }

    /// **THE RENDERED HTML FRAGMENT** — the current document walked through the gpui-free web
    /// renderer (`deos-view::render_html`), the same renderer the cockpit's web projection bakes.
    /// The live `<dregg-doc>` sets this as its container's `innerHTML` after each edit/publish so
    /// the reconciler can paint the post-edit state.
    #[wasm_bindgen(js_name = render)]
    pub fn render(&self) -> String {
        use serde_json::json;
        let tree = json!({
            "kind": "vstack",
            "props": {},
            "children": [
                { "kind": "text", "props": { "text": "Document — free-text editing (each edit a patch → verified turn)" } },
                { "kind": "text", "props": { "text": self.doc.text() } },
                { "kind": "text", "props": { "text": format!("umem boundary (heap_root): {}…", short_hex(&self.commitment_hex())) } },
                { "kind": "text", "props": { "text": format!("verified publish turns (receipts): {}", self.rt.receipts.len()) } }
            ]
        })
        .to_string();
        match parse_view_tree(&tree) {
            Ok(t) => render_html(&t, &[]),
            Err(e) => format!("<pre class=\"deos-text\">view-tree error: {e}</pre>"),
        }
    }

    /// The doc-cell's id (hex) — the document's sovereignty boundary.
    #[wasm_bindgen(js_name = cellId)]
    pub fn cell_id(&self) -> String {
        crate::bindings::hex_encode(&self.rt.agents[0].cell_id.0)
    }

    /// The document's commitment: the doc-cell's committed umem-heap boundary `heap_root` (hex).
    /// After a [`Self::publish_edit`] this equals `substrate_commit(published)`.
    #[wasm_bindgen(js_name = commitmentHex)]
    pub fn commitment_hex(&self) -> String {
        let cell_id = self.rt.agents[0].cell_id;
        let root = self
            .rt
            .ledger
            .get(&cell_id)
            .map(|c| c.state.heap_root.to_bytes32())
            .unwrap_or([0u8; 32]);
        crate::bindings::hex_encode(&root)
    }

    /// The committed-receipt count — one per published boundary (incl. the genesis seed publish).
    #[wasm_bindgen(js_name = receiptCount)]
    pub fn receipt_count(&self) -> usize {
        self.rt.receipts.len()
    }

    /// **The invariant: the doc-cell's committed umem boundary EQUALS `substrate_commit` of the
    /// last PUBLISHED document.** True right after a [`Self::publish_edit`]; an unpublished edit
    /// leaves the boundary lagging the working document (correctly — it is not yet a verified turn).
    #[wasm_bindgen(js_name = boundaryMatchesProjection)]
    pub fn boundary_matches_projection(&self) -> bool {
        let cell_id = self.rt.agents[0].cell_id;
        let Some(cell) = self.rt.ledger.get(&cell_id) else {
            return false;
        };
        cell.state.heap_root.to_bytes32() == substrate_commit(&self.published)
    }

    // ── internals ───────────────────────────────────────────────────────────────────────

    /// Diff `new_text` into the document via [`Doc::edit`] and summarize the graph move by
    /// comparing the pre- and post-edit atom sets (added = fresh ids; tombstoned = previously-alive
    /// ids now dead). This is a read of `dregg-doc`'s OWN diff/commit result, not a reimplemented
    /// diff — the minimal-patch property is `Doc::edit`'s, surfaced here.
    fn edit_internal(&mut self, new_text: &str) -> EditSummary {
        let before = self.doc.history().replay();
        let before_ids: HashSet<AtomId> = before.atoms().map(|a| a.id).collect();
        let before_alive: HashSet<AtomId> = before
            .atoms()
            .filter(|a| a.is_alive())
            .map(|a| a.id)
            .collect();

        self.doc.edit(self.author, new_text);

        let after = self.doc.history().replay();
        let atoms_added = after
            .atoms()
            .filter(|a| !before_ids.contains(&a.id))
            .count();
        let atoms_tombstoned = after
            .atoms()
            .filter(|a| !a.is_alive() && before_alive.contains(&a.id))
            .count();

        EditSummary {
            atoms_added,
            atoms_tombstoned,
            text: self.doc.text(),
        }
    }

    /// Publish the current document as a verified turn and record it as the new published boundary.
    fn publish_internal(&mut self) -> Result<(), String> {
        let g = self.doc.history().replay();
        publish_doc_graph(&mut self.rt, 0, &g)?;
        self.published = g;
        Ok(())
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    /// THE FREE-TEXT EDIT LOOP: a person edits prose → a MINIMAL patch (one atom added + one
    /// tombstoned, the surrounding words KEPT — not a full rewrite) → publish → the doc-cell's
    /// committed umem boundary equals `substrate_commit` of the edited document, and the current
    /// text reflects the edit.
    #[test]
    fn free_text_edit_is_a_minimal_patch_then_a_verified_turn() {
        let mut world =
            DocTextWorld::new("the quick brown fox".to_string(), 1).expect("mint doc-cell");

        // Genesis seed already published: one receipt, boundary matches the seed projection.
        assert_eq!(
            world.receipt_count(),
            1,
            "the seed published as a verified turn"
        );
        assert!(
            world.boundary_matches_projection(),
            "the seed boundary equals substrate_commit(seed)"
        );

        // The person edits "brown" → "RED". The LCS preserves "the quick"/"fox": exactly ONE atom
        // is added ("RED ") and ONE tombstoned ("brown ") — NOT a four-atom full rewrite.
        let s = world.edit_internal("the quick RED fox");
        assert_eq!(
            s.atoms_added, 1,
            "one word inserted (minimal, not a rewrite)"
        );
        assert_eq!(
            s.atoms_tombstoned, 1,
            "one word deleted (minimal, not a rewrite)"
        );
        assert_eq!(s.text, "the quick RED fox");
        assert_eq!(world.current_text(), "the quick RED fox");

        // Before publishing, the committed boundary still binds the last PUBLISHED (seed)
        // document — the edited WORKING doc is not yet bound (the edit isn't a verified turn yet).
        let cell_id = world.rt.agents[0].cell_id;
        let committed_before_pub = world
            .rt
            .ledger
            .get(&cell_id)
            .unwrap()
            .state
            .heap_root
            .to_bytes32();
        assert_ne!(
            committed_before_pub,
            substrate_commit(&world.doc.history().replay()),
            "the edited working doc is NOT yet bound by the committed boundary"
        );
        assert!(
            world.boundary_matches_projection(),
            "the boundary still binds the last published document until publish"
        );

        // Publish the edit: a real verified turn reseals the boundary.
        world.publish_internal().expect("publish the edit");
        assert_eq!(
            world.receipt_count(),
            2,
            "the edit published as a second verified turn"
        );

        // The receipt's heap_root EQUALS substrate_commit of the edited document.
        let committed = world
            .rt
            .ledger
            .get(&cell_id)
            .unwrap()
            .state
            .heap_root
            .to_bytes32();
        let edited_projection = substrate_commit(&world.doc.history().replay());
        assert_eq!(
            committed, edited_projection,
            "the committed umem boundary binds the edited document"
        );
        assert!(world.boundary_matches_projection());
    }

    /// TWO CONCURRENT EDITS TO DIFFERENT WORDS MERGE CLEAN — disjoint edits commute (the pushout
    /// carries no conflict). Reuses `dregg-doc`'s `merge` wholesale.
    #[test]
    fn concurrent_disjoint_edits_merge_clean() {
        let mut base = Doc::new(Granularity::Word);
        base.edit(Author(1), "the quick brown fox");
        let shared = base.history().clone();

        // Alice replaces "quick"; Bob replaces "fox" — disjoint spans.
        let mut alice = Doc::from_history(shared.clone(), Granularity::Word);
        alice.edit(Author(1), "the SLOW brown fox");
        let mut bob = Doc::from_history(shared.clone(), Granularity::Word);
        bob.edit(Author(2), "the quick brown DOG");

        let merged = merge(&alice.history().replay(), &bob.history().replay());
        let rendered = content(&merged);
        assert!(
            !rendered.has_conflict(),
            "disjoint word edits reconcile without a conflict"
        );
        assert_eq!(
            rendered.to_marked_string(),
            "the SLOW brown DOG",
            "both disjoint edits land in the merged document"
        );
    }

    /// A GENUINE SAME-SPAN CONFLICT IS FIRST-CLASS — two authors edit the SAME word differently,
    /// so the merge surfaces a `ConflictRegion` (shown, never silently merged away).
    #[test]
    fn same_span_edit_is_a_first_class_conflict() {
        let mut base = Doc::new(Granularity::Word);
        base.edit(Author(1), "the quick brown fox");
        let shared = base.history().clone();

        // Both replace the SAME word "quick" — with different words.
        let mut alice = Doc::from_history(shared.clone(), Granularity::Word);
        alice.edit(Author(1), "the RED brown fox");
        let mut bob = Doc::from_history(shared.clone(), Granularity::Word);
        bob.edit(Author(2), "the BLUE brown fox");

        let merged = merge(&alice.history().replay(), &bob.history().replay());
        let rendered = content(&merged);
        assert!(
            rendered.has_conflict(),
            "a same-span edit is a first-class conflict, not a silent merge"
        );
        // Both alternatives are present and attributed (neither is dropped).
        let region = rendered.conflicts().next().expect("a conflict region");
        let authors: HashSet<u64> = region
            .alternatives
            .iter()
            .map(|a| a.provenance.author.0)
            .collect();
        assert!(
            authors.contains(&1) && authors.contains(&2),
            "both authors' alternatives are carried in the conflict"
        );
    }
}
