//! THE DOCUMENT EDITOR model — the cockpit's DOCS tab over the dreggverse
//! document language (`docs/deos/DOCUMENT-LANGUAGE.md`).
//!
//! A dreggverse document is a *patch-theoretic object riding the cell substrate*:
//! a document is a cell, an edit is a **patch is a turn** (a real receipt), the
//! content is the fold of the patch-history, and a **conflict is a first-class
//! STATE** you live in (two live alternatives, each attributed to who wrote it),
//! resolved by a later patch — never a merge failure.
//!
//! This module is the gpui-free MODEL the DOCS panel renders (the established
//! `web_cells`/`landing` discipline: a pure, `cargo test`-able text model; the
//! cockpit's gpui layer paints it). It RIDES — never re-expresses — the real
//! `dregg-doc` patch core:
//!
//! - **An edit is a cap-gated turn.** [`DocEditor::edit`] drives every edit
//!   through `dregg_doc::ExecutorDrivenDoc::edit`, which builds a genuine
//!   `dregg_turn::Turn` and runs it through the real `dregg_turn::TurnExecutor`.
//!   An editor that lacks the per-region edit cap is **refused in-band**
//!   (`TurnError::CapabilityNotHeld`, the anti-ghost tooth — a `Result` error,
//!   never a panic), and the document is left untouched. A committed edit returns
//!   a finalized `TurnReceipt` whose pre/post-state hashes are the real cell
//!   commitment.
//!
//! - **The content is the fold.** [`DocEditor::rendered`] reads
//!   `dregg_doc::content` over the executor-driven witness graph — the
//!   linearized prose plus any first-class `ConflictRegion`s.
//!
//! - **Conflicts are states.** [`DocEditor::sow_conflict`] commits two concurrent
//!   alternative edits (two distinct authors append after the same atom — both
//!   real cap-gated turns) so the document carries a genuine `Regime::Prose`
//!   antichain, OR two concurrent single-valued field writes (a `Regime::Field`
//!   conservation/authority clash). The renderer surfaces BOTH alternatives,
//!   each tagged with its provenance (resolved to the real receipt when one
//!   exists). [`DocEditor::resolve_prose`] / [`DocEditor::resolve_field`] commit a
//!   resolving patch (a real cap-gated turn) that collapses the antichain.
//!
//! - **Transclusion + backlinks are the built Nelson pieces.** A document quotes
//!   another cell through the verified `web_cells::Transclusion` (content-
//!   addressed + receipt + quorum), and "what links here" is the
//!   `links_here::LinksHerePanel` witness-graph read backward — both already in
//!   this crate. [`DocEditor::transclusion`] / [`DocEditor::backlinks`] surface
//!   them on the document so the editor is a hypermedia surface, not an island.

use dregg_cell::CellId;
use dregg_doc::{
    content, resolutions, resolve_connect_by, resolve_field, resolve_keep_in, walk_atoms,
    Alternative, AtomId, Author, ConflictRegion, ExecutorDrivenDoc, Op, Patch, Regime,
    RegionResolutions, Rendered, ResolutionChoice, Segment,
};
use dregg_turn::TurnError;

use crate::world::World;

/// One author identity the editor attributes edits to. Maps to a `dregg_doc::Author`
/// (the conflict view attributes each alternative to one of these).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DocAuthor {
    /// The underlying patch-algebra author id.
    pub id: u64,
    /// A short human name for the conflict-view attribution.
    pub name: &'static str,
}

impl DocAuthor {
    /// The two demo co-authors whose concurrent edits sow a first-class conflict.
    pub const ALICE: DocAuthor = DocAuthor {
        id: 1,
        name: "alice",
    };
    pub const BOB: DocAuthor = DocAuthor { id: 2, name: "bob" };

    fn author(self) -> Author {
        Author(self.id)
    }

    /// Resolve a `dregg_doc::Author` back to a display name (for the conflict view).
    pub fn name_of(author: Author) -> &'static str {
        match author.0 {
            0 => "system",
            1 => "alice",
            2 => "bob",
            _ => "other",
        }
    }
}

/// The outcome of an edit attempt: a committed turn (finalized receipt) or an
/// in-band refusal (the editor lacked the per-region edit cap, or the edit was a
/// no-op). A refusal is a FEATURE — the anti-ghost tooth made visible.
#[derive(Clone, Debug)]
pub enum EditOutcome {
    /// The edit committed as a real cap-gated turn. Carries the receipt hash, the
    /// pre/post state commitments, and the action count (the kernel writes).
    Committed {
        /// The committed turn's receipt hash (the provenance handle).
        receipt_hash: [u8; 32],
        /// The cell-state commitment before the edit.
        pre_state: [u8; 32],
        /// The cell-state commitment after the edit (moved — the edit landed).
        post_state: [u8; 32],
        /// The number of `SetField` effects the edit performed.
        actions: usize,
        /// Whether the executor finalized the receipt (driving the real executor
        /// IS the finality upgrade).
        finalized: bool,
    },
    /// The edit was REFUSED in-band: the editor lacks the region cap (the
    /// per-region edit gate), or it was a no-op (no change to commit). The
    /// document is untouched.
    Refused {
        /// A legible reason (`CapabilityNotHeld` for the cap gate; "no change"
        /// for a no-op).
        reason: String,
        /// True iff this was the per-region cap refusal (the security gate), as
        /// opposed to a benign no-op.
        unauthorized: bool,
    },
}

impl EditOutcome {
    /// True iff the edit committed.
    pub fn committed(&self) -> bool {
        matches!(self, EditOutcome::Committed { .. })
    }

    /// True iff the edit was refused by the per-region cap gate (the security
    /// refusal, not a no-op).
    pub fn unauthorized(&self) -> bool {
        matches!(
            self,
            EditOutcome::Refused {
                unauthorized: true,
                ..
            }
        )
    }

    /// A one-line banner for the panel.
    pub fn banner(&self) -> String {
        match self {
            EditOutcome::Committed {
                receipt_hash,
                actions,
                finalized,
                ..
            } => format!(
                "✓ committed as a turn · {} effect{} · {} · receipt {}",
                actions,
                if *actions == 1 { "" } else { "s" },
                if *finalized { "FINAL" } else { "tentative" },
                hex8(receipt_hash),
            ),
            EditOutcome::Refused {
                reason,
                unauthorized,
            } => {
                if *unauthorized {
                    format!("⛔ REFUSED in-band (the anti-ghost tooth): {reason}")
                } else {
                    format!("· no change: {reason}")
                }
            }
        }
    }
}

/// One rendered alternative within a conflict, attributed to its author and (when
/// a committed receipt exists) its receipt — "who wrote which alternative" is a
/// substrate FACT, not a guess.
#[derive(Clone, Debug)]
pub struct AttributedAlternative {
    /// The rendered text / field value of this alternative.
    pub text: String,
    /// The authoring identity's display name.
    pub author_name: &'static str,
    /// The fork-point atom id a prose resolution `Connect`s or `Delete`s (unused
    /// for a field clash).
    pub head: AtomId,
    /// The witnessing receipt hash, when this alternative's patch committed a real
    /// turn (the provenance IS the receipt). `None` when the alternative came from
    /// a witness-only merge with no retained receipt.
    pub receipt_hash: Option<[u8; 32]>,
}

/// A first-class conflict the document is living in: its regime (is it real?), the
/// clashing field name (if any), and the attributed alternatives.
#[derive(Clone, Debug)]
pub struct ConflictView {
    /// Prose (an illusory/unilaterally-resolvable antichain) or Field (a
    /// conservation/authority clash that may need consensus).
    pub regime: Regime,
    /// The field name for a `Regime::Field` clash; `None` for a prose antichain.
    pub field: Option<String>,
    /// Whether resolving may require consensus (a field authority/conservation
    /// clash) vs. being resolvable unilaterally by a region author.
    pub needs_consensus: bool,
    /// The live alternatives, each attributed to who wrote it.
    pub alternatives: Vec<AttributedAlternative>,
}

/// A first-class conflict rendered INLINE for editing: the attributed alternatives
/// (both shown, each tagged with who wrote it — provenance IS the receipt) PLUS the
/// one-click resolution choices a reader can take. This is the conflict-as-editor
/// surface: "two people wrote this differently — here's both — click to keep one,
/// order them, or settle the field", every click a single cap-gated turn.
#[derive(Clone, Debug)]
pub struct InlineConflict {
    /// The attributed alternatives (the both-shown-with-provenance view).
    pub view: ConflictView,
    /// The ready resolution gestures, each a one-click patch.
    pub choices: Vec<ResolutionChoice>,
}

impl InlineConflict {
    /// The resolution that loses nothing (keeps every alternative, ordering them) —
    /// the safe default a one-click "resolve, keep both" button arms.
    pub fn keep_all_choice(&self) -> Option<&ResolutionChoice> {
        self.choices.iter().find(|c| c.keeps_all())
    }
}

/// THE DOCUMENT EDITOR — a document riding a real cell, edited through the genuine
/// executor, with conflicts-as-states + the hypermedia (transclusion/backlinks)
/// faces.
pub struct DocEditor {
    /// The executor-driven document: an edit is a cap-gated turn through the real
    /// `dregg_turn::TurnExecutor`. The editor (author cell) HOLDS the per-region
    /// edit cap to the document (region) cell, so authorized edits commit.
    doc: ExecutorDrivenDoc,
    /// A SECOND executor-driven document whose editor LACKS the region cap — the
    /// unauthorized-edit demonstration. An edit here is refused in-band by the
    /// executor's cross-cell cap gate (`CapabilityNotHeld`).
    unauthorized: ExecutorDrivenDoc,
    /// The receipt hash per author-patch that committed, keyed by `Author` — used
    /// to attribute a conflict alternative to its witnessing receipt. (The
    /// executor-driven path commits one author per turn; we record the latest
    /// committed receipt per author so the conflict view can show provenance.)
    receipt_by_author: std::collections::BTreeMap<u64, [u8; 32]>,
    /// The running clean text the ergonomic text-diff edit path diffs against (the
    /// `Doc::edit`-style author-by-typing surface). Mirrors the committed clean
    /// content.
    draft_text: String,
}

impl DocEditor {
    /// Open a fresh document editor. Boots with a real region cell and an editor
    /// cell holding the per-region edit cap, plus a parallel unauthorized editor
    /// (no cap) for the refusal demonstration.
    pub fn new() -> Self {
        let mut ed = DocEditor {
            // editor seed 11, region seed 12, editor HOLDS the region cap.
            doc: ExecutorDrivenDoc::new(11, 12, true),
            // editor seed 21, region seed 22, editor LACKS the region cap.
            unauthorized: ExecutorDrivenDoc::new(21, 22, false),
            receipt_by_author: std::collections::BTreeMap::new(),
            draft_text: String::new(),
        };
        // Seed a small opening sentence so the panel boots on real content rather
        // than an empty pane (a single authorized edit = a real turn).
        let _ = ed.append("The dreggverse document is a patch. ", DocAuthor::ALICE);
        ed
    }

    /// The document (region) cell id — the document's substrate identity.
    pub fn region_id(&self) -> CellId {
        self.doc.region_id()
    }

    /// The editor (author) cell id holding the per-region edit cap.
    pub fn editor_id(&self) -> CellId {
        self.doc.editor_id()
    }

    /// The document's commitment: the region cell's real canonical state
    /// commitment (which absorbs the `fields_root` the executor writes).
    pub fn commitment(&self) -> [u8; 32] {
        self.doc.state_commitment()
    }

    /// True iff the document the patch algebra sees and the commitment the light
    /// client trusts are the same object (the seam is closed through the executor).
    pub fn commitment_matches(&self) -> bool {
        self.doc.commitment_matches_projection()
    }

    /// The current rendered content: the linearized prose plus any first-class
    /// conflict regions (the fold of the patch-history).
    pub fn rendered(&self) -> Rendered {
        content(self.doc.graph())
    }

    /// The live document's folded [`dregg_doc::DocGraph`] — the source the moldable
    /// `DocumentInspection` reads (so the DOCS tab can surface the document as an
    /// inspectable object, the same way every other lens inspects its target).
    pub fn graph(&self) -> &dregg_doc::DocGraph {
        self.doc.graph()
    }

    /// The current CLEAN text (the fold's clean segments concatenated). A
    /// conflicted region renders separately via [`Self::conflicts`].
    pub fn clean_text(&self) -> String {
        self.rendered()
            .segments
            .iter()
            .filter_map(|s| match s {
                Segment::Clean(t) => Some(t.as_str()),
                Segment::Conflict(_) => None,
            })
            .collect()
    }

    /// The draft text the ergonomic edit path diffs against (mirrors the clean
    /// content; the panel's text box binds this).
    pub fn draft_text(&self) -> &str {
        &self.draft_text
    }

    /// Set the draft text (the panel's edit box feeds keystrokes here; commit with
    /// [`Self::commit_draft`]).
    pub fn set_draft_text(&mut self, text: impl Into<String>) {
        self.draft_text = text.into();
    }

    /// Whether the document currently carries an unresolved conflict.
    pub fn has_conflict(&self) -> bool {
        self.rendered().has_conflict()
    }

    /// **APPEND content as a cap-gated turn.** The ergonomic edit: insert `text`
    /// after the document's current tail atom, committing the resulting `Add`
    /// patch through the REAL executor (a cap-gated turn leaving a receipt).
    /// Returns the outcome (committed receipt or in-band refusal).
    pub fn append(&mut self, text: &str, author: DocAuthor) -> EditOutcome {
        let after = self.tail_atom();
        let (_id, op) = Patch::add(seed_for(text, after), text, after);
        self.commit_edit(Patch::by(author.author(), [op]), author)
    }

    /// **COMMIT THE DRAFT as a cap-gated turn.** Diff the committed clean text
    /// against [`Self::draft_text`] and commit the difference as an append (the
    /// minimal authoring path). For the demo surface this appends the new tail
    /// (the `Doc::edit` token-diff lives in `dregg_doc::Doc`; here we drive the
    /// executor path, which is the cap-gated one).
    pub fn commit_draft(&mut self, author: DocAuthor) -> EditOutcome {
        let clean = self.clean_text();
        let draft = self.draft_text.clone();
        if let Some(added) = draft.strip_prefix(&clean) {
            if added.is_empty() {
                return EditOutcome::Refused {
                    reason: "draft equals committed text".into(),
                    unauthorized: false,
                };
            }
            self.append(added, author)
        } else {
            // A non-append rewrite: append the whole draft as a fresh tail (the
            // coarse demo path; the full LCS rewrite is `dregg_doc::Doc::edit`).
            self.append(&draft, author)
        }
    }

    /// **DEMONSTRATE THE PER-REGION CAP GATE.** Attempt the same append on the
    /// UNAUTHORIZED editor (the one whose editor cell lacks the region cap). The
    /// executor's cross-cell cap gate REFUSES it in-band with `CapabilityNotHeld`
    /// (a `Result` error, never a panic) — the document untouched. Returns the
    /// refusal outcome.
    pub fn attempt_unauthorized(&mut self, text: &str, author: DocAuthor) -> EditOutcome {
        let after = AtomId::ROOT; // a fresh unauthorized doc starts at ROOT
        let (_id, op) = Patch::add(seed_for(text, after), text, after);
        match self.unauthorized.edit(Patch::by(author.author(), [op])) {
            Ok(_) => EditOutcome::Committed {
                receipt_hash: [0u8; 32],
                pre_state: [0u8; 32],
                post_state: [0u8; 32],
                actions: 0,
                finalized: true,
            },
            Err(e) => refusal(e),
        }
    }

    /// **SOW A FIRST-CLASS PROSE CONFLICT.** Two co-authors (`ALICE`, `BOB`)
    /// concurrently insert a different continuation *after the same tail atom* —
    /// both committed as real cap-gated turns. Because neither orders the other,
    /// the resulting graph has a genuine antichain: the document is HONESTLY
    /// conflicted at that fork (and clean everywhere else). Not an error — a state.
    pub fn sow_prose_conflict(&mut self, alt_a: &str, alt_b: &str) -> (EditOutcome, EditOutcome) {
        let fork = self.tail_atom();
        let (_ida, op_a) = Patch::add(seed_for(alt_a, fork), alt_a, fork);
        let (_idb, op_b) = Patch::add(seed_for(alt_b, fork).wrapping_add(0x9E37), alt_b, fork);
        let a = self.commit_edit(
            Patch::by(DocAuthor::ALICE.author(), [op_a]),
            DocAuthor::ALICE,
        );
        let b = self.commit_edit(Patch::by(DocAuthor::BOB.author(), [op_b]), DocAuthor::BOB);
        (a, b)
    }

    /// **SOW A FIRST-CLASS FIELD CONFLICT** (the conservation/authority regime):
    /// two co-authors write a different value to one single-valued field (a
    /// canonical title). Both assignments survive as a `Regime::Field` clash a
    /// resolution must *choose* (it may need consensus). Both are real turns.
    pub fn sow_field_conflict(
        &mut self,
        field: &str,
        value_a: &str,
        value_b: &str,
    ) -> (EditOutcome, EditOutcome) {
        let a = self.commit_edit(
            Patch::by(
                DocAuthor::ALICE.author(),
                [Op::SetField {
                    name: field.to_string(),
                    value: value_a.to_string(),
                    superseding: false,
                }],
            ),
            DocAuthor::ALICE,
        );
        let b = self.commit_edit(
            Patch::by(
                DocAuthor::BOB.author(),
                [Op::SetField {
                    name: field.to_string(),
                    value: value_b.to_string(),
                    superseding: false,
                }],
            ),
            DocAuthor::BOB,
        );
        (a, b)
    }

    /// **RESOLVE a prose conflict by ORDERING** the alternatives (`heads[0]` before
    /// `heads[1]` ...). Commits the resolving `Connect` patch as a real cap-gated
    /// turn — collapsing the antichain to a single walk, every alternative kept.
    pub fn resolve_prose_order(&mut self, heads: &[AtomId], author: DocAuthor) -> EditOutcome {
        let patch = resolve_connect_by(author.author(), heads);
        self.commit_edit(patch, author)
    }

    /// **RESOLVE a prose conflict by CHOOSING** one alternative (`keep`) and
    /// tombstoning each dropped alternative WHOLE (head + its exclusively-owned
    /// tail, via the graph-aware `resolve_keep_in`). Commits the resolving patch as
    /// a real cap-gated turn — so a dropped multi-atom branch cannot leak its tail
    /// and re-form a fresh antichain.
    pub fn resolve_prose_keep(
        &mut self,
        keep: AtomId,
        drop: &[AtomId],
        author: DocAuthor,
    ) -> EditOutcome {
        let patch = resolve_keep_in(self.doc.graph(), author.author(), keep, drop);
        self.commit_edit(patch, author)
    }

    /// **RESOLVE a field conflict** by choosing a single canonical value (a
    /// superseding `SetField`). Commits as a real cap-gated turn; the chosen
    /// `author` is recorded as the settling authority.
    pub fn resolve_field_choose(
        &mut self,
        field: &str,
        value: &str,
        author: DocAuthor,
    ) -> EditOutcome {
        let patch = resolve_field(author.author(), field, value);
        self.commit_edit(patch, author)
    }

    /// All current conflicts, each with its alternatives attributed to who wrote
    /// them (provenance resolved to the committed receipt when one exists).
    pub fn conflicts(&self) -> Vec<ConflictView> {
        self.rendered()
            .conflicts()
            .map(|c| self.attribute(c))
            .collect()
    }

    /// **THE INLINE CONFLICT-VIEW WITH ONE-CLICK RESOLUTIONS.** For every open
    /// conflict, the attributed alternatives (who wrote which) PLUS the set of
    /// ready resolution gestures a reader can click — keep one, order all, or
    /// settle a field. This is the editing UX the literate surface lacked: a
    /// conflict renders as both alternatives inline, each gesture a single patch.
    /// `resolver` authors any chosen resolution (its receipt is under that author).
    pub fn conflict_views(&self, resolver: DocAuthor) -> Vec<InlineConflict> {
        let rendered = self.rendered();
        let menu: Vec<RegionResolutions> =
            resolutions(self.doc.graph(), &rendered, resolver.author());
        rendered
            .conflicts()
            .zip(menu)
            .map(|(region, region_res)| InlineConflict {
                view: self.attribute(region),
                choices: region_res.choices,
            })
            .collect()
    }

    /// **COMMIT A CHOSEN RESOLUTION** as a cap-gated turn. Takes the ready
    /// [`ResolutionChoice::patch`] (from [`Self::conflict_views`]) and runs it
    /// through the real executor, collapsing the conflict and leaving a receipt.
    /// An unauthorized resolver is refused in-band (the same anti-ghost tooth).
    pub fn resolve_choice(
        &mut self,
        choice: &ResolutionChoice,
        resolver: DocAuthor,
    ) -> EditOutcome {
        self.commit_edit(choice.patch.clone(), resolver)
    }

    // ── hypermedia faces (the built Nelson/Engelbart pieces, reused) ──────────

    /// THE TRANSCLUSION face: a verified cross-cell quote — the document quotes
    /// another cell's value (content-addressed + receipt + quorum). Reuses the
    /// existing `web_cells::WebCellsBrowser` (the Nelson piece is already here): it
    /// publishes the live world's cells as `dregg://` pages and resolves a genuine
    /// `TranscludedField` quote, which we surface on the document. `None` when the
    /// web has too few cells to compose a quote.
    pub fn transclusion(
        &self,
        world: &World,
        viewer: CellId,
        rights: dregg_cell::AuthRequired,
    ) -> Option<crate::web_cells::Transclusion> {
        crate::web_cells::WebCellsBrowser::build(world, viewer, rights, None).transclusion
    }

    /// THE BACKLINKS face: "what links here", Ted Nelson's two-way link read
    /// backward — the witness-graph projected through the viewer's membrane. Built
    /// from the live world via the existing `links_here::LinksHerePanel` (already
    /// here; this surfaces it on the document).
    pub fn backlinks(
        &self,
        world: &World,
        focus: CellId,
        rights: dregg_cell::AuthRequired,
        depth: usize,
    ) -> crate::links_here::LinksHerePanel {
        crate::links_here::LinksHerePanel::build(world, focus, rights, depth)
    }

    // ── internals ─────────────────────────────────────────────────────────────

    /// Commit a patch through the real executor, recording the per-author receipt
    /// for conflict attribution and mirroring the draft text on success.
    fn commit_edit(&mut self, patch: Patch, author: DocAuthor) -> EditOutcome {
        match self.doc.edit(patch) {
            Ok(receipt) => {
                let rh = receipt.receipt_hash();
                self.receipt_by_author.insert(author.id, rh);
                self.draft_text = self.clean_text();
                EditOutcome::Committed {
                    receipt_hash: rh,
                    pre_state: receipt.pre_state_hash,
                    post_state: receipt.post_state_hash,
                    actions: receipt.action_count,
                    finalized: receipt.finality == dregg_turn::Finality::Final,
                }
            }
            Err(e) => refusal(e),
        }
    }

    /// The current tail atom — the last alive atom in document order (the anchor a
    /// fresh append is ordered after). `ROOT` for an empty document.
    fn tail_atom(&self) -> AtomId {
        walk_atoms(self.doc.graph())
            .last()
            .map(|(id, _)| *id)
            .unwrap_or(AtomId::ROOT)
    }

    /// Attribute a conflict region's alternatives to who wrote them, resolving the
    /// committed receipt when one exists for that author.
    fn attribute(&self, c: &ConflictRegion) -> ConflictView {
        let alternatives = c
            .alternatives
            .iter()
            .map(|alt: &Alternative| {
                let author = alt.provenance.author;
                AttributedAlternative {
                    text: alt.text.clone(),
                    author_name: DocAuthor::name_of(author),
                    head: alt.head,
                    receipt_hash: self.receipt_by_author.get(&author.0).copied(),
                }
            })
            .collect();
        ConflictView {
            regime: c.regime,
            field: c.field.clone(),
            needs_consensus: c.regime.needs_consensus(),
            alternatives,
        }
    }
}

impl Default for DocEditor {
    fn default() -> Self {
        Self::new()
    }
}

/// Map a `TurnError` to a refusal outcome (the in-band anti-ghost tooth).
fn refusal(e: TurnError) -> EditOutcome {
    let unauthorized = matches!(e, TurnError::CapabilityNotHeld { .. });
    let reason = match &e {
        TurnError::CapabilityNotHeld { .. } => {
            "CapabilityNotHeld — the editor lacks the per-region edit cap".to_string()
        }
        TurnError::EmptyForest => "no change to commit".to_string(),
        other => format!("{other:?}"),
    };
    EditOutcome::Refused {
        reason,
        unauthorized,
    }
}

/// A deterministic atom seed from the content + anchor (so repeated content at
/// distinct anchors gets distinct atom ids — the `dregg_doc::Doc` stable-id rule).
fn seed_for(content: &str, after: AtomId) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    content.hash(&mut h);
    after.0.hash(&mut h);
    h.finish()
}

/// Short hex of a 32-byte hash for the panel banners.
fn hex8(h: &[u8; 32]) -> String {
    let mut s = String::with_capacity(16);
    for b in &h[..8] {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_edit_commits_as_a_cap_gated_turn() {
        let mut ed = DocEditor::new();
        let pre = ed.commitment();
        let out = ed.append("hello world. ", DocAuthor::ALICE);
        assert!(
            out.committed(),
            "the authorized edit committed: {}",
            out.banner()
        );
        if let EditOutcome::Committed {
            finalized,
            post_state,
            ..
        } = out
        {
            assert!(finalized, "driving the real executor finalizes the receipt");
            assert_ne!(post_state, pre, "the edit moved the commitment");
        }
        assert!(
            ed.commitment_matches(),
            "the seam is closed: commitment == projection"
        );
        assert!(ed.clean_text().contains("hello world."));
    }

    #[test]
    fn an_unauthorized_region_edit_is_refused_in_band() {
        let mut ed = DocEditor::new();
        let out = ed.attempt_unauthorized("forbidden ", DocAuthor::BOB);
        assert!(
            out.unauthorized(),
            "refused by the per-region cap gate: {}",
            out.banner()
        );
        match out {
            EditOutcome::Refused {
                unauthorized,
                reason,
            } => {
                assert!(unauthorized);
                assert!(reason.contains("CapabilityNotHeld"), "{reason}");
            }
            other => panic!("expected refusal, got {other:?}"),
        }
    }

    #[test]
    fn a_prose_conflict_renders_both_alternatives_with_provenance() {
        let mut ed = DocEditor::new();
        let (a, b) = ed.sow_prose_conflict("Cats are best. ", "Dogs are best. ");
        assert!(
            a.committed() && b.committed(),
            "both alternatives committed"
        );
        assert!(
            ed.has_conflict(),
            "the document is living in a conflict state"
        );

        let conflicts = ed.conflicts();
        assert_eq!(conflicts.len(), 1, "exactly one conflict region");
        let c = &conflicts[0];
        assert_eq!(c.regime, Regime::Prose);
        assert_eq!(c.alternatives.len(), 2, "BOTH alternatives are rendered");

        // Each alternative is attributed to WHO WROTE IT (a fact) + a real receipt.
        let names: Vec<&str> = c.alternatives.iter().map(|a| a.author_name).collect();
        assert!(
            names.contains(&"alice") && names.contains(&"bob"),
            "{names:?}"
        );
        for alt in &c.alternatives {
            assert!(
                alt.receipt_hash.is_some(),
                "each alternative carries its witnessing receipt (provenance IS the receipt)"
            );
        }

        // The clean prefix is still usable WHILE the conflict stands.
        assert!(
            ed.clean_text().contains("patch"),
            "the rest of the doc is clean + usable"
        );
    }

    #[test]
    fn resolving_a_prose_conflict_by_keeping_collapses_it() {
        let mut ed = DocEditor::new();
        ed.sow_prose_conflict("Cats. ", "Dogs. ");
        assert!(ed.has_conflict());

        let c = ed.conflicts().remove(0);
        let heads: Vec<AtomId> = c.alternatives.iter().map(|a| a.head).collect();
        // Keep the first alternative, drop the rest — a real cap-gated resolving turn.
        let keep = heads[0];
        let drop: Vec<AtomId> = heads[1..].to_vec();
        let out = ed.resolve_prose_keep(keep, &drop, DocAuthor::ALICE);
        assert!(
            out.committed(),
            "the resolution committed as a turn: {}",
            out.banner()
        );
        assert!(
            !ed.has_conflict(),
            "the conflict collapsed to a single walk"
        );
        assert!(ed.commitment_matches());
    }

    #[test]
    fn resolving_a_prose_conflict_by_ordering_collapses_it() {
        let mut ed = DocEditor::new();
        ed.sow_prose_conflict("First. ", "Second. ");
        let c = ed.conflicts().remove(0);
        let heads: Vec<AtomId> = c.alternatives.iter().map(|a| a.head).collect();
        let out = ed.resolve_prose_order(&heads, DocAuthor::ALICE);
        assert!(out.committed(), "{}", out.banner());
        assert!(
            !ed.has_conflict(),
            "ordering collapsed the antichain (both kept)"
        );
    }

    #[test]
    fn a_field_conflict_is_the_conservation_regime_and_resolves_by_choosing() {
        let mut ed = DocEditor::new();
        let (a, b) = ed.sow_field_conflict("title", "Cats", "Dogs");
        assert!(a.committed() && b.committed());
        let conflicts = ed.conflicts();
        let field = conflicts
            .iter()
            .find(|c| c.regime == Regime::Field)
            .expect("a field clash");
        assert_eq!(field.field.as_deref(), Some("title"));
        assert!(
            field.needs_consensus,
            "a field authority/conservation clash may need consensus"
        );
        assert_eq!(field.alternatives.len(), 2, "both clashing values survive");

        let out = ed.resolve_field_choose("title", "Cats", DocAuthor::ALICE);
        assert!(out.committed(), "{}", out.banner());
        assert!(
            ed.conflicts().iter().all(|c| c.regime != Regime::Field),
            "the field clash collapsed to the chosen value"
        );
    }

    #[test]
    fn the_inline_conflict_view_offers_clickable_resolutions_that_collapse_it() {
        // A sown prose conflict surfaces inline as BOTH alternatives + one-click
        // resolutions; committing any choice through the executor collapses it.
        let mut ed = DocEditor::new();
        ed.sow_prose_conflict("Cats. ", "Dogs. ");
        assert!(ed.has_conflict());

        let inline = ed.conflict_views(DocAuthor::ALICE);
        assert_eq!(inline.len(), 1, "one inline conflict");
        let c = &inline[0];
        // both alternatives shown, attributed.
        assert_eq!(c.view.alternatives.len(), 2);
        let names: Vec<&str> = c.view.alternatives.iter().map(|a| a.author_name).collect();
        assert!(
            names.contains(&"alice") && names.contains(&"bob"),
            "{names:?}"
        );
        // a keep-each + order menu is offered, and a keep-all default exists.
        assert!(!c.choices.is_empty(), "resolution choices offered");
        assert!(
            c.keep_all_choice().is_some(),
            "a keep-both default is armed"
        );

        // pick the keep-all (order) choice and commit it as a real cap-gated turn.
        let choice = c.keep_all_choice().unwrap().clone();
        let out = ed.resolve_choice(&choice, DocAuthor::ALICE);
        assert!(
            out.committed(),
            "the one-click resolution committed: {}",
            out.banner()
        );
        assert!(!ed.has_conflict(), "the conflict collapsed");
        assert!(ed.commitment_matches());
    }

    #[test]
    fn an_inline_field_conflict_settles_by_clicking_a_value() {
        let mut ed = DocEditor::new();
        ed.sow_field_conflict("title", "On Cats", "On Dogs");
        let inline = ed.conflict_views(DocAuthor::ALICE);
        let field = inline
            .iter()
            .find(|c| c.view.regime == Regime::Field)
            .expect("a field conflict inline");
        // one choose per distinct value.
        assert!(
            field.choices.len() >= 2,
            "a choose per value: {:?}",
            field.choices.len()
        );
        let choice = field.choices[0].clone();
        let out = ed.resolve_choice(&choice, DocAuthor::ALICE);
        assert!(out.committed(), "{}", out.banner());
        assert!(
            ed.conflicts().iter().all(|c| c.regime != Regime::Field),
            "the field clash settled"
        );
    }

    #[test]
    fn a_clean_document_has_no_inline_conflicts() {
        let ed = DocEditor::new();
        assert!(!ed.has_conflict());
        assert!(
            ed.conflict_views(DocAuthor::ALICE).is_empty(),
            "nothing to resolve"
        );
    }

    #[test]
    fn the_document_is_a_real_cell() {
        let ed = DocEditor::new();
        // The region cell and editor cell are distinct real substrate identities.
        assert_ne!(ed.region_id(), ed.editor_id());
        assert!(
            ed.commitment_matches(),
            "commitment == projection from genesis"
        );
    }
}
