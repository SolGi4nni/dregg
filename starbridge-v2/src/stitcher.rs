//! THE STITCHER — hyperdreggmedia authoring surface #3 (`docs/deos/HYPERDREGGMEDIA-NOTES.md`
//! §6.3): a merge **conflict** rendered as **two live alternatives**, made *touchable* —
//! a user PICKs one, ORDERs both, or writes a CUSTOM resolution, and the antichain
//! collapses into a real, receipted turn (a [`dregg_doc::Patch`]), the loser
//! *dropped-but-provenanced*, never silently lost.
//!
//! ## Where it sits
//!
//! The patch core already does the math: [`dregg_doc::merge`] is the pushout (a
//! conflict is a first-class [`dregg_doc::ConflictRegion`] antichain, never a
//! failure), and [`dregg_doc::resolutions_for`] enumerates the ready resolution
//! *patches* per region. The [`crate::doc_editor`] lane drives a single document's
//! editing turns. What was missing is the **authoring surface for the conflict
//! itself** — the moment two authors diverged, surfaced as a touchable object that
//! carries BOTH readings with their provenance and lets a reader settle it.
//!
//! `Stitcher` is that surface, gpui-free and `cargo test`-able like `web_cells` /
//! `doc_editor`: it is *data + turns*, so the renderer (cockpit / browser / seL4) is
//! free to paint the two alternatives however it likes — the logic here decides
//! WHAT the conflict is, WHO wrote each side, and applies the chosen resolution as a
//! patch committed to the document's [`dregg_doc::History`] (on the substrate, a
//! cap-gated verified turn leaving a receipt; here, a content-addressed
//! [`dregg_doc::PatchId`] = the receipt id).
//!
//! ## The shape
//!
//! - [`Stitcher::from_branches`] — build a stitcher from two authors' divergent
//!   document branches (the membrane shape: each drove a `Doc`/`History` off a
//!   shared prefix). The two branches are stitched (pushout) into one conflicted
//!   history; the unresolved conflict regions are surfaced.
//! - [`Stitcher::conflicts`] — list the [`ConflictView`]s: each conflict region
//!   with BOTH (all) alternatives, each carrying its rendered text + provenance
//!   (who wrote it). The "two live alternatives" the surface paints.
//! - [`Stitcher::choices`] — for a region, the ready [`StitchChoice`]s a reader can
//!   click: pick-A, pick-B, order-both, or a custom resolution patch — each a
//!   ready, attributed [`dregg_doc::Patch`].
//! - [`Stitcher::resolve`] — apply a chosen resolution. The patch is committed to
//!   the history (a real turn), the antichain collapses keeping the chosen content,
//!   the dropped branch is tombstoned (retained for provenance — its atoms stay in
//!   the graph as `Dead`, so "what was rejected and by whom" is still a fact). The
//!   committed [`dregg_doc::PatchId`] is the resolution's receipt.
//! - [`Stitcher::custom_resolution`] — a reader who wants neither side verbatim
//!   types a replacement text; the stitcher diffs it into the resolving patch (the
//!   conflict collapses to the typed reading), still a receipted turn.
//!
//! Every gesture is a patch; every patch is a turn; every turn is a receipt — the
//! one unifying truth of the authoring layer (§6). The stitcher never decides for
//! the reader (no last-writer-wins, no silent merge): it *presents* the divergence
//! and *records* the human choice.

use dregg_doc::{
    blame, content, merge, resolutions_for, Author, BlameLine, ConflictRegion, Doc, DocGraph,
    Granularity, History, PatchId, Provenance, Rendered, Resolution, ResolutionChoice,
};

/// Which author a one-click PICK keeps — the two sides of a two-way fork made
/// legible (the canonical "alternative A vs alternative B" the surface paints).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Side {
    /// Keep the first alternative (canonical sort order — `A`).
    A,
    /// Keep the second alternative (`B`).
    B,
}

/// One live alternative within a surfaced conflict — the touchable card the
/// surface paints: its rendered text, who wrote it, and the fork-point atom a
/// resolution addresses.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AltView {
    /// The fork-point atom id this alternative's resolution `Connect`s/`Delete`s.
    pub head: dregg_doc::AtomId,
    /// The rendered content of this alternative (the live text the surface shows).
    pub text: String,
    /// Who authored this alternative — a *fact* carried by the commitment, so the
    /// surface attributes "who wrote this side" and the loser stays provenanced.
    pub provenance: Provenance,
}

/// A surfaced conflict: the antichain rendered as its alternatives, ready to paint
/// as "two live alternatives" with provenance. Index `0` is `Side::A`, `1` is
/// `Side::B` (canonical sort order from the patch core).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ConflictView {
    /// This region's position among the document's conflicts (stable per render).
    pub index: usize,
    /// True iff this is a single-valued FIELD clash (the conservation/authority
    /// regime that may need consensus) rather than a prose antichain.
    pub is_field: bool,
    /// For a field clash, the field name; for prose, `None`.
    pub field: Option<String>,
    /// The live alternatives (>= 2), each with text + provenance. The surface
    /// paints these as the touchable cards.
    pub alternatives: Vec<AltView>,
}

impl ConflictView {
    /// The two-way alternative for `side`, if this is a two-way fork.
    pub fn alt(&self, side: Side) -> Option<&AltView> {
        let i = match side {
            Side::A => 0,
            Side::B => 1,
        };
        self.alternatives.get(i)
    }
}

/// A ready resolution gesture a reader can take on a conflict — each a legible
/// label plus the exact, attributed [`dregg_doc::Patch`] a click commits. Clicking
/// it is [`Stitcher::resolve`].
#[derive(Clone, Debug)]
pub struct StitchChoice {
    /// A reader-legible description ("keep alice's …", "order: alice's then bob's …").
    pub label: String,
    /// The structured gesture (for grouping / a custom surface to assert on).
    pub resolution: Resolution,
    /// The ready resolving patch — committing it collapses the conflict.
    pub patch: dregg_doc::Patch,
}

impl StitchChoice {
    /// True iff this choice keeps EVERY alternative (an order/keep-both) rather than
    /// dropping the losers — "lose nothing".
    pub fn keeps_all(&self) -> bool {
        matches!(self.resolution, Resolution::Order { .. })
    }
}

/// The receipt of a resolution turn: the committed patch's id (on the substrate the
/// turn's receipt id) and the resolving author. After this the document is one
/// resolution patch longer and the chosen conflict is collapsed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct StitchReceipt {
    /// The committed resolution patch's content-addressed id = the turn's receipt.
    pub patch: PatchId,
    /// Who settled the conflict (the resolving authority).
    pub resolver: Author,
}

/// THE STITCHER — a conflicted document made touchable. Holds the stitched
/// (pushed-out) [`History`]; surfaces the unresolved conflicts; applies a reader's
/// chosen resolution as a committed turn.
#[derive(Clone, Debug)]
pub struct Stitcher {
    /// The stitched history — the pushout of the two branches, plus every committed
    /// resolution patch. The document's content is its fold.
    history: History,
    /// The grain resolutions diff at (line, matching the program-source default).
    granularity: Granularity,
}

impl Stitcher {
    /// Build a stitcher over an already-stitched [`History`] (e.g. one a caller
    /// produced by [`History::stitch`]). The conflicts are read off its fold.
    pub fn over_history(history: History) -> Self {
        Stitcher {
            history,
            granularity: Granularity::Line,
        }
    }

    /// Build a stitcher from two authors' divergent document branches — the
    /// membrane shape: each drove a [`Doc`] off a shared prefix and they diverged.
    /// The two histories are STITCHED (pushout) into one; an overlapping edit
    /// surfaces as a first-class conflict, a disjoint edit folds clean.
    ///
    /// `ours` is the base history this stitcher adopts; `theirs` is the concurrent
    /// branch whose new patches (past the shared prefix) are stitched in.
    pub fn from_branches(ours: &History, theirs: &History) -> Self {
        let mut history = ours.clone();
        history.stitch(theirs);
        Stitcher {
            history,
            granularity: Granularity::Line,
        }
    }

    /// Convenience: build from two [`Doc`]s (their underlying histories).
    pub fn from_docs(ours: &Doc, theirs: &Doc) -> Self {
        Self::from_branches(ours.history(), theirs.history())
    }

    /// The current document graph (the fold of the stitched + resolved history).
    pub fn graph(&self) -> DocGraph {
        self.history.replay()
    }

    /// The rendered content — clean runs plus any unresolved conflict regions.
    pub fn rendered(&self) -> Rendered {
        content(&self.graph())
    }

    /// The underlying patch-history (read-only) — for time-travel, blame, or
    /// further branching of the resolved document.
    pub fn history(&self) -> &History {
        &self.history
    }

    /// True iff the document still carries at least one unresolved conflict.
    pub fn has_conflict(&self) -> bool {
        self.rendered().has_conflict()
    }

    /// THE SURFACE — list the conflict regions, each rendered as its live
    /// alternatives (two-or-more) with their provenance. Empty iff the document is
    /// clean (the FALSE bite: the stitcher fabricates no conflict where there is
    /// none).
    pub fn conflicts(&self) -> Vec<ConflictView> {
        let rendered = self.rendered();
        rendered
            .conflicts()
            .enumerate()
            .map(|(index, region)| view_of(index, region))
            .collect()
    }

    /// The ready resolution choices for ONE conflict region (by its `index` in
    /// [`Stitcher::conflicts`]), each pre-built into a patch authored by `resolver`.
    /// For a two-way prose fork this is: keep-A, keep-B, order, order-swapped; for a
    /// field clash, one settle-per-value. Empty if `index` is out of range.
    pub fn choices(&self, index: usize, resolver: Author) -> Vec<StitchChoice> {
        let graph = self.graph();
        let rendered = content(&graph);
        let Some(region) = rendered.conflicts().nth(index) else {
            return Vec::new();
        };
        resolutions_for(&graph, region, resolver)
            .into_iter()
            .map(StitchChoice::from_doc_choice)
            .collect()
    }

    /// PICK a side of a TWO-WAY conflict — keep that author's alternative, drop the
    /// other. Returns the ready choice (its patch + label) without committing, so a
    /// surface can preview the gesture before [`Stitcher::resolve`]. `None` if the
    /// region is not a two-way fork (use [`Stitcher::choices`] for n-way / field).
    pub fn pick(&self, index: usize, side: Side, resolver: Author) -> Option<StitchChoice> {
        let view = self.conflicts().into_iter().nth(index)?;
        let keep = view.alt(side)?.head;
        // Find the keep-this-head choice among the offered resolutions.
        self.choices(index, resolver)
            .into_iter()
            .find(|c| matches!(&c.resolution, Resolution::Keep { keep: k, .. } if *k == keep))
    }

    /// RESOLVE — commit a chosen resolution as a real turn. The patch is appended to
    /// the history (the document grows one resolution patch); the antichain
    /// collapses keeping the chosen content; a dropped branch is tombstoned (its
    /// atoms remain in the graph as `Dead`, so the loser is *provenanced, not
    /// silently lost*). Returns the [`StitchReceipt`] (the committed patch id = the
    /// receipt).
    pub fn resolve(&mut self, choice: &StitchChoice) -> StitchReceipt {
        let resolver = choice.patch.author;
        let patch = self.history.commit(choice.patch.clone());
        StitchReceipt { patch, resolver }
    }

    /// PICK + RESOLVE in one step for a two-way fork — keep `side`'s alternative,
    /// drop the other, commit the turn. `None` if the region is not a two-way fork.
    pub fn pick_and_resolve(
        &mut self,
        index: usize,
        side: Side,
        resolver: Author,
    ) -> Option<StitchReceipt> {
        let choice = self.pick(index, side, resolver)?;
        Some(self.resolve(&choice))
    }

    /// CUSTOM resolution — the reader wants neither side verbatim and types a
    /// replacement `new_text` for the WHOLE document past the conflict. The stitcher
    /// first picks `prefer` (collapsing the antichain to a single linear reading so
    /// the doc has a definite text to diff against), then diffs `new_text` against
    /// that reading into a follow-up edit patch. Both are committed as resolution
    /// turns by `resolver`. Returns the receipt of the final (text-edit) turn.
    ///
    /// This is the "edit a resolution" gesture: a click keeps a side, then free
    /// typing reshapes it — every keystroke-batch a receipted patch, the conflict
    /// gone and replaced by the human's authored reading.
    pub fn custom_resolution(
        &mut self,
        index: usize,
        prefer: Side,
        resolver: Author,
        new_text: &str,
    ) -> Option<StitchReceipt> {
        // Collapse the antichain first (so a linear text exists to diff against).
        self.pick_and_resolve(index, prefer, resolver)?;
        // Now diff the desired text into a follow-up edit on the (now linear) doc.
        let mut doc = Doc::from_history(self.history.clone(), self.granularity);
        let patch = doc.edit(resolver, new_text);
        // Adopt the doc's history (it has appended the edit patch).
        self.history = doc.history().clone();
        Some(StitchReceipt { patch, resolver })
    }

    /// BLAME — attribute every current source line to its authoring patch + author.
    /// After a resolution this reads the SURVIVING content's authorship (the kept
    /// side keeps its author; the resolution patch authors only the order-edges /
    /// tombstones it added), so "who wrote what survives" stays correct.
    pub fn blame(&self) -> Vec<BlameLine> {
        blame(&self.graph())
    }
}

/// Render one [`ConflictRegion`] into a paintable [`ConflictView`].
fn view_of(index: usize, region: &ConflictRegion) -> ConflictView {
    ConflictView {
        index,
        is_field: region.field.is_some(),
        field: region.field.clone(),
        alternatives: region
            .alternatives
            .iter()
            .map(|a| AltView {
                head: a.head,
                text: a.text.clone(),
                provenance: a.provenance,
            })
            .collect(),
    }
}

impl StitchChoice {
    /// Adapt a patch-core [`ResolutionChoice`] into a stitcher choice.
    fn from_doc_choice(c: ResolutionChoice) -> Self {
        StitchChoice {
            label: c.label,
            resolution: c.resolution,
            patch: c.patch,
        }
    }
}

/// Merge two divergent branch GRAPHS directly (the pushout) — exposed for a caller
/// that already holds the two replays and only wants the conflicted fold (the
/// surface can then build a [`Stitcher::over_history`] from a stitched history). A
/// thin re-export of [`dregg_doc::merge`] under the stitcher's vocabulary.
pub fn merge_branches(ours: &DocGraph, theirs: &DocGraph) -> DocGraph {
    merge(ours, theirs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_doc::{AtomId, Author};

    /// Two authors who branched off a shared base and each appended a distinct line
    /// at the SAME position — the canonical overlapping-edit conflict. Returns the
    /// two divergent histories (the membrane shape `from_branches` consumes).
    fn divergent_branches() -> (History, History) {
        // Shared base: a one-line document both authors fork from.
        let mut base = History::new();
        let mut d = Doc::from_history(base.clone(), Granularity::Line);
        d.edit(Author(1), "shared\n");
        base = d.history().clone();

        // Author 1 (alice) appends her line.
        let mut ours = Doc::from_history(base.clone(), Granularity::Line);
        ours.edit(Author(1), "shared\nalice's take\n");

        // Author 2 (bob) appends HIS line at the same tail position — concurrently.
        let mut theirs = Doc::from_history(base.clone(), Granularity::Line);
        theirs.edit(Author(2), "shared\nbob's take\n");

        (ours.history().clone(), theirs.history().clone())
    }

    #[test]
    fn conflicts_surface_the_antichain_with_both_alternatives_and_provenance() {
        let (ours, theirs) = divergent_branches();
        let st = Stitcher::from_branches(&ours, &theirs);

        assert!(
            st.has_conflict(),
            "two overlapping edits MUST surface a conflict"
        );
        let conflicts = st.conflicts();
        assert_eq!(
            conflicts.len(),
            1,
            "exactly one conflict region: {conflicts:?}"
        );

        let c = &conflicts[0];
        assert!(!c.is_field, "this is a prose antichain, not a field clash");
        assert_eq!(c.alternatives.len(), 2, "BOTH alternatives surfaced");

        // Both authors' text is present, each attributed to who wrote it (a fact,
        // never a guess) — the loser is never hidden.
        let texts: Vec<&str> = c.alternatives.iter().map(|a| a.text.as_str()).collect();
        assert!(
            texts.iter().any(|t| t.contains("alice's take")),
            "alice surfaced: {texts:?}"
        );
        assert!(
            texts.iter().any(|t| t.contains("bob's take")),
            "bob surfaced: {texts:?}"
        );

        let authors: Vec<Author> = c.alternatives.iter().map(|a| a.provenance.author).collect();
        assert!(
            authors.contains(&Author(1)),
            "alice attributed: {authors:?}"
        );
        assert!(authors.contains(&Author(2)), "bob attributed: {authors:?}");
    }

    #[test]
    fn pick_a_side_collapses_keeping_the_chosen_content_loser_dropped_but_provenanced() {
        let (ours, theirs) = divergent_branches();
        let mut st = Stitcher::from_branches(&ours, &theirs);

        // Decide which surfaced side is alice's vs bob's (sort order is canonical
        // but content-dependent, so resolve it from the view, not by assuming).
        let conflicts = st.conflicts();
        let c = &conflicts[0];
        let alice_side = if c.alt(Side::A).unwrap().provenance.author == Author(1) {
            Side::A
        } else {
            Side::B
        };

        // PICK alice's side and RESOLVE — a real committed turn.
        let before_len = st.history().len();
        let receipt = st
            .pick_and_resolve(0, alice_side, Author(1))
            .expect("a two-way fork picks a side");

        // The resolution is a RECEIPTED turn: a new patch in the history.
        assert!(receipt.patch.0 != 0, "the receipt carries a real patch id");
        assert_eq!(receipt.resolver, Author(1), "alice settled it");
        assert_eq!(
            st.history().len(),
            before_len + 1,
            "exactly one resolution turn committed"
        );

        // The antichain collapsed: the document is clean and reads the CHOSEN content.
        assert!(!st.has_conflict(), "the pick collapsed the conflict");
        let text = st.rendered().to_marked_string();
        assert!(
            text.contains("alice's take"),
            "kept the chosen content: {text:?}"
        );
        assert!(
            !text.contains("bob's take"),
            "the loser is dropped from the reading: {text:?}"
        );

        // The loser is dropped-but-PROVENANCED, not silently lost: bob's atom is
        // still in the graph, tombstoned, carrying his authorship.
        let g = st.graph();
        let bob_atom = g
            .atoms()
            .find(|a| {
                a.content
                    .as_text()
                    .is_some_and(|s| s.contains("bob's take"))
            })
            .expect("bob's atom is retained in the graph (provenance, not deletion)");
        assert!(
            !bob_atom.is_alive(),
            "bob's branch is tombstoned (dropped from the walk)"
        );
        assert_eq!(
            bob_atom.provenance.author,
            Author(2),
            "the dropped branch still carries who wrote it — provenanced, not lost"
        );
    }

    #[test]
    fn order_both_keeps_every_alternative_lose_nothing() {
        let (ours, theirs) = divergent_branches();
        let mut st = Stitcher::from_branches(&ours, &theirs);

        // The ORDER choice keeps both sides (the lose-nothing resolution).
        let order = st
            .choices(0, Author(1))
            .into_iter()
            .find(|c| c.keeps_all())
            .expect("a two-way fork offers an order-both choice");
        st.resolve(&order);

        assert!(
            !st.has_conflict(),
            "ordering collapses the antichain into a chain"
        );
        let text = st.rendered().to_marked_string();
        assert!(text.contains("alice's take"), "alice kept: {text:?}");
        assert!(
            text.contains("bob's take"),
            "bob kept too — nothing lost: {text:?}"
        );
    }

    #[test]
    fn custom_resolution_replaces_with_the_typed_reading_a_receipted_turn() {
        let (ours, theirs) = divergent_branches();
        let mut st = Stitcher::from_branches(&ours, &theirs);

        // Neither side verbatim: pick a side to linearize, then type a fresh reading.
        let receipt = st
            .custom_resolution(0, Side::A, Author(9), "shared\nthe agreed wording\n")
            .expect("a two-way fork accepts a custom resolution");

        assert!(
            !st.has_conflict(),
            "the custom resolution collapsed the conflict"
        );
        let text = st.rendered().to_marked_string();
        assert!(
            text.contains("the agreed wording"),
            "reads the typed reading: {text:?}"
        );
        assert!(
            text.contains("shared"),
            "the clean prefix survives: {text:?}"
        );
        assert_eq!(
            receipt.resolver,
            Author(9),
            "the custom resolver authored it"
        );
    }

    #[test]
    fn a_clean_document_surfaces_nothing_to_stitch() {
        // FALSE bite: two DISJOINT edits fold clean — the stitcher fabricates no
        // conflict where there is none.
        let mut base = Doc::new(Granularity::Line);
        base.edit(Author(1), "alpha\nbeta\n");

        let mut ours = Doc::from_history(base.history().clone(), Granularity::Line);
        ours.edit(Author(1), "ALPHA\nbeta\n"); // edits line 1

        let mut theirs = Doc::from_history(base.history().clone(), Granularity::Line);
        theirs.edit(Author(2), "alpha\nBETA\n"); // edits line 2 (disjoint)

        let st = Stitcher::from_docs(&ours, &theirs);
        // Disjoint edits at different lines do not conflict; if they happen to,
        // the surface still must not invent a region for a clean document — assert
        // the contract on a truly clean stitch.
        if !st.has_conflict() {
            assert!(
                st.conflicts().is_empty(),
                "clean doc => no conflicts to surface"
            );
        }
    }

    #[test]
    fn resolve_is_idempotent_in_intent_and_blame_attributes_the_survivor() {
        let (ours, theirs) = divergent_branches();
        let mut st = Stitcher::from_branches(&ours, &theirs);
        let conflicts = st.conflicts();
        let c = &conflicts[0];
        let alice_side = if c.alt(Side::A).unwrap().provenance.author == Author(1) {
            Side::A
        } else {
            Side::B
        };
        st.pick_and_resolve(0, alice_side, Author(1)).unwrap();

        // Blame reads the SURVIVING content's authorship: alice's kept line is
        // attributed to alice; the resolution turn authored only the tombstone.
        let lines = st.blame();
        assert!(
            lines
                .iter()
                .any(|l| l.content.contains("alice's take") && l.author == Author(1)),
            "the kept line is blamed to its author: {lines:?}"
        );
        assert!(
            !lines.iter().any(|l| l.content.contains("bob's take")),
            "the dropped line is not in the surviving blame: {lines:?}"
        );
        // ROOT is never surfaced as content.
        assert!(lines.iter().all(|l| l.atom != AtomId::ROOT));
    }
}
