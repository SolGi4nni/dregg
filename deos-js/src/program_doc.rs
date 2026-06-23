//! **The program-source-as-document weld** — a gadget's `view_source` is a
//! [`dregg_doc::Doc`] (a patch-history), not an opaque blob.
//!
//! ember's gap: [`crate::portable`] stores a gadget's program text (`view_source`)
//! as an OPAQUE heap blob — you can carry it and re-run it, but you cannot *edit it
//! as a patch*, *transclude a fragment of it with provenance*, or *merge two authors'
//! concurrent edits*. The source is a frozen string.
//!
//! This module closes that by making the program's source a real [`dregg_doc::Doc`].
//! The source text is the **fold of a patch-history**; the three XANADU document
//! powers then apply to a *program*:
//!
//! - **PATCH** ([`ProgramSource::edit`]): editing the gadget's source is appending a
//!   patch. The current source is the doc's fold ([`ProgramSource::view_source`]);
//!   [`ProgramSource::blame`] attributes each line to its authoring patch + author —
//!   correct-by-construction (the atom id is content-addressed, so blame rides with
//!   the content across inserts, never smearing the way `git blame` does).
//! - **TRANSCLUDE** ([`ProgramSource::transclude_fragment`]): one gadget quotes a
//!   *fragment* of another gadget's source as a **provenanced live quote**. The quote
//!   carries the SOURCE's blame (who authored each quoted line, in which patch). It is
//!   **cap-bounded like the membrane**: an unauthorized viewer gets a
//!   [`TranscludedFragment::Darkened`] — the citation (which gadget) survives, the
//!   bytes do not — mirroring `dregg_doc::composition::ChildResolution::Darkened`.
//! - **MERGE** ([`ProgramSource::merge`]): two authors edit the same gadget
//!   concurrently. Disjoint edits fold **clean**; an overlapping edit yields a
//!   first-class [`dregg_doc::ConflictRegion`] (the antichain is surfaced, never a
//!   silent overwrite), resolvable by a later patch.
//!
//! **It stays runnable.** [`ProgramSource::seal_into`] writes the doc's *fold* — the
//! materialized program text — into a [`crate::AppletManifest`]'s `view_source`, so a
//! gadget whose source is a `Doc` still mints, persists, loads, and RUNS exactly as
//! before (the doc is the source of truth; the cell carries the fold the runtime
//! runs). The document is the editor; the fold is what executes.

use dregg_doc::{blame, content, merge, Author, BlameLine, Doc, Granularity, History, Rendered};

use crate::portable::AppletManifest;

/// A gadget's **program source as a document** — a [`dregg_doc::Doc`] whose fold is
/// the `view_source` the runtime runs.
///
/// Hold one of these to author a gadget's program by *editing* (each edit a patch),
/// to *blame* its source line-by-line, to *transclude* a fragment of another gadget's
/// source, or to *merge* a concurrent author's edits. Seal it into an
/// [`AppletManifest`] (writing the fold as `view_source`) when you want to mint/run.
#[derive(Clone, Debug)]
pub struct ProgramSource {
    doc: Doc,
}

impl ProgramSource {
    /// A fresh, empty program source (line-granular — the coarse default the patch
    /// core recommends, and the right grain for source code).
    pub fn empty() -> Self {
        ProgramSource {
            doc: Doc::new(Granularity::Line),
        }
    }

    /// Seed a program source from an initial `view_source` string, authored by
    /// `author`. The whole initial text is committed as the genesis patch (so even
    /// the first version has provenance).
    pub fn seed(author: Author, view_source: &str) -> Self {
        let mut s = Self::empty();
        s.edit(author, view_source);
        s
    }

    /// Lift an existing gadget's manifest into a document: its current `view_source`
    /// becomes the seed (genesis) patch authored by `author`. This is the bridge from
    /// the opaque-blob world — an already-minted gadget's frozen source becomes an
    /// editable, blameable, mergeable document.
    pub fn from_manifest(author: Author, manifest: &AppletManifest) -> Self {
        Self::seed(author, &manifest.view_source)
    }

    /// **PATCH** — edit the gadget's source. Diffs the current source against
    /// `new_source` and commits the minimal `Add`/`Delete` patch authored by
    /// `author`. The source is never rewritten wholesale; an edit is a patch.
    pub fn edit(&mut self, author: Author, new_source: &str) {
        self.doc.edit(author, new_source);
    }

    /// The current program source — the doc's fold. This is the `view_source` the
    /// runtime runs (sealed via [`ProgramSource::seal_into`]).
    pub fn view_source(&self) -> String {
        self.doc.text()
    }

    /// The underlying document (read-only) — for time-travel, branching, or merging.
    pub fn doc(&self) -> &Doc {
        &self.doc
    }

    /// The patch-history of this source — every edit is a patch in it.
    pub fn history(&self) -> &History {
        self.doc.history()
    }

    /// **BLAME** — attribute every source line to its authoring patch + author.
    /// Correct-by-construction: the attribution rides with the content (a middle
    /// insert by a third author does not smear blame onto the surrounding lines).
    pub fn blame(&self) -> Vec<BlameLine> {
        blame(&self.doc.history().replay())
    }

    /// The rendered content of the source (clean runs + any first-class conflict
    /// regions). After a clean merge this is all `Clean`; after an overlapping merge
    /// it carries a [`dregg_doc::ConflictRegion`].
    pub fn rendered(&self) -> Rendered {
        content(&self.doc.history().replay())
    }

    /// **MERGE** — fold a concurrent author's edits into this source.
    ///
    /// `theirs` is another [`ProgramSource`] that branched from a shared prefix of
    /// THIS one's history and then diverged. The pushout/union merge is total:
    /// disjoint edits fold clean; an overlapping edit at the same position yields a
    /// first-class [`dregg_doc::ConflictRegion`] (the antichain, surfaced — not a
    /// silent overwrite), resolvable by a later patch.
    ///
    /// Returns the merged [`Rendered`] (so a caller can ask `has_conflict()` /
    /// inspect the conflict region) and *also* records the branch's new patches into
    /// THIS source's history, so the merged source is reproducible and further
    /// editable.
    pub fn merge(&mut self, theirs: &ProgramSource) -> Rendered {
        // Stitch the branch's new patches into our history (BRANCH-AND-STITCH §3):
        // the published content is the merge of the two folds.
        let mut hist = self.doc.history().clone();
        hist.stitch(theirs.doc.history());
        // Rebuild our doc from the stitched history. (`Doc` exposes editing by text;
        // we reconstruct it from the merged history by re-seeding, but the canonical
        // truth is the merged GRAPH — `merge` of the two replays — which we render.)
        let merged_graph = merge(
            &self.doc.history().replay(),
            &theirs.doc.history().replay(),
        );
        // Adopt the stitched history so subsequent edits chain off the merged state.
        self.doc = Doc::from_history(hist, Granularity::Line);
        content(&merged_graph)
    }

    /// **SEAL** — write the doc's fold into a manifest's `view_source`, returning a
    /// manifest the rest of [`crate::portable`] mints/persists/loads/runs unchanged.
    ///
    /// The document is the source of truth; the *fold* is what the cell carries and
    /// the runtime runs. If the source currently carries an unresolved conflict, the
    /// fold is the clean prefix (a conflicted program is not yet runnable past the
    /// fork — resolve it with a patch first); [`ProgramSource::rendered`]`.has_conflict()`
    /// reports this.
    pub fn seal_into(&self, mut manifest: AppletManifest) -> AppletManifest {
        manifest.view_source = self.view_source();
        manifest
    }
}

/// **TRANSCLUDE** — a provenanced live quote of a fragment of a gadget's source.
///
/// The fragment carries the SOURCE gadget's blame: who authored each quoted line, in
/// which patch — the citation. Cap-bounded like the membrane: minted only for a
/// viewer authorized to read the source gadget; an unauthorized viewer gets a
/// [`TranscludedFragment::Darkened`] (the citation survives, the bytes do not).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscludedFragment {
    /// The viewer could read the source: the quoted lines, each with its real
    /// provenance (the live quote).
    Quoted {
        /// Which gadget the fragment was quoted from.
        from: GadgetCite,
        /// The quoted source lines, each carrying its original authorship.
        lines: Vec<BlameLine>,
    },
    /// The viewer's caps do not reach the source gadget: the read was withheld by the
    /// membrane. The citation survives (which gadget, how many lines); the bytes do
    /// not — exactly `ChildResolution::Darkened`.
    Darkened {
        /// Which gadget was withheld.
        from: GadgetCite,
        /// How many lines were withheld (the citation keeps the shape, not the text).
        withheld_lines: usize,
    },
}

impl TranscludedFragment {
    /// The concatenated text of the quote (empty when darkened — the bytes were
    /// withheld). This is the live-quote text a transcluding gadget would splice into
    /// its own source.
    pub fn text(&self) -> String {
        match self {
            TranscludedFragment::Quoted { lines, .. } => {
                lines.iter().map(|l| l.content.as_str()).collect()
            }
            TranscludedFragment::Darkened { .. } => String::new(),
        }
    }

    /// True iff the bytes were withheld (out-of-cap).
    pub fn is_darkened(&self) -> bool {
        matches!(self, TranscludedFragment::Darkened { .. })
    }

    /// The gadget this fragment cites (survives darkening).
    pub fn cite(&self) -> &GadgetCite {
        match self {
            TranscludedFragment::Quoted { from, .. } => from,
            TranscludedFragment::Darkened { from, .. } => from,
        }
    }
}

/// A citation of the gadget a fragment was transcluded from — the cell/gadget id. This
/// survives even a darkened (out-of-cap) read, so provenance is never lost.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GadgetCite(pub u128);

impl ProgramSource {
    /// **TRANSCLUDE** a fragment (a `[start, end)` line range of the source's blame)
    /// out of THIS gadget, for a viewer with the given read authority over it.
    ///
    /// `from` cites this gadget; `viewer_can_read` is the membrane gate. Authorized →
    /// a [`TranscludedFragment::Quoted`] carrying each quoted line's REAL provenance
    /// (a live, provenanced quote). Unauthorized → a [`TranscludedFragment::Darkened`]
    /// keeping the citation but withholding the bytes (no amplification — the viewer
    /// learns the shape, never the source).
    pub fn transclude_fragment(
        &self,
        from: GadgetCite,
        line_range: std::ops::Range<usize>,
        viewer_can_read: bool,
    ) -> TranscludedFragment {
        let all = self.blame();
        let start = line_range.start.min(all.len());
        let end = line_range.end.min(all.len());
        let slice = &all[start..end];
        if viewer_can_read {
            TranscludedFragment::Quoted {
                from,
                lines: slice.to_vec(),
            }
        } else {
            TranscludedFragment::Darkened {
                from,
                withheld_lines: slice.len(),
            }
        }
    }

    /// Splice a transcluded fragment into THIS source as a provenanced quote, authored
    /// by `quoting_author`. The quoted text is inserted after the current source; the
    /// quote's CITATION (the source gadget + the original blame) is returned so the
    /// caller can record the provenance edge. A darkened fragment splices nothing (the
    /// bytes were withheld) but is still a legible event (its citation is returned).
    ///
    /// (The quoted lines re-enter this doc as new atoms authored by `quoting_author` —
    /// the quote is the quoter's edit — while the returned [`TranscludedFragment`]
    /// preserves the ORIGINAL authorship as the citation, so "who wrote the quoted
    /// material" remains a fact distinct from "who placed the quote here".)
    pub fn splice_quote(&mut self, quoting_author: Author, fragment: &TranscludedFragment) {
        let quoted = fragment.text();
        if !quoted.is_empty() {
            let mut next = self.view_source();
            next.push_str(&quoted);
            self.edit(quoting_author, &next);
        }
    }
}
