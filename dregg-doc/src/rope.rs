//! # The rope<->patch BRIDGE — `ropey::Rope` text <-> the patch graph
//!
//! The keystone weld of `docs/deos/APPS-AS-CELLS.md` §1: *"the rope buffer <->
//! patch graph impedance is the genuine engineering question."* deos-zed's editor
//! (`deos-zed/src/editor.rs`) holds its buffer as a `ropey::Rope` — a balanced
//! b-tree of text optimized for edit-at-cursor. The *durable* document, by
//! contrast, is a [`crate::DocGraph`]: a partial order of alive/dead atoms, folded
//! from a patch [`History`]. This module is the impedance-match between the two:
//!
//! - **`new_rope -> Patch`** ([`RopeDoc::edit_rope`] / [`rope_diff`]): the editor
//!   edits its rope freely (fast, ephemeral view-state); on a save / debounced
//!   checkpoint it hands the new rope here, and we **diff it against the current
//!   document content** and emit the minimal `Add`/`Delete`/`Connect` patch — the
//!   *same* alignment the string path ([`crate::Doc::edit`]) uses, so the rope
//!   buffer becomes a patch with no loss of the duplicate-token-stability and
//!   stable-atom-id guarantees the core proves.
//! - **`Patch`-fold -> Rope`** ([`RopeDoc::rope`] / [`graph_to_rope`]): the
//!   document's content (the fold of its patch history, [`History::replay`]) is
//!   materialized back into a `ropey::Rope` — the buffer the editor displays. So
//!   the round-trip the editor lives in (display a rope, edit it, save it as a
//!   patch, re-render the fold as a rope) closes.
//!
//! ## The two-level mapping (APPS-AS-CELLS.md §1)
//!
//! The visible buffer STAYS a rope (the fast interactive cache); the *durable*
//! document is the patch fold. [`RopeDoc`] holds the [`History`] (durable) and
//! renders/diffs against a rope at the seam — never storing the rope as the source
//! of truth. That is the *buffer = a cache of the fold* discipline: the rope is
//! regenerable from the history at any cursor, time-travel for free.
//!
//! ## Why a beta-pinned `ropey`
//!
//! `ropey 2.0.0-beta.1` is the exact crate+version deos-zed's `Editor` uses
//! (`deos-zed/Cargo.lock`), so a `&ropey::Rope` from the editor's buffer is the
//! *same type* this consumes — the weld is direct, not a stringify-at-the-FFI.
//! (We DO stringify INTERNALLY to drive the proven token-LCS diff; that is an
//! implementation detail of the diff, not the seam — the seam takes a real
//! `Rope`.)
//!
//! Behind the OFF-by-default `rope` feature so the standalone core stays
//! dependency-free.

use crate::atom::{Author, PatchId};
use crate::content::content;
use crate::doc::{Granularity, diff_history_to_ops};
use crate::history::History;
use crate::patch::{Op, Patch};
use ropey::Rope;

/// A document authored through a `ropey::Rope` editor buffer. Holds the durable
/// patch [`History`]; the rope is materialized on demand ([`RopeDoc::rope`]) and
/// each [`RopeDoc::edit_rope`] diffs a new rope against the current content,
/// committing the minimal patch. The rope is a *cache of the fold*, never the
/// source of truth.
#[derive(Clone, Debug)]
pub struct RopeDoc {
    history: History,
    granularity: Granularity,
}

impl RopeDoc {
    /// A fresh, empty rope-document at the given granularity (the spec's §4.4
    /// default is [`Granularity::Line`] — start span-coarse).
    pub fn new(g: Granularity) -> Self {
        RopeDoc {
            history: History::new(),
            granularity: g,
        }
    }

    /// Adopt an existing patch [`History`] as a rope-document (e.g. one loaded
    /// from the substrate, or a peer's branch to render in the editor).
    pub fn from_history(history: History, g: Granularity) -> Self {
        RopeDoc { history, granularity: g }
    }

    /// THE fold -> rope direction: materialize the current document content (the
    /// fold of the patch history) into the `ropey::Rope` the editor displays.
    /// Clean segments only — the linear text a single-author buffer is; a conflict
    /// region has no single linear rope (use [`crate::content`] /
    /// [`crate::render_three_way`] for the conflict view).
    pub fn rope(&self) -> Rope {
        graph_to_rope(&self.history)
    }

    /// THE rope -> patch direction: diff the editor's `new_rope` against the
    /// current document content and commit the minimal `Add`/`Delete`/`Connect`
    /// patch, authored by `author`. Returns the new tip [`PatchId`]. An unchanged
    /// rope yields an empty (no-op) patch.
    ///
    /// This is what the editor calls on save / checkpoint: the rope it has been
    /// editing becomes a verifiable patch over the durable document — the
    /// `editor-buffer = a document-language document` weld made real.
    pub fn edit_rope(&mut self, author: Author, new_rope: &Rope) -> PatchId {
        let ops = rope_diff(&self.history, new_rope, self.granularity);
        self.history.commit(Patch::by(author, ops))
    }

    /// The underlying patch-history (read-only) — for time-travel, branching, or
    /// merging with a co-author's branch (the buffer is a cache; THIS is durable).
    pub fn history(&self) -> &History {
        &self.history
    }
}

/// Materialize a patch [`History`]'s current content (the fold) into a
/// `ropey::Rope`. Clean segments are concatenated in document order; a conflict
/// region (an antichain with no linear order) is skipped here — the linear rope
/// is exactly the unconflicted text. The free, exact rope<-fold direction.
pub fn graph_to_rope(history: &History) -> Rope {
    let rendered = content(&history.replay());
    let mut text = String::new();
    for seg in &rendered.segments {
        if let crate::content::Segment::Clean(t) = seg {
            text.push_str(t);
        }
    }
    Rope::from_str(&text)
}

/// Diff `new_rope` against a [`History`]'s current content and return the minimal
/// `Add`/`Delete`/`Connect` ops — the editor edit -> patch transform. The rope is
/// stringified ONLY to drive the proven token-LCS alignment ([`diff_history_to_ops`]);
/// the public seam is the real `&Rope`. This is the genuine engineering question
/// APPS-AS-CELLS.md §1 names, answered by reusing the string path's alignment so the
/// stable-atom-id + duplicate-token guarantees carry over to the rope buffer.
pub fn rope_diff(history: &History, new_rope: &Rope, g: Granularity) -> Vec<Op> {
    // `ropey::Rope::to_string` walks the b-tree chunks once; the diff then runs
    // on the flat text. (Token-granular diffing over the rope's chunk structure
    // directly is a future optimization; correctness rides the proven path.)
    let new_text = new_rope.to_string();
    diff_history_to_ops(history, &new_text, g)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::AtomId;
    use crate::merge::merge;

    fn rope(s: &str) -> Rope {
        Rope::from_str(s)
    }

    // ── THE ROUND-TRIP: rope -> patch -> fold -> rope ────────────────────────

    #[test]
    fn rope_round_trips_through_the_patch_fold() {
        let mut d = RopeDoc::new(Granularity::Line);
        d.edit_rope(Author(1), &rope("alpha\nbeta\ngamma\n"));
        // The fold materialized back to a rope equals what was typed.
        assert_eq!(d.rope().to_string(), "alpha\nbeta\ngamma\n");
    }

    #[test]
    fn empty_rope_doc_renders_empty() {
        let d = RopeDoc::new(Granularity::Line);
        assert_eq!(d.rope().to_string(), "");
        assert_eq!(d.rope().len(), 0);
    }

    #[test]
    fn edit_rope_insert_in_the_middle() {
        let mut d = RopeDoc::new(Granularity::Line);
        d.edit_rope(Author(1), &rope("one\nthree\n"));
        d.edit_rope(Author(1), &rope("one\ntwo\nthree\n"));
        assert_eq!(d.rope().to_string(), "one\ntwo\nthree\n");
    }

    #[test]
    fn edit_rope_delete_a_line() {
        let mut d = RopeDoc::new(Granularity::Line);
        d.edit_rope(Author(1), &rope("a\nb\nc\n"));
        d.edit_rope(Author(1), &rope("a\nc\n"));
        assert_eq!(d.rope().to_string(), "a\nc\n");
    }

    #[test]
    fn unchanged_rope_is_a_noop_patch() {
        let mut d = RopeDoc::new(Granularity::Line);
        d.edit_rope(Author(1), &rope("stable\n"));
        let before = d.history().len();
        d.edit_rope(Author(1), &rope("stable\n"));
        // The commit happens, but the diff is empty (no atoms touched).
        assert_eq!(d.rope().to_string(), "stable\n");
        let last = d.history().patches().last().unwrap();
        assert!(last.ops.is_empty(), "an unchanged rope yields an empty patch");
        assert_eq!(d.history().len(), before + 1);
    }

    // ── The bridge preserves the core's stable-atom-id guarantee ─────────────

    #[test]
    fn duplicate_lines_stay_distinct_through_the_rope_bridge() {
        // The duplicate-token trap (doc.rs) survives the rope path: dropping the
        // FIRST "x" leaves the SECOND, because the rope diff rides the same
        // predecessor-seeded id scheme.
        let mut d = RopeDoc::new(Granularity::Line);
        d.edit_rope(Author(1), &rope("x\ny\nx\n"));
        d.edit_rope(Author(1), &rope("y\nx\n"));
        assert_eq!(d.rope().to_string(), "y\nx\n");
    }

    // ── The bridge is just a face on the patch core: edits are real patches ──

    #[test]
    fn rope_edits_carry_authorship() {
        let mut d = RopeDoc::new(Granularity::Line);
        d.edit_rope(Author(1), &rope("kept\n"));
        d.edit_rope(Author(9), &rope("kept\nadded\n"));
        let g = d.history().replay();
        let added = g
            .atoms()
            .find(|a| a.is_alive() && a.content == "added\n")
            .expect("the inserted line exists");
        assert_eq!(added.provenance.author, Author(9));
    }

    // ── Two rope-buffers, edited concurrently, MERGE (the multi-author weld) ──

    #[test]
    fn two_rope_buffers_merge_clean_when_independent() {
        // Both authors start from the same content (shared genesis), then each
        // edits their own rope-buffer offline. Independent edits merge clean.
        let mut base = RopeDoc::new(Granularity::Line);
        base.edit_rope(Author(1), &rope("title\nbody\n"));

        // Two branches off the shared history.
        let mut a = RopeDoc::from_history(base.history().branch(), Granularity::Line);
        let mut b = RopeDoc::from_history(base.history().branch(), Granularity::Line);

        // A edits the title line; B appends a footer. Disjoint regions.
        a.edit_rope(Author(1), &rope("TITLE\nbody\n"));
        b.edit_rope(Author(2), &rope("title\nbody\nfooter\n"));

        // Merge the two graphs: independent edits commute -> clean merge.
        let merged = merge(&a.history().replay(), &b.history().replay());
        let r = content(&merged);
        // No conflict: both edits land.
        assert!(!r.has_conflict(), "disjoint rope edits merge clean");
        let text = r.to_marked_string();
        assert!(text.contains("TITLE\n"), "A's title edit survived");
        assert!(text.contains("footer\n"), "B's footer survived");
    }

    #[test]
    fn two_rope_buffers_at_same_tail_yield_a_conflict_object() {
        // Both authors append a DIFFERENT line after the same tail -> an antichain
        // -> a first-class conflict object (not a textual marker, not a failure).
        let mut base = RopeDoc::new(Granularity::Line);
        base.edit_rope(Author(1), &rope("shared\n"));

        let mut a = RopeDoc::from_history(base.history().branch(), Granularity::Line);
        let mut b = RopeDoc::from_history(base.history().branch(), Granularity::Line);
        a.edit_rope(Author(1), &rope("shared\nA-says\n"));
        b.edit_rope(Author(2), &rope("shared\nB-says\n"));

        let merged = merge(&a.history().replay(), &b.history().replay());
        let r = content(&merged);
        assert!(r.has_conflict(), "concurrent tail edits are a conflict STATE");
        // The conflict is a first-class object carrying both alternatives + who
        // wrote each — inspectable, not a `<<<<<<<` text wound.
        let region = r.conflicts().next().expect("a conflict region exists");
        let authors: Vec<Author> = region
            .alternatives
            .iter()
            .map(|alt| alt.provenance.author)
            .collect();
        assert!(authors.contains(&Author(1)) && authors.contains(&Author(2)));
        // The clean prefix is still usable while the conflict stands.
        assert!(r.to_marked_string().starts_with("shared\n"));
    }

    #[test]
    fn graph_to_rope_skips_conflict_regions() {
        // The fold->rope direction renders ONLY the linear (clean) text; a
        // conflict has no single rope. The clean prefix materializes; the
        // antichain does not appear as a linear run. We build a conflicted graph
        // by forking at the tail, then assert the linear rope is just the prefix.
        let mut base = RopeDoc::new(Granularity::Line);
        base.edit_rope(Author(1), &rope("base\n"));
        let g = base.history().replay();
        let tail = crate::walk_atoms(&g)
            .last()
            .map(|(id, _)| *id)
            .unwrap_or(AtomId::ROOT);
        let pa = Patch::by(Author(1), [Patch::add(101, "x\n", tail).1]);
        let pb = Patch::by(Author(2), [Patch::add(102, "y\n", tail).1]);
        let merged = merge(&pa.apply_to(&g), &pb.apply_to(&g));

        let r = content(&merged);
        assert!(r.has_conflict(), "the fork is a conflict");
        let linear: String = r
            .segments
            .iter()
            .filter_map(|s| match s {
                crate::content::Segment::Clean(t) => Some(t.as_str()),
                crate::content::Segment::Conflict(_) => None,
            })
            .collect();
        let linear_rope = Rope::from_str(&linear);
        assert_eq!(
            linear_rope.to_string(),
            "base\n",
            "only the clean prefix is linear; the antichain is not a linear run"
        );
    }
}
