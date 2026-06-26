//! The literate surface — a markup that parses to PATCHES, where a conflict is a
//! first-class part of the SYNTAX (not a wound carved into the text by a tool).
//!
//! [`crate::Doc`] is the *prose-only* ergonomic path: it diffs flat text into an
//! `Add`/`Delete` patch. This module lifts that to a small **literate markup**
//! that also carries the two things a real dreggverse document needs in its
//! surface and that flat text cannot express:
//!
//! 1. **Fields** (the non-monotone fragment, §2.4) — a leading frontmatter fence
//!    of `key: value` lines. Each field is a single-valued [`Op::SetField`];
//!    concurrent assignments to one field are the [`Regime::Field`] clash the
//!    classifier flags as *real*.
//! 2. **Conflicts as first-class syntax** (§2.3) — a [`ConflictRegion`] renders
//!    to a block the surface UNDERSTANDS, and that block PARSES BACK to the same
//!    region. Unlike Git's `<<<<<<<`/`>>>>>>>` markers (text the tools don't
//!    understand, *outside* the model), here the conflict block is a legible,
//!    round-tripping projection of a genuine antichain / field clash, each
//!    alternative tagged with **who wrote it** (a substrate fact, never a guess).
//!
//! ## The grammar (informal)
//!
//! ```text
//! ---                      ┐  frontmatter fence (optional). Between the fences,
//! title: The Cat           │  each `key: value` line is one single-valued field.
//! author: ember            │  A field appearing >=2 times (a clash) renders as a
//! ---                      ┘  field conflict block (see below).
//!
//! The first line of prose.   ┐ body. Each non-fence line is one line-atom
//! The second line.           ┘ (Granularity::Line). Blank lines are atoms too.
//!
//! <<< prose                ┐  a CONFLICT block: a prose antichain. `regime` after
//! || @1: one way           │  `<<<` is the regime label; each `|| @author: text`
//! || @2: another way       │  line is one live alternative with its author.
//! >>>                      ┘  Resolved later by an ordering/choosing patch.
//!
//! <<< field(title)         ┐  a CONFLICT block over a single-valued field: same
//! || @1: The Cat           │  shape, `field(name)` names the clashing field. A
//! || @2: The Dog           │  resolution is a superseding SetField.
//! >>>                      ┘
//! ```
//!
//! ## What this module is, precisely
//!
//! - [`parse`] : `&str -> Parsed` — splits a literate source into `(fields,
//!   body_lines, conflict blocks)`. PURE syntax; no graph yet.
//! - [`LiterateDoc`] : the authoring object. [`LiterateDoc::edit`] takes the new
//!   full literate source, diffs it (prose via the same token-LCS [`crate::Doc`]
//!   rides; fields via a key/value diff) and commits ONE [`Patch`]. The prose
//!   round-trips byte-exactly; a field write is a genuine non-monotone
//!   [`Op::SetField`].
//! - [`render`] : `&Rendered -> String` — the inverse: a folded document
//!   (clean runs + [`Segment::Conflict`] regions + field clashes) back to
//!   literate markup. [`render`] ∘ fold is the surface a reader sees.
//!
//! ## The two load-bearing both-polarity facts (tested)
//!
//! - **Round-trip (the TRUE bite).** A clean literate source `parse`d into a
//!   fresh [`LiterateDoc`] and `render`ed back yields the same source. Authoring
//!   text is faithful.
//! - **Conflict-as-state (the FALSE bite).** Two authors who concurrently edit
//!   the same region (prose) or set the same field (field) `merge` to a document
//!   whose `render` contains a `<<< … >>>` conflict block with BOTH alternatives
//!   and their authors — and that block `parse`s back to the same region. A
//!   conflict is a first-class, legible, round-tripping STATE, never a failure.

use crate::atom::Author;
use crate::content::{Alternative, ConflictRegion, Rendered, Segment, content};
use crate::doc::{Doc, Granularity};
use crate::graph::DocGraph;
use crate::history::History;
use crate::patch::{Op, Patch};
use crate::regime::Regime;

/// The fence line that opens/closes the frontmatter field block.
const FENCE: &str = "---";
/// The conflict-block open marker (followed by the regime descriptor).
const CONFLICT_OPEN: &str = "<<<";
/// The conflict-block close marker.
const CONFLICT_CLOSE: &str = ">>>";
/// The per-alternative line prefix inside a conflict block.
const ALT_PREFIX: &str = "|| @";

/// One authored alternative as it appears in parsed literate source: the author
/// label and the alternative's text (everything after `|| @<author>: `).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParsedAlternative {
    /// The author label parsed from `@<n>`.
    pub author: Author,
    /// The alternative's text.
    pub text: String,
}

/// A conflict block parsed from literate source: its regime, the optional field
/// name (for a field clash), and the live alternatives in source order.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParsedConflict {
    /// `Prose` or `Field` (from the `<<<` descriptor).
    pub regime: Regime,
    /// For a field clash, the field name; for a prose antichain, `None`.
    pub field: Option<String>,
    /// The alternatives, each with its author.
    pub alternatives: Vec<ParsedAlternative>,
}

/// A single field assignment parsed from the frontmatter fence.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParsedField {
    /// The field name (left of the first `:`).
    pub name: String,
    /// The field value (right of the first `:`, trimmed of one leading space).
    pub value: String,
}

/// The pure-syntax decomposition of a literate source.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Parsed {
    /// Frontmatter fields, in source order.
    pub fields: Vec<ParsedField>,
    /// The body prose as flat text (the conflict blocks REMOVED — they are not
    /// authorable prose, they are surfaced state). This is exactly the text the
    /// prose diff rides, so a clean document round-trips.
    pub prose: String,
    /// Any conflict blocks the source carried, in source order. On a freshly
    /// authored document this is empty; it is non-empty only when the source is a
    /// re-`render`ed conflicted document.
    pub conflicts: Vec<ParsedConflict>,
}

/// Parse a literate source into its `(fields, prose, conflicts)` decomposition.
///
/// This is PURE syntax — it builds no graph and commits no patch. The frontmatter
/// fence (a leading `---` … `---`) yields the [`ParsedField`]s; conflict blocks
/// (`<<< … >>>`) are lifted out into [`ParsedConflict`]s; everything else is body
/// prose (joined back with `'\n'`, byte-faithful to the body the author typed).
pub fn parse(source: &str) -> Parsed {
    let mut out = Parsed::default();

    // Split into physical lines, each KEEPING its trailing `'\n'` (so the body is
    // reassembled byte-faithfully — the `Line` granularity the prose diff rides
    // carries the newline on its atom). The final line has no `'\n'` iff the
    // source did not end in one.
    let lines = split_keep_newlines(source);
    let mut i = 0;

    // Frontmatter: only if the VERY FIRST line is the fence.
    if lines
        .first()
        .map(|l| l.trim_end() == FENCE)
        .unwrap_or(false)
    {
        i += 1; // consume the opening fence
        while i < lines.len() {
            let line = &lines[i];
            i += 1;
            if line.trim_end() == FENCE {
                break; // closing fence
            }
            if let Some((name, value)) = split_field(line.trim_end()) {
                out.fields.push(ParsedField { name, value });
            }
        }
    }

    // Body: prose runs (kept verbatim with their newlines) and conflict blocks
    // (excised into `conflicts`, contributing no prose).
    let mut prose = String::new();
    while i < lines.len() {
        let line = &lines[i];
        if let Some(rest) = line.trim_end().strip_prefix(CONFLICT_OPEN) {
            i += 1; // consume the `<<<` line
            let (regime, field) = parse_conflict_descriptor(rest.trim());
            let mut alternatives = Vec::new();
            while i < lines.len() {
                let inner = lines[i].trim_end();
                i += 1;
                if inner == CONFLICT_CLOSE {
                    break;
                }
                if let Some(alt) = parse_alternative(inner) {
                    alternatives.push(alt);
                }
            }
            out.conflicts.push(ParsedConflict {
                regime,
                field,
                alternatives,
            });
        } else {
            prose.push_str(line); // verbatim, including its trailing newline
            i += 1;
        }
    }
    out.prose = prose;
    out
}

/// Split `text` into physical lines, each KEEPING its trailing `'\n'` (the final
/// line carries none iff the text does not end in `'\n'`). The byte-faithful line
/// split the body reassembly rides — mirrors the `Line`-granularity tokenizer the
/// prose diff uses, so `parse` ∘ `render` and the prose round-trip are exact.
fn split_keep_newlines(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for ch in text.chars() {
        cur.push(ch);
        if ch == '\n' {
            out.push(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

/// Split a frontmatter `key: value` line. Returns `None` for a line with no
/// colon (treated as not-a-field — the fence body is forgiving).
fn split_field(line: &str) -> Option<(String, String)> {
    let (k, v) = line.split_once(':')?;
    let name = k.trim().to_string();
    if name.is_empty() {
        return None;
    }
    // Strip exactly one leading space after the colon (the canonical
    // `key: value` spacing) so `render` ∘ `parse` is the identity.
    let value = v.strip_prefix(' ').unwrap_or(v).to_string();
    Some((name, value))
}

/// Parse the descriptor after `<<<`: either `prose` or `field(<name>)`.
fn parse_conflict_descriptor(desc: &str) -> (Regime, Option<String>) {
    if let Some(rest) = desc.strip_prefix("field") {
        let name = rest
            .trim()
            .strip_prefix('(')
            .and_then(|r| r.strip_suffix(')'))
            .map(|s| s.to_string());
        (Regime::Field, name)
    } else {
        (Regime::Prose, None)
    }
}

/// Parse a `|| @<author>: <text>` alternative line.
fn parse_alternative(line: &str) -> Option<ParsedAlternative> {
    let rest = line.strip_prefix(ALT_PREFIX)?;
    let (author_str, text) = rest.split_once(':')?;
    let author = author_str.trim().parse::<u64>().ok()?;
    let text = text.strip_prefix(' ').unwrap_or(text).to_string();
    Some(ParsedAlternative {
        author: Author(author),
        text,
    })
}

/// A document authored in the literate surface.
///
/// Holds a prose [`Doc`] (the line-granular patch-history the prose diff rides)
/// plus the current field assignments, so an [`LiterateDoc::edit`] can diff BOTH
/// the prose and the fields against the new full source and commit one [`Patch`].
#[derive(Clone, Debug)]
pub struct LiterateDoc {
    prose: Doc,
    /// The last-committed field assignments, in author order, so a field diff can
    /// tell a fresh assignment from an unchanged one.
    fields: Vec<ParsedField>,
}

impl Default for LiterateDoc {
    fn default() -> Self {
        Self::new()
    }
}

impl LiterateDoc {
    /// A fresh, empty literate document (line-granular prose, no fields).
    pub fn new() -> Self {
        LiterateDoc {
            prose: Doc::new(Granularity::Line),
            fields: Vec::new(),
        }
    }

    /// The prose patch-history (read-only) — for time-travel, branching, merging
    /// with another author's branch (the same `History` the algebra operates on).
    pub fn history(&self) -> &History {
        self.prose.history()
    }

    /// The committed field assignments.
    pub fn fields(&self) -> &[ParsedField] {
        &self.fields
    }

    /// The current literate source: the inverse of [`parse`] applied to the
    /// folded document. Clean prose renders as prose; conflicts render as blocks;
    /// fields render as the frontmatter fence. Round-trips with [`LiterateDoc::edit`].
    pub fn source(&self) -> String {
        let rendered = content(&self.prose.history().replay());
        render_with_fields(&self.fields, &rendered)
    }

    /// THE literate edit: diff the current source into `new_source` and commit one
    /// [`Patch`] authored by `author`. The prose delta becomes `Add`/`Delete`
    /// ops; each NEW or CHANGED field becomes a non-monotone [`Op::SetField`].
    /// Returns the committed [`Patch`] (so a caller can route it to the substrate
    /// — `ExecutorDrivenDoc::edit` — or merge it).
    ///
    /// Conflict blocks in `new_source` are IGNORED for authoring (they are
    /// surfaced state, not authorable input); the author resolves a conflict with
    /// an explicit ordering/choosing edit, not by hand-editing the markers.
    pub fn edit(&mut self, author: Author, new_source: &str) -> Patch {
        let parsed = parse(new_source);

        // Prose: ride the existing token-LCS diff (byte-faithful round-trip).
        // `Doc::edit` commits the prose patch to its own history and returns the
        // tip id; recover that patch's ops (the prose delta) to fold into the
        // combined description this edit returns.
        let prose_pid = self.prose.edit(author, &parsed.prose);
        let mut ops: Vec<Op> = self
            .prose
            .history()
            .patches()
            .iter()
            .rev()
            .find(|p| p.id() == prose_pid)
            .map(|p| p.ops.clone())
            .unwrap_or_default();

        // Fields: a new field name, or a changed value for an existing one, is a
        // fresh single-valued assignment. (Concurrent assignments across BRANCHES
        // are what clash; sequential re-assignment by the same author supersedes.)
        for f in &parsed.fields {
            let prior = self.fields.iter().find(|p| p.name == f.name);
            let changed = prior.map(|p| p.value != f.value).unwrap_or(true);
            if changed {
                ops.push(Op::SetField {
                    name: f.name.clone(),
                    value: f.value.clone(),
                    // Sequential same-author re-assignment supersedes its own
                    // prior value (no self-clash); the concurrent cross-branch
                    // case is non-superseding and clashes (the §2.4 boundary).
                    superseding: prior.is_some(),
                });
            }
        }
        self.fields = parsed.fields;

        Patch::by(author, ops)
    }
}

/// Render a folded document (clean runs + conflicts) plus its field assignments
/// back to literate source: the inverse of [`parse`]. The frontmatter fence comes
/// first (if any field is set), then the body (prose runs and conflict blocks in
/// document order).
pub fn render_with_fields(fields: &[ParsedField], rendered: &Rendered) -> String {
    let mut out = String::new();

    // Frontmatter fence (only if there are fields).
    if !fields.is_empty() {
        out.push_str(FENCE);
        out.push('\n');
        for f in fields {
            out.push_str(&f.name);
            out.push_str(": ");
            out.push_str(&f.value);
            out.push('\n');
        }
        out.push_str(FENCE);
        out.push('\n');
    }

    out.push_str(&render(rendered));
    out
}

/// Render a folded document's segments to literate body markup: clean runs as
/// their content, [`Segment::Conflict`] regions as `<<< … >>>` blocks. This is
/// the surface a reader sees — a conflict is LEGIBLE, both alternatives shown
/// with their author, and it PARSES BACK (`parse` ∘ `render` recovers the region).
pub fn render(rendered: &Rendered) -> String {
    let mut out = String::new();
    for seg in &rendered.segments {
        match seg {
            Segment::Clean(s) => out.push_str(s),
            Segment::Conflict(c) => {
                // A conflict block is recognized by `parse` only when its `<<<`
                // begins a physical line. If preceding clean content did not end
                // in a newline, break the line first so the block stands alone.
                if !out.is_empty() && !out.ends_with('\n') {
                    out.push('\n');
                }
                render_conflict(c, &mut out);
            }
        }
    }
    out
}

/// Render one conflict region as a `<<< … >>>` block.
fn render_conflict(c: &ConflictRegion, out: &mut String) {
    out.push_str(CONFLICT_OPEN);
    out.push(' ');
    match (&c.regime, &c.field) {
        (Regime::Field, Some(name)) => {
            out.push_str("field(");
            out.push_str(name);
            out.push(')');
        }
        _ => out.push_str(c.regime.label()),
    }
    out.push('\n');
    for alt in &c.alternatives {
        out.push_str(ALT_PREFIX);
        out.push_str(&alt.provenance.author.0.to_string());
        out.push_str(": ");
        // The block grammar is one alternative per line; a prose alternative's
        // text is a line-atom carrying its own trailing newline, so normalize it
        // away (the block's own `'\n'` is the line terminator). `parsed_shape`
        // strips the same, so folded and reparsed regions compare exactly equal.
        out.push_str(alt.text.strip_suffix('\n').unwrap_or(&alt.text));
        out.push('\n');
    }
    out.push_str(CONFLICT_CLOSE);
    out.push('\n');
}

/// Reconstruct the conflict regions a literate source carries, WITHOUT a graph —
/// the pure-syntax inverse of [`render`]'s conflict blocks. Used to prove the
/// conflict-as-state round-trip: `parse(render(rendered)).conflicts` recovers the
/// same regions (regime, field, alternatives + authors) the fold surfaced.
pub fn parsed_conflicts_of(source: &str) -> Vec<ParsedConflict> {
    parse(source).conflicts
}

/// Lift a [`ConflictRegion`] to its pure-syntax [`ParsedConflict`] shape, for
/// comparing a folded region against a parsed one (the round-trip assertion).
pub fn parsed_shape(c: &ConflictRegion) -> ParsedConflict {
    ParsedConflict {
        regime: c.regime,
        field: c.field.clone(),
        alternatives: c
            .alternatives
            .iter()
            .map(|a: &Alternative| ParsedAlternative {
                author: a.provenance.author,
                // Strip the line-atom's trailing newline to match the block
                // grammar's one-line-per-alternative normalization (see
                // `render_conflict`), so a folded region and its `render` ∘ `parse`
                // round-trip compare exactly equal.
                text: a.text.strip_suffix('\n').unwrap_or(&a.text).to_string(),
            })
            .collect(),
    }
}

/// Author a fresh document graph from a literate source by Author `author`: parse
/// the source and apply ONE patch onto an empty graph. The seam helper the
/// merge-conflict test rides (two authors author from the same base, then merge).
pub fn author_graph(author: Author, source: &str) -> DocGraph {
    let mut doc = LiterateDoc::new();
    let patch = doc.edit(author, source);
    patch.apply_to(&DocGraph::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::merge::merge;

    // ── PARSE: pure syntax ───────────────────────────────────────────────────

    #[test]
    fn parse_splits_frontmatter_prose_and_conflicts() {
        let src = "\
---
title: The Cat
author: ember
---
First line.
Second line.";
        let p = parse(src);
        assert_eq!(p.fields.len(), 2);
        assert_eq!(
            p.fields[0],
            ParsedField {
                name: "title".into(),
                value: "The Cat".into()
            }
        );
        assert_eq!(
            p.fields[1],
            ParsedField {
                name: "author".into(),
                value: "ember".into()
            }
        );
        assert_eq!(p.prose, "First line.\nSecond line.");
        assert!(p.conflicts.is_empty());
    }

    #[test]
    fn parse_with_no_frontmatter_is_all_prose() {
        let p = parse("just prose\nno fence");
        assert!(p.fields.is_empty());
        assert_eq!(p.prose, "just prose\nno fence");
    }

    // ── ROUND-TRIP: the TRUE bite ────────────────────────────────────────────

    #[test]
    fn clean_source_round_trips_through_author_and_render() {
        // parse -> author one patch -> render recovers the source. The prose is
        // byte-faithful and the fields render back into the frontmatter fence.
        let src = "\
---
title: The Cat
---
The cat sat.
The cat ran.
";
        let mut doc = LiterateDoc::new();
        doc.edit(Author(1), src);
        assert_eq!(doc.source(), src, "a clean literate source round-trips");
    }

    #[test]
    fn prose_only_source_round_trips() {
        let src = "one\ntwo\nthree\n";
        let mut doc = LiterateDoc::new();
        doc.edit(Author(1), src);
        assert_eq!(doc.source(), src);
    }

    #[test]
    fn fields_only_source_round_trips() {
        let src = "---\ntitle: T\nauthor: a\n---\n";
        let mut doc = LiterateDoc::new();
        doc.edit(Author(1), src);
        assert_eq!(doc.source(), src);
    }

    #[test]
    fn sequential_field_reassignment_supersedes_not_clashes() {
        // The same author re-setting a field supersedes (no self-clash); the
        // document stays clean and renders the latest value.
        let mut doc = LiterateDoc::new();
        doc.edit(Author(1), "---\ntitle: A\n---\nbody\n");
        doc.edit(Author(1), "---\ntitle: B\n---\nbody\n");
        let rendered = content(&doc.history().replay());
        assert!(!rendered.has_conflict(), "sequential reassignment is clean");
        assert_eq!(doc.fields()[0].value, "B");
    }

    // ── CONFLICT-AS-STATE: the FALSE bite ────────────────────────────────────

    #[test]
    fn concurrent_prose_edits_render_a_first_class_conflict_block_that_parses_back() {
        // Two authors append concurrently at the same tail => a prose antichain.
        // The merged document RENDERS a `<<< prose ... >>>` block with BOTH
        // alternatives and their authors, and that block PARSES BACK to the same
        // region. A conflict is a legible, round-tripping STATE.
        let mut base_doc = LiterateDoc::new();
        base_doc.edit(Author(0), "shared\n");
        let base = base_doc.history().replay();

        // Author 1 and Author 2 each append a distinct line after the shared one.
        let a = {
            let mut d = LiterateDoc {
                prose: clone_doc(&base_doc),
                fields: vec![],
            };
            d.edit(Author(1), "shared\nalpha\n");
            d.history().replay()
        };
        let b = {
            let mut d = LiterateDoc {
                prose: clone_doc(&base_doc),
                fields: vec![],
            };
            d.edit(Author(2), "shared\nbeta\n");
            d.history().replay()
        };
        // Sanity: both forked from the same base.
        assert_eq!(content(&base).to_marked_string(), "shared\n");

        let merged = merge(&a, &b);
        let rendered = content(&merged);
        assert!(
            rendered.has_conflict(),
            "concurrent tail edits => a conflict"
        );

        let src = render(&rendered);
        assert!(
            src.contains("<<< prose"),
            "renders a prose conflict block:\n{src}"
        );
        assert!(
            src.contains("|| @1: alpha"),
            "alternative A with its author:\n{src}"
        );
        assert!(
            src.contains("|| @2: beta"),
            "alternative B with its author:\n{src}"
        );

        // The block PARSES BACK to the same region (regime + both authored alts).
        let reparsed = parsed_conflicts_of(&src);
        assert_eq!(reparsed.len(), 1, "one conflict region round-trips");
        let folded: Vec<ParsedConflict> = rendered.conflicts().map(parsed_shape).collect();
        assert_eq!(
            reparsed, folded,
            "render then parse recovers the conflict region"
        );
    }

    #[test]
    fn concurrent_field_clash_renders_a_field_conflict_block_that_parses_back() {
        // Two authors set the SAME single-valued field to different values on
        // concurrent branches => the non-monotone (Regime::Field) clash. It
        // renders a `<<< field(title) ... >>>` block with both authored values,
        // and parses back.
        let a = author_graph(Author(1), "---\ntitle: The Cat\n---\nbody\n");
        let b = author_graph(Author(2), "---\ntitle: The Dog\n---\nbody\n");
        let merged = merge(&a, &b);
        let rendered = content(&merged);

        let field_conflicts: Vec<_> = rendered.field_conflicts().collect();
        assert_eq!(field_conflicts.len(), 1, "the title field clashes");
        assert_eq!(field_conflicts[0].regime, Regime::Field);
        assert!(
            field_conflicts[0].regime.needs_consensus(),
            "a field clash is REAL"
        );

        let src = render(&rendered);
        assert!(
            src.contains("<<< field(title)"),
            "renders a field conflict block:\n{src}"
        );
        assert!(
            src.contains("The Cat") && src.contains("The Dog"),
            "both values:\n{src}"
        );

        let reparsed = parsed_conflicts_of(&src);
        let folded: Vec<ParsedConflict> = rendered.conflicts().map(parsed_shape).collect();
        assert_eq!(reparsed, folded, "the field conflict block round-trips");
    }

    #[test]
    fn a_conflict_block_in_authored_source_is_not_re_authored_as_prose() {
        // Feeding rendered conflict markup BACK as an edit must NOT inject the
        // markers as literal prose lines (they are surfaced state, not input).
        let src = "before\n<<< prose\n|| @1: x\n|| @2: y\n>>>\nafter\n";
        let p = parse(src);
        assert_eq!(
            p.prose, "before\nafter\n",
            "the conflict block is lifted out of prose"
        );
        assert_eq!(p.conflicts.len(), 1);
        let mut doc = LiterateDoc::new();
        doc.edit(Author(1), src);
        // The authored prose is just the clean lines; no `<<<` leaked in.
        assert!(
            !doc.source().contains("|| @1: x"),
            "markers did not become prose atoms"
        );
    }

    // tiny helper: clone the inner prose Doc (it is Clone) for a fork.
    fn clone_doc(d: &LiterateDoc) -> Doc {
        d.prose.clone()
    }
}
