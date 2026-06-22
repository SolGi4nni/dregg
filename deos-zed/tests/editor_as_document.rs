//! Editor-buffer-as-document + the multi-author merge, headless.
//!
//! The gpui `Editor` needs a `Window`/`Context` to construct, so these tests
//! exercise the document-language layer the editor rides on EXACTLY as the editor
//! drives it: a `RopeDoc` at line granularity, opened from file content, edited by
//! handing it a `ropey::Rope` (the same `edit_rope` call `Editor::save` makes),
//! branched per co-author, and merged. This is the data the `DocViewer` renders;
//! the visual half is `cargo run --bin merge_demo`.

use dregg_doc::{Author, Granularity, RopeDoc, Segment};
use ropey::Rope;

fn rope(s: &str) -> Rope {
    Rope::from_str(s)
}

/// Open a file -> a Document; edits accrue patches; blame/history are queryable.
/// This mirrors `Editor::open` (seed the document from file content) then a
/// sequence of `Editor::save`s (each `edit_rope`).
#[test]
fn open_then_edits_accrue_patches_with_blame() {
    // "open": seed from loaded file content (author = the local editor).
    let mut doc = RopeDoc::new(Granularity::Line);
    doc.edit_rope(Author(1), &rope("fn main() {\n    todo!()\n}\n"));
    assert_eq!(doc.history().len(), 1, "open seeds one genesis patch");

    // "save": the buffer changed — a second author fills in the body.
    doc.edit_rope(
        Author(2),
        &rope("fn main() {\n    println!(\"hi\");\n}\n"),
    );
    assert_eq!(doc.history().len(), 2, "each save accrues a patch");
    assert_eq!(
        doc.rope().to_string(),
        "fn main() {\n    println!(\"hi\");\n}\n",
        "the buffer is the materialized patch fold"
    );

    // The patch history is queryable: blame attributes each live span.
    let blame = doc.blame();
    let body = blame
        .iter()
        .find(|b| b.content.contains("println"))
        .expect("the body line is in blame");
    assert_eq!(body.author, Author(2), "the second author wrote the body");
    let sig = blame
        .iter()
        .find(|b| b.content.contains("fn main"))
        .expect("the signature line is in blame");
    assert_eq!(sig.author, Author(1), "the opener wrote the signature");
}

/// Blame does NOT smear when surrounding text moves — the git-blame middle-insert
/// failure cannot occur (attribution rides the content-addressed atom).
#[test]
fn blame_survives_a_middle_insert_by_a_third_author() {
    let mut doc = RopeDoc::new(Granularity::Line);
    doc.edit_rope(Author(1), &rope("top\nbottom\n"));
    // A THIRD author inserts a line BETWEEN them.
    doc.edit_rope(Author(3), &rope("top\nmiddle\nbottom\n"));

    let blame = doc.blame();
    let by = |c: &str| blame.iter().find(|b| b.content == c).map(|b| b.author);
    assert_eq!(by("top\n"), Some(Author(1)), "top stays Author(1)");
    assert_eq!(by("bottom\n"), Some(Author(1)), "bottom stays Author(1) — NOT smeared");
    assert_eq!(by("middle\n"), Some(Author(3)), "only the insert is Author(3)");
}

/// TWO editors branch off a shared document, edit offline, merge — CLEAN where the
/// edits are disjoint. (Each `RopeDoc` is one editor's buffer-as-document.)
#[test]
fn two_editors_merge_clean_when_disjoint() {
    // The shared document both editors opened.
    let mut shared = RopeDoc::new(Granularity::Line);
    shared.edit_rope(Author(1), &rope("# Title\n\nintro paragraph\n"));

    // Each editor forks its own offline copy (open-the-same-file, edit-apart).
    let mut alice = shared.branch();
    let mut bob = shared.branch();

    // Alice rewrites the title; Bob appends a section. Disjoint regions.
    alice.edit_rope(Author(1), &rope("# The Real Title\n\nintro paragraph\n"));
    bob.edit_rope(
        Author(2),
        &rope("# Title\n\nintro paragraph\n\n## New Section\n"),
    );

    // Merge Bob's branch into Alice's (the pushout).
    let mut merged = alice.branch();
    let rendered = merged.merge_branch(&bob);

    assert!(!rendered.has_conflict(), "disjoint edits merge CLEAN");
    let text = rendered.to_marked_string();
    assert!(text.contains("# The Real Title\n"), "Alice's title survived");
    assert!(text.contains("## New Section\n"), "Bob's section survived");
}

/// TWO editors edit the SAME region offline — a genuine conflict, surfaced as a
/// first-class object carrying both alternatives + authorship (NOT a `<<<<<<<`).
#[test]
fn two_editors_genuine_conflict_is_an_object_with_authorship() {
    let mut shared = RopeDoc::new(Granularity::Line);
    shared.edit_rope(Author(1), &rope("status: draft\n"));

    let mut alice = shared.branch();
    let mut bob = shared.branch();
    // Both append a different next line after the same tail — concurrent, clashing.
    alice.edit_rope(Author(1), &rope("status: draft\nreviewed-by: alice\n"));
    bob.edit_rope(Author(2), &rope("status: draft\nreviewed-by: bob\n"));

    let mut merged = alice.branch();
    let rendered = merged.merge_branch(&bob);

    assert!(rendered.has_conflict(), "concurrent same-tail edits clash");
    let region = rendered
        .conflicts()
        .next()
        .expect("the conflict is a first-class region");
    // BOTH alternatives are present, each attributed to its real author.
    assert_eq!(region.alternatives.len(), 2, "two pens, two alternatives");
    let authors: Vec<u64> = region
        .alternatives
        .iter()
        .map(|a| a.provenance.author.0)
        .collect();
    assert!(authors.contains(&1) && authors.contains(&2), "both authors named");
    // The clean prefix is still fully usable while the conflict stands.
    assert!(rendered.to_marked_string().starts_with("status: draft\n"));
    // The viewer renders THIS structure: a Clean run then a Conflict object.
    assert!(
        rendered.segments.iter().any(|s| matches!(s, Segment::Conflict(_))),
        "the rendered structure carries a Conflict segment the viewer surfaces"
    );
}
