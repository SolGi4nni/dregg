//! THE PROGRAM-SOURCE-AS-DOCUMENT WELD, PROVEN BY RUNNING: a deos-js gadget's
//! `view_source` is a `dregg_doc::Doc` (a patch-history), so the three XANADU document
//! powers apply to a PROGRAM — and the program still LOADS-AND-RUNS.
//!
//! The chain proven here:
//!   PATCH      — edit a gadget's source via a patch; the loaded program reflects the
//!                edit; `blame` attributes each line to its authoring patch + author.
//!   TRANSCLUDE — one gadget quotes a fragment of another's source as a provenanced
//!                live quote; an unauthorized viewer gets a DARKENED quote (citation
//!                survives, bytes withheld) — cap-bounded like the membrane.
//!   MERGE      — two authors edit the same gadget concurrently; a disjoint merge folds
//!                CLEAN; an overlapping edit yields a first-class ConflictRegion.
//!   RUN        — a gadget whose source is a Doc seals its fold into a manifest, mints,
//!                serializes, loads in a fresh runtime, and FIRES an affordance — a real
//!                cap-gated verified turn on the loaded cell. The doc IS the source.

use deos_js::portable::{AppletManifest, PortableApplet};
use deos_js::program_doc::{GadgetCite, ProgramSource, TranscludedFragment};
use deos_js::{AffordanceSpec, ApplyOp};
use dregg_cell::AuthRequired;
use dregg_doc::{Author, Segment};

/// A counter gadget's manifest, with a multi-line JS `view_source` (so line-granular
/// patches/blame/merge have something to bite on).
fn counter_manifest(view_source: &str) -> AppletManifest {
    AppletManifest {
        seed_fields: vec![(0usize, 0u64)],
        affordances: vec![
            AffordanceSpec {
                name: "inc".into(),
                required: AuthRequired::Signature,
                op: ApplyOp::AddToSlot { slot: 0 },
            },
            AffordanceSpec {
                name: "dec".into(),
                required: AuthRequired::Signature,
                op: ApplyOp::SubFromSlot { slot: 0 },
            },
            AffordanceSpec {
                name: "reset".into(),
                required: AuthRequired::Proof,
                op: ApplyOp::SetSlot { slot: 0, value: 0 },
            },
        ],
        held: AuthRequired::Signature,
        view_source: view_source.to_string(),
    }
}

const BASE_SOURCE: &str = "\
deos.ui.vstack(
  deos.ui.text(\"Counter\"),
  deos.ui.bind(function() { return app.get(0); }),
  deos.ui.button(\"+1\", \"inc\", 1)
)
";

/// ── PATCH: editing a gadget's source is a patch; blame attributes each line. ───────
#[test]
fn program_source_edits_as_a_patch_and_blame_attributes_it() {
    let alice = Author(1);
    let bob = Author(2);

    // Alice seeds the gadget's source (the genesis patch carries the whole base).
    let mut src = ProgramSource::seed(alice, BASE_SOURCE);
    assert_eq!(src.view_source(), BASE_SOURCE, "the fold reproduces the seed source");

    // Bob edits: insert a label line in the middle (a PATCH, not a rewrite).
    let edited = "\
deos.ui.vstack(
  deos.ui.text(\"Counter\"),
  deos.ui.text(\"clicks so far:\"),
  deos.ui.bind(function() { return app.get(0); }),
  deos.ui.button(\"+1\", \"inc\", 1)
)
";
    src.edit(bob, edited);
    assert_eq!(src.view_source(), edited, "the edited source is the doc's new fold");

    // BLAME: the inserted line is attributed to Bob; the surrounding lines stay Alice's
    // (correct-by-construction — the middle insert did NOT smear blame).
    let blamed = src.blame();
    let inserted = blamed
        .iter()
        .find(|l| l.content.contains("clicks so far"))
        .expect("the inserted line is present in blame");
    assert_eq!(inserted.author, bob, "the inserted line is blamed on its author (Bob)");

    let surrounding = blamed
        .iter()
        .find(|l| l.content.contains("deos.ui.button"))
        .expect("a surrounding line is present");
    assert_eq!(
        surrounding.author, alice,
        "a line Bob did NOT touch is still attributed to Alice (blame did not smear)"
    );
    // The inserted line's patch id differs from the seed line's patch id (distinct edits).
    assert_ne!(inserted.patch, surrounding.patch, "the two lines came from different patches");
}

/// ── TRANSCLUDE: a provenanced live quote of another gadget's source fragment, ──────
///    cap-bounded (darkens out of cap).
#[test]
fn one_gadget_transcludes_another_gadgets_source_fragment_with_provenance() {
    let alice = Author(1);
    let carol = Author(3);

    // The SOURCE gadget (the one being quoted), authored by Alice.
    let source_gadget = ProgramSource::seed(alice, BASE_SOURCE);
    let cite = GadgetCite(0xC0FFEE);

    // An AUTHORIZED viewer transcludes the "bind" fragment (line index 2) — a live,
    // provenanced quote: the quoted line carries ALICE's authorship (a fact).
    let quote = source_gadget.transclude_fragment(cite, 2..3, /*viewer_can_read=*/ true);
    match &quote {
        TranscludedFragment::Quoted { from, lines } => {
            assert_eq!(*from, cite, "the quote cites the source gadget");
            assert_eq!(lines.len(), 1, "one line was quoted");
            assert!(lines[0].content.contains("deos.ui.bind"), "the right fragment was quoted");
            assert_eq!(
                lines[0].author, alice,
                "the quoted line carries the SOURCE author's provenance (a provenanced quote)"
            );
        }
        other => panic!("expected an authorized quote, got {other:?}"),
    }
    assert!(quote.text().contains("deos.ui.bind"), "the quote's bytes are the source fragment");

    // An UNAUTHORIZED viewer gets a DARKENED quote: the citation survives, the bytes do
    // not (cap-bounded like the membrane — no amplification).
    let dark = source_gadget.transclude_fragment(cite, 2..3, /*viewer_can_read=*/ false);
    assert!(dark.is_darkened(), "an out-of-cap viewer's quote is darkened");
    assert_eq!(dark.cite(), &cite, "the citation (which gadget) survives darkening");
    assert_eq!(dark.text(), "", "the bytes were withheld (darkened)");

    // A QUOTING gadget (Carol's) splices the authorized quote into its own source: the
    // quote is now part of Carol's program, but the quoted line's ORIGINAL authorship
    // (Alice) is preserved as the citation.
    let mut quoter = ProgramSource::seed(carol, "// Carol's gadget\n");
    quoter.splice_quote(carol, &quote);
    assert!(
        quoter.view_source().contains("deos.ui.bind"),
        "the quoted fragment is spliced into the quoting gadget's source"
    );
    // The quote record still attributes the quoted material to Alice (provenance fact).
    assert_eq!(quote.cite(), &cite);
    if let TranscludedFragment::Quoted { lines, .. } = &quote {
        assert_eq!(lines[0].author, alice, "the quote's provenance still names the original author");
    }
}

/// ── MERGE: two concurrent edits — disjoint folds clean; overlapping is a conflict. ─
#[test]
fn two_authors_merge_concurrent_edits_disjoint_clean_overlapping_conflicts() {
    let alice = Author(1);
    let bob = Author(2);

    // ── disjoint: Alice edits the FIRST line, Bob the LAST line — no overlap. ──
    {
        let base = ProgramSource::seed(alice, "header\nmiddle\nfooter\n");

        // Alice's branch: change the header.
        let mut a = base.clone();
        a.edit(alice, "HEADER-A\nmiddle\nfooter\n");

        // Bob's branch (forked from the same base): change the footer.
        let mut b = base.clone();
        b.edit(bob, "header\nmiddle\nFOOTER-B\n");

        // Merge Bob's branch into Alice's: a disjoint merge folds CLEAN.
        let rendered = a.merge(&b);
        assert!(!rendered.has_conflict(), "disjoint edits merge with NO conflict");
        let folded = a.view_source();
        assert!(folded.contains("HEADER-A"), "Alice's header change survived the merge");
        assert!(folded.contains("FOOTER-B"), "Bob's footer change survived the merge");
        assert!(folded.contains("middle"), "the untouched middle line is intact");
    }

    // ── overlapping: both edit the SAME line concurrently — a first-class conflict. ──
    {
        let base = ProgramSource::seed(alice, "header\nshared\nfooter\n");

        let mut a = base.clone();
        a.edit(alice, "header\nSHARED-A\nfooter\n"); // Alice rewrites the shared line

        let mut b = base.clone();
        b.edit(bob, "header\nSHARED-B\nfooter\n"); // Bob rewrites the SAME line

        let rendered = a.merge(&b);
        assert!(
            rendered.has_conflict(),
            "two concurrent edits to the SAME line yield a first-class conflict (not a silent overwrite)"
        );
        // The conflict is a real ConflictRegion carrying BOTH alternatives, each with
        // its author — a fact, not a guess.
        let conflict = rendered
            .segments
            .iter()
            .find_map(|s| match s {
                Segment::Conflict(c) => Some(c),
                _ => None,
            })
            .expect("a conflict region is present");
        assert!(
            conflict.alternatives.len() >= 2,
            "the conflict carries both authors' alternatives"
        );
        let authors: Vec<u64> = conflict.alternatives.iter().map(|alt| alt.provenance.author.0).collect();
        assert!(authors.contains(&alice.0), "Alice's alternative is attributed to her");
        assert!(authors.contains(&bob.0), "Bob's alternative is attributed to him");
    }
}

/// ── RUN: a gadget whose source is a Doc seals its fold and LOADS-AND-RUNS — an ─────
///    affordance fire is a real cap-gated verified turn. The doc IS the source.
#[test]
fn a_patched_document_program_loads_and_runs_a_real_turn() {
    let alice = Author(1);
    let bob = Author(2);

    // Alice authors the gadget's source as a DOCUMENT, then Bob patches it.
    let mut src = ProgramSource::seed(alice, BASE_SOURCE);
    let patched = BASE_SOURCE.replace("\"Counter\"", "\"Counter (patched)\"");
    src.edit(bob, &patched);
    assert!(src.view_source().contains("Counter (patched)"), "the source carries Bob's patch");

    // SEAL the doc's fold into a manifest — the rest of the portable path is unchanged.
    let manifest = src.seal_into(counter_manifest(BASE_SOURCE));
    assert_eq!(
        manifest.view_source,
        src.view_source(),
        "the sealed manifest's view_source IS the doc's fold (the doc is the source of truth)"
    );
    assert!(
        manifest.view_source.contains("Counter (patched)"),
        "the patched (document) source is what gets minted into the cell"
    );

    // MINT the gadget from the document-sourced manifest, advance its model, serialize.
    let mut pk = [0u8; 32];
    pk[0] = 0xD0;
    let mut origin = PortableApplet::mint(pk, [0u8; 32], &manifest);
    origin.fire("inc", 4).unwrap(); // a real turn on the origin
    assert_eq!(origin.get_u64(0), 4);
    let cell_bytes = PortableApplet::to_cell_bytes(&origin);

    // LOAD in a FRESH runtime: the cell carries the PATCHED (document) source.
    let (mut loaded, loaded_manifest) =
        PortableApplet::from_cell(&cell_bytes).expect("load the document-sourced gadget");
    assert!(
        loaded_manifest.view_source.contains("Counter (patched)"),
        "the loaded cell carries the PATCHED document source (the fold travelled in the cell)"
    );

    // FIRE on the loaded gadget → a REAL cap-gated verified turn on the loaded cell.
    let receipt = loaded.fire("inc", 10).expect("the document-sourced program's inc fires a real turn");
    assert_ne!(receipt.receipt_hash(), [0u8; 32], "the fire left a real receipt");
    assert_eq!(loaded.get_u64(0), 14, "the loaded model advanced (4 + 10) via a verified turn");
    assert_eq!(loaded.receipt_count(), 1, "exactly one verified turn committed");

    // The cap tooth is intact: reset (Proof) vs held Signature → refused, anti-ghost.
    let refused = loaded.fire("reset", 0);
    assert!(
        matches!(refused, Err(deos_js::FireError::Unauthorized { .. })),
        "the cap tooth still refuses the over-reach on the document-sourced program"
    );
    assert_eq!(loaded.get_u64(0), 14, "the refused turn changed nothing");
}
