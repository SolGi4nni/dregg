//! **THE END-TO-END WELD — the literate surface rides the real cap-gated
//! executor.** (DOCUMENT-LANGUAGE.md §3.3 per-region caps, §4.3 dregg-native.)
//!
//! Two halves of the document language were built but never joined in one ride:
//!
//! - the **literate surface** ([`LiterateDoc`]): a markup that parses to a
//!   [`Patch`] (`text -> patch`), with conflicts as first-class round-tripping
//!   syntax;
//! - the **canonical substrate ride** ([`ExecutorDrivenDoc`]): a patch driven
//!   through the genuine `dregg_turn::TurnExecutor` — cap-gated, finalized,
//!   journaled — so the document commitment is the real `fields_root` a light
//!   client trusts.
//!
//! This file is the weld: an author *types literate text*, that text becomes a
//! `Patch`, and the patch is driven through the **real executor** onto a real
//! cell. So the full chain a reader cares about — `text -> patch -> turn ->
//! committed cell -> receipt` — is exercised end to end, not just its two halves
//! in isolation.
//!
//! SUBSTRATE-GATED: this weld exercises the real `dregg_turn::TurnExecutor` and
//! [`ExecutorDrivenDoc`], both of which live behind `--features substrate` (the
//! `../cell` / `../turn` ride). With the feature OFF the standalone core builds
//! and tests in isolation, so this whole file is `#![cfg(feature = "substrate")]`.
//! (Reconciliation note: [`ExecutorDrivenDoc`] is the ONE canonical
//! doc-on-cell model; the former hand-assembled `DocCell`/`heap_map` path —
//! which landed document leaves in the cell's fixed register file rather than the
//! committed `fields_map` overflow region, and never round-tripped through the
//! real executor — is RETIRED.)
//!
//! ## Both polarities (the standing law: bite TRUE and bite FALSE)
//!
//! - `literate_text_drives_the_real_executor` (TRUE) — an authorized author
//!   types literate prose; the edit drives through the executor and commits with
//!   a FINAL receipt over the real cell, and the committed document folds back to
//!   exactly the prose typed.
//! - `unauthorized_literate_edit_is_refused_in_band` (FALSE) — an editor lacking
//!   the per-region cap types the same prose; the executor's cross-cell cap gate
//!   REFUSES it in-band (`CapabilityNotHeld`), and the document is left untouched.
//! - `concurrent_literate_authors_yield_a_first_class_conflict_over_the_cell`
//!   (CONFLICT-AS-STATE) — two authors each type a distinct line after a shared
//!   base, each driving their OWN executor-backed replica; merging the two
//!   committed replicas' witness graphs surfaces a `<<<`-block [`ConflictRegion`]
//!   that round-trips through the literate parser — a conflict is a legible,
//!   first-class STATE carried over the real substrate, never a merge failure.

#![cfg(feature = "substrate")]

use dregg_doc::{
    Author, AtomId, ExecutorDrivenDoc, LiterateDoc, content, merge, parsed_conflicts_of,
    parsed_shape, render,
};
use dregg_turn::{Finality, TurnError};

/// The literate source a single author types: a small frontmatter + two prose
/// lines. The chain under test compiles THIS text into a patch and drives the
/// patch through the real executor.
const SRC: &str = "\
The cat sat.
The cat ran.
";

#[test]
fn literate_text_drives_the_real_executor() {
    // The author HOLDS the per-region edit cap → the literate edit commits.
    let mut region = ExecutorDrivenDoc::new(1, 2, /* holds_cap */ true);

    // 1. text -> patch (the literate surface).
    let mut surface = LiterateDoc::new();
    let patch = surface.edit(Author(1), SRC);

    // 2. patch -> turn -> committed cell (the real executor).
    let pre = region.state_commitment();
    let receipt = region
        .edit(patch)
        .expect("an authorized literate edit commits through the executor");

    // THE FINALITY UPGRADE: driving through the real executor finalizes the
    // receipt (not the direct-assembly `Tentative`).
    assert_eq!(
        receipt.finality,
        Finality::Final,
        "the literate edit drove the real executor → a FINAL receipt"
    );
    assert_eq!(receipt.agent, region.editor_id(), "the editor is the turn's agent");
    assert_ne!(
        region.state_commitment(),
        pre,
        "the literate edit moved the real document commitment"
    );

    // The document the algebra sees and the commitment the executor wrote are the
    // SAME object, and it folds back to exactly the prose typed.
    assert!(region.commitment_matches_projection());
    assert_eq!(
        content(region.graph()).to_marked_string(),
        "The cat sat.\nThe cat ran.\n",
        "the committed document is exactly the typed prose"
    );
}

#[test]
fn unauthorized_literate_edit_is_refused_in_band() {
    // The author LACKS the region cap → the executor's cross-cell cap gate refuses
    // the literate edit IN-BAND. The anti-ghost tooth: a Result error, not a panic,
    // and the document is left untouched.
    let mut region = ExecutorDrivenDoc::new(3, 4, /* holds_cap */ false);
    let pre = region.state_commitment();

    let mut surface = LiterateDoc::new();
    let patch = surface.edit(Author(1), SRC);

    let err = region
        .edit(patch)
        .expect_err("an editor without the region cap is refused");
    match err {
        TurnError::CapabilityNotHeld { actor, target } => {
            assert_eq!(actor, region.editor_id(), "the editor is the refused actor");
            assert_eq!(target, region.region_id(), "the region is the gated target");
        }
        other => panic!("expected CapabilityNotHeld, got {other:?}"),
    }

    // UNTOUCHED: the executor rolled the ledger back and the witness graph too.
    assert_eq!(
        region.state_commitment(),
        pre,
        "a refused literate edit leaves the commitment untouched"
    );
    assert!(region.commitment_matches_projection());
    assert_eq!(
        content(region.graph()).to_marked_string(),
        "",
        "the refused edit's prose did not land"
    );
}

#[test]
fn concurrent_literate_authors_yield_a_first_class_conflict_over_the_cell() {
    // A shared base committed through the executor, then two authors each type a
    // distinct line after it on their OWN executor-backed replica. The literate
    // surface produces the patches; the executor commits each; merging the two
    // committed replicas' witness graphs surfaces a first-class conflict that the
    // literate parser round-trips.

    // ── Shared base: one line, committed through the executor. ────────────────
    // We use the SAME literate surface to produce the base patch for BOTH
    // replicas, so they genuinely fork from one base (identical atom ids).
    let mut base_surface = LiterateDoc::new();
    let base_patch = base_surface.edit(Author(0), "shared\n");

    let make_replica = |editor_seed: u8, region_seed: u8| {
        let mut r = ExecutorDrivenDoc::new(editor_seed, region_seed, true);
        r.edit(base_patch.clone()).expect("base edit commits");
        r
    };
    let mut replica_a = make_replica(11, 12);
    let mut replica_b = make_replica(21, 22);

    // ── Author 1 types a distinct line; Author 2 types another — concurrently
    //    (each off the SAME shared base, on its own replica). ───────────────────
    let mut surface_a = clone_surface(&base_surface);
    let patch_a = surface_a.edit(Author(1), "shared\nalpha\n");
    replica_a.edit(patch_a).expect("author 1's edit commits");

    let mut surface_b = clone_surface(&base_surface);
    let patch_b = surface_b.edit(Author(2), "shared\nbeta\n");
    replica_b.edit(patch_b).expect("author 2's edit commits");

    // Each replica is individually clean and substrate-consistent.
    assert!(replica_a.commitment_matches_projection());
    assert!(replica_b.commitment_matches_projection());
    assert!(!content(replica_a.graph()).has_conflict());
    assert!(!content(replica_b.graph()).has_conflict());

    // ── The merge of the two committed replicas' witness graphs is the conflict.
    let merged = merge(replica_a.graph(), replica_b.graph());
    let rendered = content(&merged);
    assert!(
        rendered.has_conflict(),
        "two concurrent literate tail-edits over the cell => a first-class conflict"
    );

    // The conflict renders a legible `<<<`-block with BOTH alternatives + authors.
    let src = render(&rendered);
    assert!(src.contains("<<< prose"), "renders a prose conflict block:\n{src}");
    assert!(src.contains("|| @1: alpha"), "alternative A with its author:\n{src}");
    assert!(src.contains("|| @2: beta"), "alternative B with its author:\n{src}");

    // And it ROUND-TRIPS: the rendered block parses back to the same region the
    // fold surfaced — a conflict is a first-class, legible, round-tripping STATE.
    let reparsed = parsed_conflicts_of(&src);
    let folded: Vec<_> = rendered.conflicts().map(parsed_shape).collect();
    assert_eq!(
        reparsed, folded,
        "the conflict block over the real cell round-trips through the literate parser"
    );

    // Sanity: the shared prefix is still clean and usable.
    assert!(src.starts_with("shared\n"), "the shared base line is clean:\n{src}");
    let _ = AtomId::ROOT; // keep the surface import honest if the helper changes
}

/// Clone a [`LiterateDoc`] for a fork (it is `Clone`). A thin helper so the two
/// concurrent authors genuinely branch from one shared base surface.
fn clone_surface(d: &LiterateDoc) -> LiterateDoc {
    d.clone()
}
