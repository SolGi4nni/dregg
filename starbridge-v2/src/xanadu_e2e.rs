//! XANADU, END TO END — the dreggverse document language as ONE running demonstration.
//!
//! The individual organs are built and tested in their own modules: the
//! Pijul-shaped patch core ([`dregg_doc`] — patches, total merge, conflicts-as-objects),
//! the whole-cell transclusion ([`crate::cell_transclusion`] — provenanced live quotes
//! that darken per-viewer), and the two-way links ([`crate::links_here`] /
//! [`crate::dreggverse_map`] — the witness-graph read backward). This module is the
//! WELD: a single, `cargo test`-able demonstration that braids them into the
//! Nelson/Engelbart document the spec (`docs/deos/DOCUMENT-LANGUAGE.md`) describes, so
//! "the document language RUNS" is a fact, not a claim spread across four test suites.
//!
//! The four braided steps, each a real running assertion (no mocks, no stubs):
//!
//! 1. **A DOCUMENT IS A CELL OF PATCHES.** A document is a [`dregg_doc::History`] of
//!    patches; its content is the fold ([`dregg_doc::content`]). We BRANCH off a past
//!    cursor, make two divergent edit-streams, and [`dregg_doc::merge`] them: a
//!    DISJOINT-region merge composes CLEAN (the I-confluent union), while a
//!    same-position merge yields a first-class [`dregg_doc::ConflictRegion`] — a stored
//!    antichain of both alternatives with their provenance, never a silent overwrite —
//!    which a later resolution patch collapses. The edit-as-cap-gated-turn path is the
//!    same demonstration through the REAL executor ([`crate::doc_editor::DocEditor`]).
//!
//! 2. **TRANSCLUSION.** The document transcludes a live quote FROM another cell C via a
//!    REAL [`crate::cell_transclusion::WholeCellTransclusion`]: the quote carries
//!    provenance (the cited cell + its finalized surface commitment + receipt), it
//!    DARKENS for a reader whose caps cannot reach it (provenance kept, surface
//!    withheld — never forged), and it stays LIVE — re-resolving against the source web
//!    (`include`) and re-verifying its provenance chain (`verify`).
//!
//! 3. **BIDIRECTIONAL LINKS.** The transclusion registers BOTH directions: the forward
//!    quote (A → C) is recorded into the REAL [`Backlinks`] witness-graph, so C's
//!    "what links here" ([`crate::dreggverse_map::DreggverseMap::links_to`]) lists A as
//!    a backlink — a verifiable fact (observer + cited receipt + content commitment),
//!    not a hand-maintained index. The cockpit's [`crate::links_here::LinksHerePanel`]
//!    surfaces that same backlink, per-viewer fogged.
//!
//! 4. **ALL OF IT TOGETHER.** [`xanadu_demonstration`] runs steps 1–3 against one set
//!    of cells and returns a [`Demonstration`] report whose every field is a real
//!    observation of the running organs — the test below asserts the whole braid.

use dregg_doc::{
    content, merge, AtomId, Author, ConflictRegion, History, Patch, Rendered,
};

/// A structured report of what the end-to-end document-language demonstration actually
/// observed — every field a real read of a running organ, asserted by the test.
#[derive(Clone, Debug)]
pub struct Demonstration {
    // ── step 1: document-as-patches, branch + merge ──────────────────────────
    /// The document's content after the genesis patches (the fold of the history).
    pub base_text: String,
    /// The rendered content of the CLEAN merge of two disjoint-region branches — both
    /// edits present, no conflict (the I-confluent union composed).
    pub clean_merge_text: String,
    /// True iff the clean merge produced NO conflict region (the disjoint edits
    /// composed silently — the common, monotone case).
    pub clean_merge_is_clean: bool,
    /// The number of first-class conflict regions the CONFLICTING merge produced (two
    /// branches editing the same position) — exactly one antichain, a stored state.
    pub conflict_region_count: usize,
    /// The two alternatives the conflict carries, each tagged with the author who wrote
    /// it (the conflict is a state with provenance, not a silent overwrite).
    pub conflict_alternatives: Vec<(u64, String)>,
    /// True iff the conflict, once a resolution patch is applied, collapses to a single
    /// clean walk (resolution is just another additive patch).
    pub conflict_resolved_clean: bool,
    /// The resolved document's content after the resolution patch.
    pub resolved_text: String,

    // ── step 2: transclusion ─────────────────────────────────────────────────
    /// The `dregg://` provenance the transcluded quote carries (the cited source cell).
    pub quote_cites_source: bool,
    /// True iff the quote's provenance verifies (the embedded surface EQUALS its source
    /// — the anti-forge tooth).
    pub quote_verifies: bool,
    /// True iff a fully-capped reader sees INTO the quote (visible at their cap level).
    pub quote_visible_to_capped_reader: bool,
    /// True iff an UNDER-capped reader sees the quote DARKENED (surface withheld) while
    /// its provenance still survives (never forged).
    pub quote_darkens_for_undercapped: bool,
    /// True iff the quote re-resolves LIVE against the source web (a second `include`
    /// after the web evolves still yields the cited, verifying quote — never rots).
    pub quote_reresolves_live: bool,

    // ── step 3: bidirectional links ──────────────────────────────────────────
    /// True iff C's "what links here" lists the document A as a backlink (the reverse
    /// of the forward quote — both directions registered from ONE transclusion).
    pub backlink_a_in_c: bool,
    /// The cited receipt + content commitment of that backlink (a verifiable fact, not
    /// a bare pointer): non-empty iff the backlink carries real provenance.
    pub backlink_has_provenance: bool,
}

/// THE BRAID — run the whole document language end to end and report what was observed.
///
/// This is the gpui-free, executor-honest demonstration: it builds a document from
/// patches, branches and merges it (clean + conflict + resolve), transcludes a live
/// provenanced quote from a peer cell (visible / darkened / live-re-resolving), and
/// registers the two-way link so the source's backlinks include the document. Every
/// returned field is a real observation; the test below asserts the whole shape.
pub fn xanadu_demonstration() -> Demonstration {
    // ════════════════════════════════════════════════════════════════════════
    // STEP 1 — A DOCUMENT IS A CELL OF PATCHES; branch + merge (clean + conflict).
    // ════════════════════════════════════════════════════════════════════════
    //
    // The document is its patch-history; content is the fold. We author the genesis
    // line as two atoms (a real `Add` patch each), then BRANCH off the tail.
    let alice = Author(1);
    let bob = Author(2);

    let mut h = History::new();
    let (a_hello, p_hello) = Patch::add(1, "The treasury holds ", AtomId::ROOT);
    let (a_amount, p_amount) = Patch::add(2, "1000 grains.", a_hello);
    h.commit(Patch::by(alice, [p_hello]));
    h.commit(Patch::by(alice, [p_amount]));
    let base = h.replay();
    let base_text = content(&base).to_marked_string();

    // ── CLEAN merge: two branches edit DISJOINT regions ──────────────────────
    // Alice appends a new sentence at the tail (the prose region); Bob (concurrently,
    // off the SAME base) sets the document's canonical `title` field (a DISJOINT graph
    // region — prose atoms vs. the field store never overlap). The union is a valid
    // state with NO conflict — the I-confluent merge composes silently. (Two PROSE
    // inserts after the same anchor would instead be an antichain; that is the
    // conflicting case below. The genuinely-disjoint clean case touches non-overlapping
    // parts of the graph.)
    let alice_branch = Patch::by(alice, [Patch::add(10, " It is audited.", a_amount).1])
        .apply_to(&base);
    let bob_branch = Patch::by(
        bob,
        [dregg_doc::Op::SetField {
            name: "title".to_string(),
            value: "Treasury Ledger".to_string(),
            superseding: false,
        }],
    )
    .apply_to(&base);
    let clean = merge(&alice_branch, &bob_branch);
    let clean_r = content(&clean);
    let clean_merge_text = clean_r.to_marked_string();
    // The clean merge carries Alice's prose AND Bob's field, with NO conflict region.
    // A single (non-clashing) field assign yields exactly one live value, no clash.
    let clean_merge_has_field = clean
        .field("title")
        .iter()
        .any(|fa| fa.value == "Treasury Ledger");
    let clean_merge_is_clean = !clean_r.has_conflict() && clean_merge_has_field;

    // ── CONFLICTING merge: two branches edit the SAME position ───────────────
    // Both append a different continuation AFTER THE SAME tail atom. Neither orders the
    // other ⇒ the merged graph has a genuine antichain: a first-class CONFLICT STATE
    // carrying both alternatives + their provenance. NOT a silent overwrite; NOT a
    // rejected merge — a stored state the document lives in.
    let alice_alt = Patch::by(alice, [Patch::add(20, " Spend it wisely.", a_amount).1])
        .apply_to(&base);
    let bob_alt = Patch::by(bob, [Patch::add(21, " Save it all.", a_amount).1]).apply_to(&base);
    let conflicted = merge(&alice_alt, &bob_alt);
    let conflicted_r: Rendered = content(&conflicted);
    let conflicts: Vec<&ConflictRegion> = conflicted_r.conflicts().collect();
    let conflict_region_count = conflicts.len();
    let conflict_alternatives: Vec<(u64, String)> = conflicts
        .iter()
        .flat_map(|c| {
            c.alternatives
                .iter()
                .map(|alt| (alt.provenance.author.0, alt.text.clone()))
        })
        .collect();

    // ── RESOLVE the conflict: a later patch collapses the antichain ──────────
    // Resolution is just another additive patch (`Connect` ordering the alternatives).
    // We order alice's head before bob's — both kept, a single clean walk restored.
    let (resolved_text, conflict_resolved_clean) = if let Some(first) = conflicts.first() {
        let heads: Vec<AtomId> = first.alternatives.iter().map(|a| a.head).collect();
        if heads.len() >= 2 {
            let resolve = dregg_doc::resolve_connect_by(alice, &heads);
            let resolved = resolve.apply_to(&conflicted);
            let rr = content(&resolved);
            (rr.to_marked_string(), !rr.has_conflict())
        } else {
            (conflicted_r.to_marked_string(), false)
        }
    } else {
        (conflicted_r.to_marked_string(), false)
    };

    // ════════════════════════════════════════════════════════════════════════
    // STEP 2 — TRANSCLUSION: a live, provenanced quote FROM a peer cell C.
    // ════════════════════════════════════════════════════════════════════════
    use crate::cell_transclusion::{EmbedVisibility, WholeCellTransclusion};
    use starbridge_web_surface as web_aff;
    use web_aff::affordance::{AffordanceSurface, CellAffordance};
    use web_aff::delegate::SurfaceCapability;
    use web_aff::dregg_turn_reexport::Event;
    use web_aff::rehydrate::Membrane;
    use web_aff::transclusion::{Backlinks, TranscludedField};
    use web_aff::web_of_cells::WebOfCells;
    use web_aff::{AuthRequired, CellId, Effect};

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    // Publish cell C (the cited source) into a real web-of-cells: its surface root is
    // committed + 3-of-3 quorum-finalized — a genuine attested page, not a stub.
    let mut web = WebOfCells::new(3);
    let c_uri = web.publish(7, b"<cell C surface root>", "dregg://cell-C");
    let c_cell = c_uri.cell;

    // The document A (the host doing the including).
    let a_doc = cid(42);

    // C's published affordance surface ({view, comment, edit, admin}) — each a REAL
    // effect-template on the three-tier rights chain `Signature ⊂ Either ⊂ None`.
    let view_evt = Effect::EmitEvent {
        cell: c_cell,
        event: Event { topic: [1u8; 32], data: vec![] },
    };
    let c_surface = AffordanceSurface::new(c_cell)
        .declare(CellAffordance::new("view", AuthRequired::Signature, view_evt.clone()))
        .declare(CellAffordance::new("comment", AuthRequired::Either, view_evt.clone()))
        .declare(CellAffordance::new("edit", AuthRequired::Either, view_evt));
    // The embed lineage: a strong (Either) authority ceiling over C.
    let lineage = SurfaceCapability::root(c_cell, AuthRequired::Either);

    // A transcludes the WHOLE of C — a real verified finalized read (anti-forge tooth:
    // a forged/absent surface would fail HERE).
    let quote = WholeCellTransclusion::embed(&web, a_doc, &c_uri, c_surface, lineage)
        .expect("C's surface is finalized and embeds");

    // The provenance: the quote cites C and verifies (the embedded surface = its source).
    let quote_cites_source = quote.cite().source.cell == c_cell && quote.cite().finalized;
    let quote_verifies = quote.verify();

    // A fully-capped (Either) reader sees INTO the quote at their cap level.
    let capped = Membrane::new(SurfaceCapability::root(cid(50), AuthRequired::Either));
    let capped_view = quote.project_for(&capped);
    let quote_visible_to_capped_reader = capped_view.is_visible();

    // An UNDER-capped reader (a `Custom` identity, INCOMPARABLE with Either — neither
    // attenuates the other) sees the quote DARKENED: surface withheld, provenance kept.
    let undercapped = Membrane::new(SurfaceCapability::root(
        cid(51),
        AuthRequired::Custom { vk_hash: [9u8; 32] },
    ));
    let dark_view = quote.project_for(&undercapped);
    let quote_darkens_for_undercapped = matches!(dark_view.visibility, EmbedVisibility::Darkened)
        // the provenance SURVIVES the darkening (never forged, never substituted)
        && dark_view.provenance.source.cell == c_cell
        && dark_view.provenance.finalized;

    // LIVE: the quote re-resolves against the source web. The web evolves (a second
    // cell is published into it), yet a fresh `include` of C still yields the cited,
    // verifying quote — the citation pins an immutable past, so it never rots.
    let _other = web.publish(8, b"<unrelated cell D>", "dregg://cell-D");
    let reresolved = TranscludedField::include(&web, &c_uri);
    let quote_reresolves_live = reresolved
        .as_ref()
        .map(|f| f.verify().is_ok() && f.cite().source.cell == c_cell)
        .unwrap_or(false);

    // ════════════════════════════════════════════════════════════════════════
    // STEP 3 — BIDIRECTIONAL LINKS: the transclusion registers BOTH directions.
    // ════════════════════════════════════════════════════════════════════════
    //
    // The forward quote is A → C. We record it into the REAL `Backlinks` witness-graph
    // keyed by the SOURCE the quote points at — so the reverse direction (C ← A) is now
    // a fact: C's "what links here" lists A, with the cited receipt + content
    // commitment. ONE transclusion, both directions registered.
    let forward = reresolved.expect("the live quote re-resolves");
    let mut backlinks = Backlinks::new();
    backlinks.observe(a_doc, &forward);

    use crate::dreggverse_map::DreggverseMap;
    let map = DreggverseMap::new(&backlinks);
    let observers = map.links_to(c_cell);
    let backlink_a_in_c = observers.iter().any(|o| o.observer == a_doc);
    let backlink_has_provenance = observers
        .iter()
        .find(|o| o.observer == a_doc)
        .map(|o| o.receipt_hash != [0u8; 32] || o.content_hash != [0u8; 32])
        .unwrap_or(false);

    Demonstration {
        base_text,
        clean_merge_text,
        clean_merge_is_clean,
        conflict_region_count,
        conflict_alternatives,
        conflict_resolved_clean,
        resolved_text,
        quote_cites_source,
        quote_verifies,
        quote_visible_to_capped_reader,
        quote_darkens_for_undercapped,
        quote_reresolves_live,
        backlink_a_in_c,
        backlink_has_provenance,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::doc_editor::{DocAuthor, DocEditor};

    /// THE WHOLE BRAID, in one run: a document of patches with a clean + a conflicting
    /// merge (conflict-as-object, then resolved), a live provenanced transclusion that
    /// darkens for an under-capped reader, and the source's backlinks listing the doc.
    #[test]
    fn xanadu_runs_end_to_end() {
        let d = xanadu_demonstration();

        // ── STEP 1: document-as-patches, branch + merge ──────────────────────
        assert_eq!(
            d.base_text, "The treasury holds 1000 grains.",
            "the document content is the fold of its patch-history"
        );

        // CLEAN merge: both disjoint edits present (Alice's prose append + Bob's field),
        // NO conflict. `clean_merge_is_clean` already folds in "the field is carried".
        assert!(
            d.clean_merge_is_clean,
            "two disjoint-region branches merge clean (the I-confluent union composes, \
             carrying Alice's prose AND Bob's field)"
        );
        assert!(
            d.clean_merge_text.contains("It is audited."),
            "the clean merge carries Alice's prose append (lost neither edit): {:?}",
            d.clean_merge_text
        );

        // CONFLICTING merge: exactly one first-class conflict region, with BOTH
        // alternatives attributed to who wrote them (a stored state, not an overwrite).
        assert_eq!(
            d.conflict_region_count, 1,
            "two same-position branches produce exactly ONE first-class conflict region"
        );
        let authors: Vec<u64> = d.conflict_alternatives.iter().map(|(a, _)| *a).collect();
        assert!(
            authors.contains(&1) && authors.contains(&2),
            "the conflict carries BOTH authors' alternatives (provenance kept): {:?}",
            d.conflict_alternatives
        );
        let texts: Vec<&str> = d.conflict_alternatives.iter().map(|(_, t)| t.as_str()).collect();
        assert!(
            texts.iter().any(|t| t.contains("Spend it wisely"))
                && texts.iter().any(|t| t.contains("Save it all")),
            "neither alternative was silently dropped: {:?}",
            d.conflict_alternatives
        );

        // RESOLVE: a later patch collapses the antichain to a single clean walk.
        assert!(
            d.conflict_resolved_clean,
            "a resolution patch collapses the conflict to a clean document"
        );
        assert!(
            d.resolved_text.contains("Spend it wisely") && d.resolved_text.contains("Save it all"),
            "the order-resolution KEPT both alternatives (nothing lost): {:?}",
            d.resolved_text
        );

        // ── STEP 2: transclusion ─────────────────────────────────────────────
        assert!(d.quote_cites_source, "the quote carries provenance citing cell C");
        assert!(d.quote_verifies, "the quote's provenance verifies (anti-forge)");
        assert!(
            d.quote_visible_to_capped_reader,
            "a fully-capped reader sees into the quote"
        );
        assert!(
            d.quote_darkens_for_undercapped,
            "an under-capped reader sees the quote DARKENED, provenance surviving"
        );
        assert!(
            d.quote_reresolves_live,
            "the quote re-resolves LIVE against the evolved source web (never rots)"
        );

        // ── STEP 3: bidirectional links ──────────────────────────────────────
        assert!(
            d.backlink_a_in_c,
            "C's 'what links here' lists document A (the reverse of the forward quote)"
        );
        assert!(
            d.backlink_has_provenance,
            "the backlink carries its cited receipt + content commitment (a verifiable fact)"
        );
    }

    /// The SAME step-1 demonstration through the REAL executor: every edit is a
    /// cap-gated turn ([`DocEditor`]), a conflict is sown by two concurrent committed
    /// turns and is a first-class state, and a resolution patch (another real turn)
    /// collapses it. This proves the patch-as-turn ride, not just the pure patch core.
    #[test]
    fn the_executor_driven_document_branches_merges_and_resolves() {
        let mut ed = DocEditor::new();

        // An edit is a cap-gated turn (committed, finalized, real receipt).
        let outcome = ed.append("A first sentence. ", DocAuthor::ALICE);
        assert!(outcome.committed(), "an authorized edit commits as a real turn");
        assert!(!ed.has_conflict(), "a linear edit history has no conflict");

        // Sow a first-class PROSE conflict: two concurrent committed turns after the
        // same tail. The document is honestly conflicted there (a state), clean elsewhere.
        let (a, b) = ed.sow_prose_conflict(" Alice's ending.", " Bob's ending.");
        assert!(a.committed() && b.committed(), "both alternative edits commit as turns");
        assert!(ed.has_conflict(), "the concurrent edits produced a first-class conflict");
        let views = ed.conflicts();
        assert_eq!(views.len(), 1, "exactly one conflict region");
        let names: Vec<&str> = views[0].alternatives.iter().map(|a| a.author_name).collect();
        assert!(
            names.contains(&"alice") && names.contains(&"bob"),
            "both alternatives are attributed to who wrote them: {names:?}"
        );

        // RESOLVE by ordering — a real cap-gated turn collapses the antichain.
        let heads: Vec<_> = views[0].alternatives.iter().map(|alt| alt.head).collect();
        let resolved = ed.resolve_prose_order(&heads, DocAuthor::ALICE);
        assert!(resolved.committed(), "the resolution commits as a real turn");
        assert!(!ed.has_conflict(), "the resolution collapsed the conflict to a clean doc");

        // The document is a real cell with a real commitment that moved with the edits.
        assert!(ed.commitment_matches(), "the document commitment is the real cell state");
    }

    /// The executor anti-ghost tooth: an editor lacking the per-region edit cap is
    /// REFUSED in-band (a `Result` error, never a panic), the document untouched.
    #[test]
    fn an_unauthorized_edit_is_refused_in_band() {
        let mut ed = DocEditor::new();
        let outcome = ed.attempt_unauthorized("a forbidden edit", DocAuthor::BOB);
        assert!(
            outcome.unauthorized(),
            "the editor lacking the region cap is refused in-band (CapabilityNotHeld)"
        );
    }
}
