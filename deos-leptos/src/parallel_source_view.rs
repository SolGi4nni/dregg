//! # The EEL — Ted Nelson's **parallel source view**, made runnable on the verified
//! substrate.
//!
//! [`deos_web_cells::DreggverseDocument`] already gives us Xanadu's *actual* document
//! (an EDL of OWN spans interleaved with **transcluded spans** of other cells), and its
//! [`deos_web_cells::RenderedSpan::source_link`] gives, per span, the navigable
//! `(source dregg://cell, byte range)` anchor. What Nelson drew on top of that — and
//! Xanadu never shipped honestly — is the **EEL**: render the document in one column
//! and, **beside each transcluded span**, its SOURCE cell with the quoted range
//! highlighted, navigable ("jump to source"). The two-way docuverse, made *visual*.
//!
//! This module is that view, in the Leptos runtime, built ENTIRELY on the committed
//! `deos-web-cells` API (it edits no protocol type, invents no fetch, no membrane, no
//! attestation). The pieces:
//!
//! * a **scenario** ([`EelScenario`]) — a real [`WebOfCells`] holding several source
//!   cells, a multi-span [`DreggverseDocument`] that quotes ranges of them interleaved
//!   with OWN content, and the source-side `lineage` + a `weaker viewer` membrane (so
//!   one span DARKENS — the viewer lacks authority). Everything is the genuine
//!   `WebOfCells::publish` / `DreggverseDocument::resolve_for` machinery the
//!   `deos-web-cells` tests drive;
//! * a **row projection** ([`EelRow`]) — per EDL span: the document text it contributes,
//!   and (for a quote) its source cell's FULL committed bytes with the quoted byte
//!   range marked, the `source_link` jump anchor, and whether it darkened. The
//!   parallel-source map, computed from the REAL [`RenderedSpan::source_link`] +
//!   [`Provenance`] (never a hand-maintained index);
//! * an **SSR two-column render** ([`render_parallel_source_view`]) — the document
//!   column (each quote an `<a href="#eel-src-N">` jump link) beside the source column
//!   (each source cell, the quoted range wrapped in `<mark>`, with the matching
//!   `id="eel-src-N"` jump target). A DARKENED span still renders its citation + the
//!   honest line *"you may not read this, but here is what it cites"* — the source's
//!   bytes withheld, never forged;
//! * a **reactive component** ([`ParallelSourceView`]) — a `RwSignal` source-height
//!   trigger + a [`Memo`] that re-resolves `resolve_for` whenever a source is amended,
//!   so the highlighted range in BOTH columns tracks the source LIVE (the unbreakable
//!   link, in the EEL). Same `RwSignal`/`Memo` idiom as [`crate::transclusion_demo`];
//! * a **headless sequence** ([`eel_sequence`]) — render → amend a source → re-render,
//!   the demo's proof exercised by the tests and printed by `cargo run --bin
//!   parallel_source_view`. The runnable form of the live update, in the parallel view.
//!
//! ## Honest scope (the named follow-on, NOT built here)
//!
//! What this delivers is the **semantic** parallel-source view: the two columns, the
//! highlighted range, the working `#eel-src-N` jump anchor, the darkened-citation case —
//! all over the verified document, rendered to HTML and exercised headlessly (the same
//! reactive graph a hydrate build ships, proved by the SSR sequence). What it does NOT
//! build is the **servo-render pixel layout + click-routing**: the actual side-by-side
//! *visual* pane geometry (a real two-pane scroll-synced widget), the on-click *scroll
//! the source pane to the highlight* behavior, and the cross-pane hover correspondence.
//! Those are the `servo-render` / browser-hydration seam — the anchor (`#eel-src-N`) is
//! the contract that lane consumes; the pixel pane is its work, named here, not built in
//! this module.

use leptos::prelude::*;

use deos_web_cells::AuthRequired;
use deos_web_cells::{
    DreggUri, DreggverseDocument, Membrane, Provenance, RenderedDocument, RenderedSpan, Span,
    SpanRange, SurfaceCapability, TranscludedField, WebBundle, WebOfCells,
};

// ════════════════════════════════════════════════════════════════════════════
// THE SCENARIO — a real web-of-cells, a multi-span dreggverse document, and the
// per-viewer authority that darkens one span. All the genuine deos-web-cells API.
// ════════════════════════════════════════════════════════════════════════════

/// A worked **EEL scenario** — a real [`WebOfCells`] with several source cells, a
/// multi-span [`DreggverseDocument`] quoting ranges of them (interleaved with OWN
/// content), and the per-viewer authority pieces that make ONE span DARKEN.
///
/// This is the parallel-source view's input, built entirely on the committed
/// `deos-web-cells` API: the sources are real `WebOfCells::publish` finalized reads, the
/// document is a real EDL, and `lineage`/`weaker_viewer` are the genuine
/// `SurfaceCapability`/`Membrane` the per-viewer `resolve_for` meets. The `!Send`
/// `WebOfCells` is owned here (so the reactive component holds the scenario in a
/// thread-local `StoredValue`, the same way [`crate::transclusion_demo`] holds its
/// constitution).
pub struct EelScenario {
    /// The real web-of-cells holding every source cell the document quotes.
    web: WebOfCells,
    /// The dreggverse document — the EDL of OWN + transcluded spans.
    doc: DreggverseDocument,
    /// The amendable source whose live update the sequence drives (the "constitution"
    /// of this scenario — the quote that tracks). The other sources stay fixed.
    amendable: DreggUri,
    /// The source-side lineage the document's transcluded spans are served under — the
    /// authority a viewer's membrane is met against (the common case: one publisher's
    /// docuverse). Permits every source span's origin.
    lineage: SurfaceCapability,
    /// A WEAKER viewer's membrane — scoped so it reaches every span EXCEPT the secret
    /// one (which darkens). The per-viewer half of the EEL: "you may not read this, but
    /// here is what it cites".
    weaker_viewer: Membrane,
}

/// The stable origin key for a raw-cell source span — the SAME key the document's
/// per-viewer gate ([`DreggverseDocument::resolve_for`]) checks the viewer's projected
/// fetch-allowlist against (via the public [`WebBundle::asset_origin`] with the
/// "(document)" raw-cell asset name). So scoping a viewer to exactly these origins
/// drives the GENUINE `SurfaceCapability::may_fetch` meet, never a parallel filter.
fn raw_span_origin(source: &DreggUri) -> String {
    WebBundle::asset_origin(source.cell, "(document)")
}

impl EelScenario {
    /// Build the worked scenario: a constitution-quote document that cites three real
    /// sources interleaved with the author's own prose, where a weaker viewer can read
    /// two of the three sources and the third DARKENS.
    ///
    /// The document (an honest little annotated constitution excerpt):
    ///   * OWN: `"The council adopts: \u{201c}"`
    ///   * QUOTE a range of the **preamble** source (the opening clause);
    ///   * OWN: `"\u{201d}, with quorum "`;
    ///   * QUOTE the whole of the **threshold** source (the amendable one — what the
    ///     live update tracks);
    ///   * OWN: `". The sealed annex reads: "`
    ///   * QUOTE a range of the **annex** source — the SECRET one a weaker viewer
    ///     cannot read (it darkens; its citation survives, its bytes withheld).
    ///   * OWN: `" [end]"`.
    pub fn worked() -> Self {
        let mut web = WebOfCells::new(3);

        // Three real source cells (genuine published finalized reads).
        let preamble = web.publish(
            0x51,
            b"We the council, to govern in the open, do ordain this charter.",
            "dregg://preamble",
        );
        let threshold = web.publish(0x52, b"quorum = 3 of 5", "dregg://threshold");
        let annex = web.publish(
            0x53,
            b"ANNEX: the sealed deliberations of the founding session, sub rosa.",
            "dregg://annex",
        );

        // The EDL — OWN prose interleaved with three transcluded spans.
        //
        // Preamble: bytes 0..53 = "We the council, to govern in the open, do ordain this"
        // (a clause of the source ending on a word — a real sub-span quote, NOT the
        // whole; the source continues " charter." after the highlight).
        let preamble_clause = SpanRange::new(0, 53);
        // Annex: bytes 7..56 = "the sealed deliberations of the founding session,"
        // (a clause within the secret source — what the weaker viewer is NOT allowed to
        // read; the source continues " sub rosa." after the would-be highlight).
        let annex_clause = SpanRange::new(7, 56);

        let doc = DreggverseDocument::from_spans(vec![
            Span::own(b"The council adopts: \xe2\x80\x9c".to_vec()),
            Span::transclude_range(preamble.clone(), preamble_clause),
            Span::own(b"\xe2\x80\x9d, with quorum ".to_vec()),
            Span::transclude(threshold.clone()),
            Span::own(b". The sealed annex reads: ".to_vec()),
            Span::transclude_range(annex.clone(), annex_clause),
            Span::own(b" [end]".to_vec()),
        ]);

        // The source-side lineage: permits ALL three sources' origins (one publisher's
        // docuverse). Either authority.
        let lineage = SurfaceCapability::scoped(
            preamble.cell,
            AuthRequired::Either,
            [
                raw_span_origin(&preamble),
                raw_span_origin(&threshold),
                raw_span_origin(&annex),
            ],
            [],
        );

        // The WEAKER viewer: scoped to the preamble + threshold origins ONLY — it can
        // read those two spans, but the annex span's origin is NOT in its allowlist, so
        // the membrane meet darkens it (the secret span). Either rights, finite fetch
        // allowlist.
        let weaker_viewer = Membrane::new(SurfaceCapability::scoped(
            // a fresh viewer cell id (distinct from the publisher's) — the same kind of
            // weaker-viewer the document tests build.
            web_cell_id(0x60),
            AuthRequired::Either,
            [raw_span_origin(&preamble), raw_span_origin(&threshold)],
            [],
        ));

        EelScenario {
            web,
            doc,
            amendable: threshold,
            lineage,
            weaker_viewer,
        }
    }

    /// Borrow the underlying web-of-cells (so a resolve reads the CURRENT committed
    /// source values).
    pub fn web(&self) -> &WebOfCells {
        &self.web
    }

    /// The document's EDL.
    pub fn document(&self) -> &DreggverseDocument {
        &self.doc
    }

    /// **Resolve the document at FULL authority** — every transcluded span its verified
    /// source bytes (the author's own view; nothing darkened). The genuine
    /// [`DreggverseDocument::resolve`].
    pub fn resolve_full(&self) -> RenderedDocument {
        self.doc
            .resolve(&self.web)
            .expect("the worked scenario's document resolves at full authority")
    }

    /// **Resolve the document for the WEAKER viewer** — through the genuine per-viewer
    /// membrane meet ([`DreggverseDocument::resolve_for`]). The span the viewer's
    /// projected fetch-allowlist does not permit DARKENS: its citation survives, its
    /// bytes withheld (never forged).
    pub fn resolve_weaker(&self) -> RenderedDocument {
        self.doc
            .resolve_for(&self.web, &self.weaker_viewer, &self.lineage)
            .expect("the worked scenario resolves for the weaker viewer (one span darkens)")
    }

    /// **Amend the amendable source** — fire a turn on the threshold cell (a genuine
    /// state advance through [`WebOfCells::amend`]; the `dregg://` ref is UNCHANGED).
    /// The next resolve shows the source's NEW value in that span — the unbreakable
    /// link, in the parallel view. Returns the advanced federation height.
    pub fn amend(&mut self, new_threshold_text: &[u8]) -> u64 {
        self.web
            .amend(&self.amendable, new_threshold_text)
            .expect("the founded threshold source can be amended")
    }

    /// The amendable source's `dregg://` reference (the threshold cell the live update
    /// tracks).
    pub fn amendable(&self) -> &DreggUri {
        &self.amendable
    }
}

/// A content-addressed cell id from a seed byte — the same derivation the
/// `deos-web-cells` document tests use for a fresh viewer/source cell (so the scoped
/// viewer's window cell is the genuine [`deos_web_cells::CellId`]).
fn web_cell_id(seed: u8) -> deos_web_cells::CellId {
    let mut k = [0u8; 32];
    k[0] = seed;
    deos_web_cells::CellId::derive_raw(&k, &[0u8; 32])
}

// ════════════════════════════════════════════════════════════════════════════
// THE ROW PROJECTION — per EDL span, the parallel-source row: the document text it
// contributes, and (for a quote) its SOURCE cell's full bytes with the quoted range
// marked + the jump anchor + the darkened bit. Computed from the REAL source_link.
// ════════════════════════════════════════════════════════════════════════════

/// One **EEL row** — the parallel-source projection of a single rendered span: the
/// LEFT-column document text it contributes, and (when it is a quote) the RIGHT-column
/// source cell with the quoted range located.
///
/// This is the data the side-by-side view renders, drawn from the genuine
/// [`RenderedSpan`]: the document text from [`RenderedSpan::bytes`], the source anchor
/// from [`RenderedSpan::source_link`], and the source's FULL committed bytes re-read
/// through the REAL [`TranscludedField::include`] (so the right column shows the WHOLE
/// cited cell, with the quoted byte range highlit — Nelson's "see the quote in its
/// home"). A DARKENED row carries its citation but NO source bytes (the viewer lacks
/// authority): the right column shows the honest withholding, never the source value.
#[derive(Clone, Debug)]
pub struct EelRow {
    /// The EDL span index (the `N` the `#eel-src-N` jump anchor keys on).
    pub index: usize,
    /// The document text this span contributes to the LEFT column. OWN content verbatim;
    /// a quote's cited-range bytes; a DARKENED span contributes nothing (empty).
    pub document_text: String,
    /// The parallel-source detail — `None` for an OWN span (no foreign source), `Some`
    /// for a quote (transcluded OR darkened).
    pub source: Option<EelSource>,
}

/// The RIGHT-column source detail of a quoting [`EelRow`] — the cited source cell, with
/// the quoted byte range located so the view can highlight it (or, when darkened, the
/// citation-only withholding).
#[derive(Clone, Debug)]
pub struct EelSource {
    /// The source `dregg://<cell>` the span quotes FROM (the jump-to-source target).
    pub uri: DreggUri,
    /// The byte range within the source the span selected (the EDL's "range r").
    pub range: SpanRange,
    /// The cited receipt prefix (first 4 bytes hex) — the honest, dated provenance the
    /// view shows under the source.
    pub receipt_prefix: String,
    /// Whether the cited source's read carried quorum at the cited point (the
    /// `finalized` flag).
    pub finalized: bool,
    /// Whether this row DARKENED — the viewer lacks authority to read the source. When
    /// `true`, `full_source` is `None` (NO source bytes) and the view shows the
    /// citation-preserved withholding.
    pub darkened: bool,
    /// The source cell's FULL committed bytes (so the right column shows the WHOLE cell
    /// with the quoted range highlit) — `None` for a DARKENED row (the bytes are
    /// withheld: never the source value the viewer lacks). UTF-8 lossy for display.
    pub full_source: Option<FullSource>,
}

/// A source cell's full committed content, split at the quoted range so the view can
/// wrap the middle in a highlight. All three parts are UTF-8-lossy strings (for the
/// text-document display path).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FullSource {
    /// The source bytes BEFORE the quoted range (rendered plain).
    pub before: String,
    /// The quoted range itself (rendered highlighted — the `<mark>`).
    pub quoted: String,
    /// The source bytes AFTER the quoted range (rendered plain).
    pub after: String,
}

impl EelSource {
    /// The provenance line the view shows under a source row — the dated citation: the
    /// source ref, the quoted range, the receipt prefix, finalized.
    pub fn provenance_line(&self) -> String {
        format!(
            "{} · bytes {}..{} · receipt {}\u{2026} · {}",
            self.uri.to_uri_string(),
            self.range.start,
            range_end_label(self.range),
            self.receipt_prefix,
            if self.finalized {
                "finalized"
            } else {
                "UNATTESTED"
            },
        )
    }
}

/// A human label for a span range's end — the concrete byte for a bounded range, or
/// `"end"` for the whole-source sentinel ([`usize::MAX`]).
fn range_end_label(range: SpanRange) -> String {
    if range.end == usize::MAX {
        "end".to_string()
    } else {
        range.end.to_string()
    }
}

/// The first 4 bytes of a receipt hash as a hex prefix (the short, dated citation token
/// the view shows — matching the `transclusion_demo` provenance-line style).
fn receipt_prefix(p: &Provenance) -> String {
    let r = p.receipt_hash;
    format!("{:02x}{:02x}{:02x}{:02x}", r[0], r[1], r[2], r[3])
}

/// Build the parallel-source ROWS for a resolved document against its web-of-cells —
/// the per-span EEL projection the side-by-side view renders.
///
/// For each rendered span:
///   * OWN content → an [`EelRow`] with the verbatim document text, no source;
///   * a TRANSCLUDED quote → the cited-range document text PLUS the source detail: the
///     `source_link` anchor, the provenance, and the source cell's FULL bytes (re-read
///     through the REAL [`TranscludedField::include`]) split at the quoted range so the
///     right column highlights it;
///   * a DARKENED quote → empty document text PLUS the citation-only source detail (NO
///     source bytes — the viewer lacks authority; the citation survives).
///
/// `web` is the live web-of-cells the sources are read from (so the right column shows
/// the CURRENT committed source — amend a source, the highlighted range tracks).
pub fn eel_rows(rendered: &RenderedDocument, web: &WebOfCells) -> Vec<EelRow> {
    rendered
        .spans()
        .iter()
        .enumerate()
        .map(|(index, span)| eel_row(index, span, web))
        .collect()
}

/// Project one rendered span into its [`EelRow`].
fn eel_row(index: usize, span: &RenderedSpan, web: &WebOfCells) -> EelRow {
    // The LEFT-column text this span contributes (lossy UTF-8 for display).
    let document_text = String::from_utf8_lossy(span.bytes()).into_owned();

    // The parallel-source detail — only quotes (transcluded/darkened) carry one. OWN
    // content has `source_link() == None`, so `source` is `None`.
    let source = span.source_link().map(|(uri, range)| {
        let darkened = span.is_darkened();
        // The citation the span carries (transcluded OR darkened both keep provenance).
        let prov = span
            .provenance()
            .expect("a span with a source_link carries provenance");
        let receipt = receipt_prefix(prov);
        let finalized = prov.finalized;

        // The RIGHT-column source bytes. For a DARKENED row we must NOT read them (the
        // viewer lacks authority) — `None`. For a readable quote, re-read the source's
        // FULL committed bytes through the REAL verified read, and split at the quoted
        // range so the view highlights it. (The span itself only carries the cited
        // RANGE bytes; the right column wants the WHOLE cell to show the quote in its
        // home — so we read the source whole here, the genuine finalized read.)
        let full_source = if darkened {
            None
        } else {
            Some(full_source_split(&uri, range, web))
        };

        EelSource {
            uri,
            range,
            receipt_prefix: receipt,
            finalized,
            darkened,
            full_source,
        }
    });

    EelRow {
        index,
        document_text,
        source,
    }
}

/// Read a source cell's FULL committed bytes (the REAL [`TranscludedField::include`])
/// and split them at the quoted `range` into (before, quoted, after) — so the source
/// column renders the WHOLE cell with the quoted range highlighted in place.
///
/// The split uses the SAME clamping [`SpanRange::select`] uses (a range past the end
/// highlights only what exists; it never reads outside the source). The bytes ARE the
/// source's verified committed bytes (content-addressed via the finalized read), not a
/// copy.
fn full_source_split(uri: &DreggUri, range: SpanRange, web: &WebOfCells) -> FullSource {
    // THE REAL VERIFIED CROSS-CELL READ — the full source bytes, content-addressed +
    // provenance-verified. (A readable row already verified at resolve; this reads the
    // SAME source whole for the side-by-side display.)
    let field = TranscludedField::include(web, uri)
        .expect("a readable source row's source resolves the verified full read");
    let content = field.quoted_bytes();
    let len = content.len();
    let start = range.start.min(len);
    let end = range.end.min(len);
    let (start, end) = if start >= end {
        (start, start)
    } else {
        (start, end)
    };

    FullSource {
        before: String::from_utf8_lossy(&content[..start]).into_owned(),
        quoted: String::from_utf8_lossy(&content[start..end]).into_owned(),
        after: String::from_utf8_lossy(&content[end..]).into_owned(),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// THE SSR TWO-COLUMN RENDER — the document column (each quote a jump link) beside the
// source column (each source cell, the quoted range marked, with the jump target).
// ════════════════════════════════════════════════════════════════════════════

/// Escape the HTML-special characters so source/document text renders as TEXT (never as
/// markup) in the columns — the minimal, correct escape for the SSR string output.
fn esc(s: &str) -> String {
    // Single pass into a pre-sized buffer (was four sequential `.replace` passes,
    // each allocating a fresh String). Result-identical escaping.
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            _ => out.push(c),
        }
    }
    out
}

/// **`render_parallel_source_view`** — render the EEL (parallel source view) for a
/// resolved document to a two-column HTML string: the **document column** (the composed
/// text, each quote an `<a href="#eel-src-N">` jump link) beside the **source column**
/// (each cited source cell, the quoted byte range wrapped in `<mark>`, anchored at the
/// matching `id="eel-src-N"` jump target).
///
/// A DARKENED row renders its **citation** in the source column with the honest line
/// *"you may not read this, but here is what it cites"* — the source's bytes withheld
/// (never forged, never substituted), the document column showing nothing for that span.
///
/// `caption` is the per-render header (e.g. the viewer + the source height). The render
/// runs under a fresh reactive [`Owner`] (as the council/transclusion SSR renders do —
/// even a static render allocates reactive nodes).
pub fn render_parallel_source_view(
    rendered: &RenderedDocument,
    web: &WebOfCells,
    caption: &str,
) -> String {
    let rows = eel_rows(rendered, web);

    // ── The LEFT (document) column: the composed text, each quote a jump <a>. ──
    let mut document_col = String::new();
    for row in &rows {
        match &row.source {
            None => {
                // OWN content — verbatim text, no anchor.
                document_col.push_str(&format!(
                    "<span class=\"eel-own\">{}</span>",
                    esc(&row.document_text)
                ));
            }
            Some(src) if src.darkened => {
                // A darkened quote contributes NO document text; render a small,
                // citation-bearing placeholder that still JUMPS to the (citation-only)
                // source row — "here is what it cites", even unreadable.
                document_col.push_str(&format!(
                    "<a class=\"eel-quote eel-darkened\" href=\"#eel-src-{idx}\" \
                     title=\"darkened — quoted from {uri}\">\u{25af} [darkened quote \u{2192} \
                     {uri}]</a>",
                    idx = row.index,
                    uri = esc(&src.uri.to_uri_string()),
                ));
            }
            Some(src) => {
                // A readable quote — the cited-range text, as a jump link to its source.
                document_col.push_str(&format!(
                    "<a class=\"eel-quote\" href=\"#eel-src-{idx}\" \
                     title=\"jump to source {uri}\">{text}</a>",
                    idx = row.index,
                    uri = esc(&src.uri.to_uri_string()),
                    text = esc(&row.document_text),
                ));
            }
        }
    }

    // ── The RIGHT (source) column: one block per QUOTE row (OWN rows have no source). ──
    let mut source_col = String::new();
    for row in &rows {
        let Some(src) = &row.source else { continue };
        if src.darkened {
            // DARKENED: the citation survives, the bytes are withheld. The honest line.
            source_col.push_str(&format!(
                "<div class=\"eel-source eel-darkened\" id=\"eel-src-{idx}\">\
                   <p class=\"eel-cite\">{cite}</p>\
                   <p class=\"eel-withheld\">\u{1f512} you may not read this, but here is \
                    what it cites.</p>\
                 </div>",
                idx = row.index,
                cite = esc(&src.provenance_line()),
            ));
        } else {
            // READABLE: the WHOLE source cell, the quoted range wrapped in <mark>.
            let fs = src
                .full_source
                .as_ref()
                .expect("a readable source row carries its full bytes");
            source_col.push_str(&format!(
                "<div class=\"eel-source\" id=\"eel-src-{idx}\">\
                   <p class=\"eel-cite\">{cite}</p>\
                   <pre class=\"eel-source-body\">{before}<mark class=\"eel-mark\">{quoted}\
                    </mark>{after}</pre>\
                 </div>",
                idx = row.index,
                cite = esc(&src.provenance_line()),
                before = esc(&fs.before),
                quoted = esc(&fs.quoted),
                after = esc(&fs.after),
            ));
        }
    }

    let composed = esc(&rendered.composed_text().unwrap_or_default());
    let darkened = rendered.darkened_count();

    let owner = Owner::new();
    owner.with(move || {
        let view = view! {
            <section class="deos-eel" role="region" aria-label="parallel source view">
                <header class="eel-caption">{caption.to_string()}</header>
                <div class="eel-columns">
                    // THE DOCUMENT COLUMN — the composed document, quotes as jump links.
                    <div class="eel-document-column">
                        <h3>"document"</h3>
                        <div class="eel-document" inner_html=document_col></div>
                        <p class="eel-composed">
                            "composed: \u{201c}"{composed}"\u{201d}"
                        </p>
                    </div>
                    // THE SOURCE COLUMN — each cited cell, the quoted range highlit, the
                    // jump targets. Darkened sources show the citation-only withholding.
                    <div class="eel-source-column">
                        <h3>"sources (jump-to-source)"</h3>
                        <div class="eel-sources" inner_html=source_col></div>
                    </div>
                </div>
                <footer class="eel-footer">
                    {format!("{darkened} span(s) darkened (citation preserved, bytes withheld)")}
                </footer>
            </section>
        };
        view.to_html()
    })
}

// ════════════════════════════════════════════════════════════════════════════
// THE REACTIVE COMPONENT — the scenario lives thread-local; a source-height RwSignal
// is the trigger; a Memo re-resolves resolve_for so the highlighted range tracks LIVE.
// ════════════════════════════════════════════════════════════════════════════

/// **`ParallelSourceView`** — the EEL component in the Leptos runtime (the reactive
/// parallel source view).
///
/// The reactive shape mirrors [`crate::transclusion_demo::CouncilTransclusionView`]:
///   * the [`EelScenario`] (a real `WebOfCells` + the document — `!Send`, holds a real
///     ledger) lives in a thread-local [`StoredValue`] (`new_local`), its right home for
///     the single-threaded SSR request;
///   * a `source_height` [`RwSignal`] is the reactive trigger — the "amend source"
///     button bumps it after advancing the threshold source;
///   * the **view [`Memo`]** re-resolves the document (`resolve_full` or `resolve_weaker`,
///     per the `as_weaker_viewer` prop) and re-renders the two-column HTML whenever
///     `source_height` changes — so the highlighted range in the source column tracks
///     the amended source LIVE. The unbreakable link, in the parallel view.
///
/// Pressing "amend source (advance threshold)" advances the threshold source (a genuine
/// state advance) and bumps `source_height` → the Memo re-resolves + re-renders → the
/// source column's `<mark>` shows the NEW committed value. In a hydrate build the amend
/// is a server-fn POST (the resolve runs server-side atop native crypto — the deos
/// seam); here the body runs inline so the SSR render + tests exercise the REAL read.
#[component]
pub fn ParallelSourceView(
    /// Render for the WEAKER viewer (one span darkens) when `true`; for the full-
    /// authority author (nothing darkens) when `false`.
    as_weaker_viewer: bool,
) -> impl IntoView {
    // The scenario (a real web-of-cells + document) lives thread-local — it is `!Send`
    // (holds a real ledger), and an SSR request is single-threaded.
    let scenario = StoredValue::new_local(EelScenario::worked());

    // The reactive TRIGGER: the threshold source's current attested height. The amend
    // handler bumps it; the view Memo re-resolves + re-renders. Seeded to the founded
    // height (3 — three publishes each advanced the federation height once).
    let source_height = RwSignal::new(3u64);

    // THE EEL VIEW MEMO — re-resolves the document (per-viewer or full) and re-renders
    // the two-column HTML whenever `source_height` changes. THIS is the live parallel
    // view: the highlighted range tracks the source's committed value, reactively,
    // through the verified read.
    let html = Memo::new(move |_| {
        let h = source_height.get();
        scenario.with_value(|s| {
            let rendered = if as_weaker_viewer {
                s.resolve_weaker()
            } else {
                s.resolve_full()
            };
            let caption = format!(
                "{} · threshold source @ height {}",
                if as_weaker_viewer {
                    "weaker viewer (one span darkened)"
                } else {
                    "full authority (author's view)"
                },
                h
            );
            render_parallel_source_view(&rendered, s.web(), &caption)
        })
    });

    // The AMEND handler — the SOURCE's turn. Advance the threshold source (a genuine
    // state advance through the real `WebOfCells::amend`) and bump `source_height` so
    // the view Memo re-resolves to the NEW value. The new quorum text bumps the count.
    let on_amend = move || {
        let advanced = scenario.try_update_value(|s| {
            // Read the current threshold text to compute the next (a visible jump,
            // e.g. "quorum = 3 of 5" → "quorum = 4 of 5").
            let next = next_quorum_text(s);
            s.amend(next.as_bytes())
        });
        // `try_update_value` returns the closure's value (the advanced height) iff the
        // thread-local store was reachable.
        if let Some(h) = advanced {
            source_height.set(h);
        }
    };

    view! {
        <div class="deos-eel-reactive">
            // The two-column parallel source view (re-rendered on every amend).
            <div inner_html=move || html.get()></div>
            // THE PAYOFF BUTTON — amend the source; the highlighted range tracks.
            <button class="eel-amend" on:click=move |_| on_amend()>
                "amend source (advance threshold)"
            </button>
        </div>
    }
}

/// Compute the next quorum text for the amendable threshold source — read its current
/// committed value and bump the quorum count by one (e.g. `"quorum = 3 of 5"` →
/// `"quorum = 4 of 5"`). Fail-soft: an unreadable/unexpected source falls back to a
/// fresh `"quorum = 4 of 5"` (the demo never wedges on a parse).
fn next_quorum_text(scenario: &EelScenario) -> String {
    let cur = TranscludedField::include(scenario.web(), scenario.amendable())
        .ok()
        .map(|f| String::from_utf8_lossy(f.quoted_bytes()).into_owned())
        .unwrap_or_default();
    // Parse "quorum = N of M" and bump N (clamped at M).
    if let Some((n, m)) = parse_quorum(&cur) {
        let next_n = (n + 1).min(m);
        format!("quorum = {next_n} of {m}")
    } else {
        "quorum = 4 of 5".to_string()
    }
}

/// Parse `"quorum = N of M"` into `(N, M)` — the threshold source's committed shape.
fn parse_quorum(s: &str) -> Option<(u64, u64)> {
    let rest = s.trim().strip_prefix("quorum = ")?;
    let (n_str, m_str) = rest.split_once(" of ")?;
    Some((n_str.trim().parse().ok()?, m_str.trim().parse().ok()?))
}

// ════════════════════════════════════════════════════════════════════════════
// THE HEADLESS SEQUENCE — the demo's PROOF: render the parallel view → amend a source
// → re-render, showing the highlighted range track the source. The binary + the tests
// both drive this (the runnable demo and the proof are the SAME path).
// ════════════════════════════════════════════════════════════════════════════

/// One step of the EEL sequence — the parallel source view rendered at a moment,
/// carrying the threshold value the highlighted source showed + its provenance height.
#[derive(Clone, Debug)]
pub struct EelStep {
    /// A human label (e.g. `"founded"`, `"after amend #1"`).
    pub label: String,
    /// The threshold source's committed text at this step (what the source column's
    /// `<mark>` highlit for the threshold quote).
    pub threshold_text: String,
    /// The threshold source's provenance height at this step.
    pub height: u64,
    /// How many spans darkened (the weaker viewer's withheld count; 0 at full
    /// authority).
    pub darkened: usize,
    /// The rendered FULL-authority parallel source view HTML.
    pub full_html: String,
    /// The rendered WEAKER-viewer parallel source view HTML (one span darkened).
    pub weaker_html: String,
}

/// **`eel_sequence`** — drive the reactive parallel source view end to end and return
/// the steps (the demo's proof). Builds the worked scenario, renders BOTH the full-
/// authority and weaker-viewer parallel views (step 0), then AMENDS the threshold source
/// `amendments` times, re-rendering after each — proving the highlighted source range
/// tracks the source REACTIVELY: each step's `threshold_text` is the source's NEW
/// committed value and its `height` advances.
///
/// This is exactly what [`ParallelSourceView`]'s view `Memo` recomputes when its
/// `source_height` trigger is bumped — the headless form of the in-browser live update,
/// in the EEL.
pub fn eel_sequence(amendments: usize) -> Vec<EelStep> {
    let mut scenario = EelScenario::worked();
    let mut steps = Vec::with_capacity(amendments + 1);

    // STEP 0 — the founded scenario, freshly rendered (both viewers).
    let founded_height = 3; // three publishes advanced the attested height to 3.
    steps.push(render_step(&scenario, "founded", founded_height));

    // EACH AMENDMENT — the source's turn; the threshold quote (and its highlight)
    // re-resolves to the NEW value at the NEW height (the live update, in the EEL).
    for i in 0..amendments {
        let next = next_quorum_text(&scenario);
        let new_height = scenario.amend(next.as_bytes());
        let label = format!("after amend #{}", i + 1);
        steps.push(render_step(&scenario, &label, new_height));
    }

    steps
}

/// Render one sequence step (both the full + weaker parallel views) against the live
/// scenario.
fn render_step(scenario: &EelScenario, label: &str, height: u64) -> EelStep {
    // The threshold source's current committed text (what the highlight shows).
    let threshold_text = TranscludedField::include(scenario.web(), scenario.amendable())
        .map(|f| String::from_utf8_lossy(f.quoted_bytes()).into_owned())
        .unwrap_or_default();

    let full = scenario.resolve_full();
    let weaker = scenario.resolve_weaker();
    let darkened = weaker.darkened_count();

    let full_html = render_parallel_source_view(
        &full,
        scenario.web(),
        &format!("full authority (author's view) · threshold @ height {height}"),
    );
    let weaker_html = render_parallel_source_view(
        &weaker,
        scenario.web(),
        &format!("weaker viewer (one span darkened) · threshold @ height {height}"),
    );

    EelStep {
        label: label.to_string(),
        threshold_text,
        height,
        darkened,
        full_html,
        weaker_html,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── (1) THE PARALLEL-SOURCE ROWS: per span, the document text + (for a quote) the
    //        source cell, the quoted range located, the jump anchor, the darkened bit. ──

    #[test]
    fn eel_rows_project_each_span_to_its_parallel_source() {
        let scenario = EelScenario::worked();
        let rendered = scenario.resolve_full();
        let rows = eel_rows(&rendered, scenario.web());

        // 7 EDL spans → 7 rows (4 OWN + 3 quotes).
        assert_eq!(rows.len(), 7, "one row per EDL span");

        // Row 0 (OWN) carries document text, NO source.
        assert!(
            rows[0].source.is_none(),
            "OWN content has no parallel source"
        );
        assert!(rows[0].document_text.contains("The council adopts"));

        // Row 1 (the preamble quote) carries the cited-range text + the source detail.
        let preamble = rows[1]
            .source
            .as_ref()
            .expect("the preamble quote has a source");
        assert!(
            !preamble.darkened,
            "the preamble is readable at full authority"
        );
        assert_eq!(preamble.range, SpanRange::new(0, 53));
        assert!(preamble.uri.to_uri_string().contains("dregg://"));
        assert!(
            preamble.finalized,
            "a published+attested source is finalized"
        );
        // The cited-range document text is the FIRST 53 bytes of the preamble source.
        assert_eq!(
            rows[1].document_text,
            "We the council, to govern in the open, do ordain this"
        );

        // The source column shows the WHOLE preamble cell, split at the quoted range —
        // the quoted part equals the document text, and there are bytes AFTER it.
        let fs = preamble
            .full_source
            .as_ref()
            .expect("a readable quote carries full bytes");
        assert_eq!(
            fs.quoted, rows[1].document_text,
            "the highlighted range IS the quote"
        );
        assert_eq!(fs.before, "", "the preamble quote starts at byte 0");
        assert!(
            fs.after.contains("charter"),
            "the rest of the source follows the highlight"
        );

        // Row 3 (the threshold quote — the whole source) shows the full committed value.
        let threshold = rows[3]
            .source
            .as_ref()
            .expect("the threshold quote has a source");
        assert_eq!(
            rows[3].document_text, "quorum = 3 of 5",
            "the whole threshold source"
        );
        let tfs = threshold.full_source.as_ref().unwrap();
        assert_eq!(tfs.quoted, "quorum = 3 of 5");
        assert_eq!(tfs.after, "", "a whole-source quote highlights to the end");
    }

    // ── (2) THE SSR TWO-COLUMN RENDER: the document column with jump <a>s + the source
    //        column with the quoted range <mark>ed + the matching jump targets. ──

    #[test]
    fn render_parallel_source_view_has_columns_marks_and_jump_anchors() {
        let scenario = EelScenario::worked();
        let rendered = scenario.resolve_full();
        let html = render_parallel_source_view(&rendered, scenario.web(), "test caption");

        // The two columns are present.
        assert!(
            html.contains("eel-document-column"),
            "the document column renders"
        );
        assert!(
            html.contains("eel-source-column"),
            "the source column renders"
        );

        // The quoted range is HIGHLIGHTED in the source column (the <mark>).
        assert!(
            html.contains("<mark"),
            "the quoted range is marked in the source"
        );
        assert!(
            html.contains("We the council, to govern in the open, do ordain this"),
            "the highlighted preamble clause appears in the source column: {html}"
        );

        // THE JUMP-TO-SOURCE ANCHOR WORKS: the document column's quote links to
        // #eel-src-1, and the source column has the matching id="eel-src-1" target.
        assert!(
            html.contains("href=\"#eel-src-1\""),
            "the preamble quote is a jump link to its source: {html}"
        );
        assert!(
            html.contains("id=\"eel-src-1\""),
            "the source column has the matching jump target: {html}"
        );
        // The threshold quote (span 3) likewise jumps + targets.
        assert!(html.contains("href=\"#eel-src-3\""));
        assert!(html.contains("id=\"eel-src-3\""));

        // The OWN content renders as plain document text (no source block, no mark for
        // it) — it is in the document column.
        assert!(html.contains("The council adopts"));
        // Full authority darkened nothing.
        assert!(html.contains("0 span(s) darkened"));
    }

    // ── (3) THE DARKENED CASE, CITATION PRESERVED: a weaker viewer sees the secret span
    //        as a darkened citation — "you may not read this, but here is what it cites"
    //        — its source bytes NEVER shown, but the jump anchor + citation survive. ──

    #[test]
    fn darkened_span_shows_citation_not_source_bytes_in_the_parallel_view() {
        let scenario = EelScenario::worked();
        let rendered = scenario.resolve_weaker();

        // Exactly one span darkened (the annex), through the REAL membrane meet.
        assert_eq!(
            rendered.darkened_count(),
            1,
            "the weaker viewer darkens the annex span"
        );

        let rows = eel_rows(&rendered, scenario.web());
        // The annex quote is span 5 — darkened, NO full source bytes, citation kept.
        let annex = rows[5]
            .source
            .as_ref()
            .expect("the annex row still carries its citation");
        assert!(
            annex.darkened,
            "the annex span darkened for the weaker viewer"
        );
        assert!(
            annex.full_source.is_none(),
            "a darkened row reads NO source bytes"
        );
        assert!(
            annex.finalized,
            "the darkened span's citation is still finalized"
        );
        // The document column contributes nothing for the darkened span.
        assert_eq!(
            rows[5].document_text, "",
            "a darkened span yields no document text"
        );
        // …but the jump anchor (source_link) survives — you can still navigate to what
        // it cites.
        assert!(annex.uri.to_uri_string().contains("dregg://"));

        // The RENDER: the darkened source block shows the honest withholding line + the
        // citation, and NEVER the secret source bytes.
        let html = render_parallel_source_view(&rendered, scenario.web(), "weaker viewer");
        assert!(
            html.contains("you may not read this, but here is what it cites"),
            "the darkened source shows the honest withholding line: {html}"
        );
        assert!(
            html.contains("eel-darkened"),
            "the darkened row is marked as such"
        );
        // The citation (source ref) survives in the darkened block.
        assert!(
            html.contains("id=\"eel-src-5\""),
            "the darkened source has its jump target"
        );
        // THE ANTI-FORGE TOOTH: the secret annex bytes NEVER appear (not the value, not a
        // forgery) — the viewer sees the citation, not the bytes it lacks authority for.
        assert!(
            !html.contains("sealed deliberations"),
            "the weaker viewer NEVER sees the secret source bytes: {html}"
        );
        // The two readable quotes (preamble, threshold) still render their source bytes.
        assert!(
            html.contains("We the council"),
            "the readable preamble still shows"
        );
        assert!(
            html.contains("quorum = 3 of 5"),
            "the readable threshold still shows"
        );
    }

    // ── (4) THE LIVE UPDATE, IN THE PARALLEL VIEW: amend the threshold source → the
    //        highlighted range in the source column tracks the NEW value (not stale),
    //        the provenance height advances; every other span (and the darkened annex)
    //        untouched. The EEL's unbreakable link. ──

    #[test]
    fn eel_sequence_tracks_the_amended_source_in_the_highlight() {
        let steps = eel_sequence(2);
        assert_eq!(steps.len(), 3, "founded + 2 amendments");

        // Step 0: the founded threshold "quorum = 3 of 5".
        assert_eq!(steps[0].threshold_text, "quorum = 3 of 5");
        assert!(
            steps[0].full_html.contains("quorum = 3 of 5"),
            "the founded highlight shows quorum 3"
        );
        // Step 1: amended to "quorum = 4 of 5" — the highlight tracks the NEW value.
        assert_eq!(steps[1].threshold_text, "quorum = 4 of 5");
        assert!(
            steps[1].full_html.contains("quorum = 4 of 5"),
            "the highlight tracked the amended quorum: {}",
            steps[1].full_html
        );
        assert!(
            !steps[1].full_html.contains("quorum = 3 of 5"),
            "the parallel view is NOT stale (no quorum 3 after the amend)"
        );
        // Step 2: amended to "quorum = 5 of 5" (clamped at M).
        assert_eq!(steps[2].threshold_text, "quorum = 5 of 5");
        assert!(steps[2].full_html.contains("quorum = 5 of 5"));

        // The provenance HEIGHT advances strictly across the live updates (a stale quote
        // is visible; supersession is dated, never a silent live read).
        assert!(
            steps[0].height < steps[1].height && steps[1].height < steps[2].height,
            "provenance heights advance: {} < {} < {}",
            steps[0].height,
            steps[1].height,
            steps[2].height
        );

        // The weaker viewer keeps darkening exactly the annex across the updates — the
        // amend touched only the threshold span; the darkened annex stays withheld.
        for step in &steps {
            assert_eq!(
                step.darkened, 1,
                "the weaker viewer darkens the annex at every step"
            );
            assert!(
                !step.weaker_html.contains("sealed deliberations"),
                "the weaker viewer never sees the secret bytes, at any step"
            );
            // …and the threshold quote still tracks for the weaker viewer too (it CAN
            // read that one).
            assert!(
                step.weaker_html.contains(&step.threshold_text),
                "the weaker viewer's readable threshold tracked: {}",
                step.threshold_text
            );
        }
    }

    // ── (5) THE PRESERVED PRINCIPLE: the OTHER readable spans are byte-identical across
    //        an amend of the threshold (the unbreakable link touches only its span). ──

    #[test]
    fn amending_the_threshold_leaves_the_preamble_span_untouched() {
        let mut scenario = EelScenario::worked();
        let r0 = scenario.resolve_full();
        let rows0 = eel_rows(&r0, scenario.web());
        let preamble0 = rows0[1].document_text.clone();
        let preamble_receipt0 = rows0[1].source.as_ref().unwrap().receipt_prefix.clone();

        // Amend the threshold (a different span's source).
        scenario.amend(b"quorum = 4 of 5");
        let r1 = scenario.resolve_full();
        let rows1 = eel_rows(&r1, scenario.web());

        // The preamble span is byte-identical AND cites the SAME receipt — amending the
        // threshold touched only the threshold span.
        assert_eq!(
            rows1[1].document_text, preamble0,
            "the preamble text is unchanged"
        );
        assert_eq!(
            rows1[1].source.as_ref().unwrap().receipt_prefix,
            preamble_receipt0,
            "the preamble's citation is unchanged (the amend touched only the threshold)"
        );
        // The threshold span DID advance.
        assert_eq!(
            rows1[3].document_text, "quorum = 4 of 5",
            "the threshold span tracked"
        );
    }

    // ── SSR sanity: the reactive component renders the parallel source view on the
    //    native (gate-linkable) target, for both the full + weaker viewer. ──

    #[test]
    fn ssr_parallel_source_view_component_renders_both_viewers() {
        // Full authority — nothing darkened, the amend button present.
        let owner = Owner::new();
        let full_html =
            owner.with(|| view! { <ParallelSourceView as_weaker_viewer=false /> }.to_html());
        assert!(full_html.contains("deos-eel"), "the EEL view rendered");
        assert!(
            full_html.contains("<mark"),
            "the quoted range is highlighted"
        );
        assert!(
            full_html.contains("href=\"#eel-src-1\""),
            "the jump anchor renders"
        );
        assert!(
            full_html.contains("eel-amend"),
            "the amend payoff button renders"
        );
        assert!(
            full_html.contains("0 span(s) darkened"),
            "full authority darkens nothing"
        );

        // Weaker viewer — one span darkened, the withholding line present, the secret
        // bytes absent.
        let owner2 = Owner::new();
        let weaker_html =
            owner2.with(|| view! { <ParallelSourceView as_weaker_viewer=true /> }.to_html());
        assert!(
            weaker_html.contains("1 span(s) darkened"),
            "the weaker viewer darkens one span: {weaker_html}"
        );
        assert!(
            weaker_html.contains("you may not read this, but here is what it cites"),
            "the darkened-citation line renders for the weaker viewer"
        );
        assert!(
            !weaker_html.contains("sealed deliberations"),
            "the secret bytes never render for the weaker viewer"
        );
    }
}
