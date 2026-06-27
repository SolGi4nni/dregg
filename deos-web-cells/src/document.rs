//! The **dreggverse document** — Xanadu's *actual* document model, made honest on
//! the verified substrate: a document is not a file, it is an **EDL** (an
//! edit-decision-list) — an ordered list of **spans**, each either OWN authored
//! content or a **transcluded span of another cell** (cell X, byte range r).
//!
//! `starbridge_web_surface::transclusion` already ships Nelson's *quote* (a verified
//! cross-cell finalized read carrying receipt-pinned [`Provenance`]); this module
//! NAMES that quote as the unit an authored document is *composed from*. The
//! distinction Nelson actually drew (and Xanadu never made honest):
//!
//! - a **link** points AT a thing;
//! - a **document** is *built out of* transcluded spans — the same bytes, the same
//!   source, visibly cited, never copied — joined edge-to-edge with the author's own
//!   content. The EDL *is* the document: change the EDL, you re-author; change a
//!   SOURCE, the quoted span updates live (the unbreakable link), and the rest of
//!   the document is untouched.
//!
//! What dregg makes honest, that ambient-authority Xanadu could not:
//!
//! 1. **A transcluded span IS a verified observation** — [`DreggverseDocument::resolve`]
//!    runs the REAL [`TranscludedField::include`] per transcluded span (the genuine
//!    `dregg://` attested finalized read + the
//!    `content→commitment→receipt→receipt-stream-root→quorum` chain), then selects the
//!    span's byte range of the source's *committed* bytes. The rendered span IS the
//!    source's value, at a cited, immutable receipt — not a copy that may diverge.
//! 2. **Per-span provenance** — every transcluded span in the [`RenderedDocument`]
//!    carries its own receipt-pinned [`Provenance`] (the source ref + content
//!    commitment + cited receipt + finalized). The document is a *bibliography that
//!    renders*: each quoted span is dated and recomputable.
//! 3. **The unbreakable link** — amending a SOURCE (the REAL
//!    [`starbridge_web_surface::WebOfCells::amend`]) makes that span re-resolve to the
//!    source's NEW finalized value on the next [`DreggverseDocument::resolve`], with a
//!    NEW cited receipt — every other span untouched. The citation never rots; the
//!    quote tracks the source.
//! 4. **Per-viewer, no forgery** — [`DreggverseDocument::resolve_for`] resolves the
//!    document THROUGH a viewer's [`Membrane`]: a transcluded span the viewer's
//!    projection cannot reach (an incomparable identity, or a source the viewer's
//!    projected fetch-allowlist does not permit) is **darkened** — rendered as an
//!    opaque, provenance-stamped placeholder — NEVER forged and never the source
//!    value the viewer lacks. A weaker viewer sees the document's SHAPE (which spans
//!    exist, cited) without the bytes it has no authority to read. This is the REAL
//!    [`Membrane::project`] + [`SurfaceCapability::may_fetch`] meet, per span — never a
//!    parallel filter.
//!
//! Everything load-bearing is the genuine machinery: the include is the REAL verified
//! cross-cell finalized read; the provenance is the REAL receipt-pinned citation; the
//! per-viewer darkening is the REAL membrane projection. This module composes them
//! into an authored artifact; it invents no fetch, no attestation, no membrane.
//!
//! ## The EEL / parallel-source view (the named UX follow-on)
//!
//! A [`RenderedDocument`] is the composed text PLUS the per-span source map (each
//! transcluded span knows its source `dregg://` cell + cited receipt + byte range).
//! That map is exactly the **EEL** (the "edit-edition-list" navigability) Nelson drew:
//! a side-by-side **parallel-source view** that renders the document in one column and,
//! beside each transcluded span, its SOURCE cell with the quoted range highlit — the
//! navigable two-way docuverse made visual. [`RenderedSpan::source_link`] is the
//! per-span anchor that view consumes; building the actual side-by-side render (the
//! columns + the highlight + the live "jump to source") is the
//! `servo-render`/`deos-leptos` UX seam, named here, not built in this crate.

use starbridge_web_surface::transclusion::{Provenance, TranscludedField, TransclusionError};
use starbridge_web_surface::{DreggUri, Membrane, RehydrateError, SurfaceCapability, WebOfCells};

use crate::bundle::WebBundle;

/// A byte range within a source cell's committed content — the EDL's "range r" of
/// "transclude (cell X, range r)".
///
/// Nelson's EDL addresses a *span* of a source, not the whole source: a document
/// quotes "characters `start..end` of cell X". This is that range, over the source's
/// content-addressed committed bytes. `start..end` is half-open (`end` exclusive),
/// the Rust slice convention; [`SpanRange::whole`] selects the entire source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpanRange {
    /// The byte offset the span begins at (inclusive) within the source's committed
    /// content.
    pub start: usize,
    /// The byte offset the span ends at (exclusive). [`usize::MAX`] (via
    /// [`SpanRange::whole`]) means "to the end of the source".
    pub end: usize,
}

impl SpanRange {
    /// A span of `start..end` (half-open) of the source's committed bytes.
    pub fn new(start: usize, end: usize) -> Self {
        SpanRange { start, end }
    }

    /// The whole source content — `0..end-of-content`. The EDL's "transclude all of
    /// cell X".
    pub fn whole() -> Self {
        SpanRange {
            start: 0,
            end: usize::MAX,
        }
    }

    /// The number of bytes this range selects from a `len`-byte source (clamped to
    /// the source's length — a range past the end selects only what exists).
    pub fn len_in(&self, content_len: usize) -> usize {
        let end = self.end.min(content_len);
        end.saturating_sub(self.start.min(content_len))
    }

    /// Select this range of `content`, clamped to the content's length. A `start`
    /// past the end yields an empty slice; an `end` past the end is clamped — the EDL
    /// span never reads outside the source it cites.
    pub fn select<'a>(&self, content: &'a [u8]) -> &'a [u8] {
        let len = content.len();
        let start = self.start.min(len);
        let end = self.end.min(len);
        if start >= end {
            &content[0..0]
        } else {
            &content[start..end]
        }
    }
}

/// One **span** of a dreggverse document's EDL — either the author's OWN content, or
/// a **transcluded span** of another cell (cell X, byte range r).
///
/// This is the EDL element. An ordered `Vec<Span>` IS the document: rendering resolves
/// each span (OWN content verbatim; a transcluded span via the REAL verified
/// cross-cell read of its source's range) and composes them edge-to-edge. Editing the
/// document is editing this list; editing a SOURCE updates that span's quoted content
/// live, without touching the EDL.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Span {
    /// The author's OWN content — bytes that belong to THIS document (not quoted from
    /// anywhere). Rendered verbatim; it carries no foreign provenance.
    Own(Vec<u8>),
    /// A **transcluded span** — include-by-reference: the byte `range` of the source
    /// `dregg://` cell's finalized content. At render the source is the REAL verified
    /// cross-cell read; the rendered bytes ARE the source's committed bytes in that
    /// range, with the source's receipt-pinned provenance. If `asset` is set, the
    /// source is a `deos-web-cells` bundle and the range is taken within that NAMED
    /// asset's bytes (the DOM-level span); if `None`, the range is taken over the
    /// source's raw committed content.
    Transcluded {
        /// The source `dregg://<cell>` the span is quoted FROM.
        source: DreggUri,
        /// The byte range within the source's content the span selects (the EDL's
        /// "range r").
        range: SpanRange,
        /// For a bundle source: the named asset the range is within (e.g.
        /// `index.html`). `None` ⇒ the range is over the source cell's raw committed
        /// content (a non-bundle source).
        asset: Option<String>,
    },
}

impl Span {
    /// An OWN-content span carrying `content`.
    pub fn own(content: impl Into<Vec<u8>>) -> Self {
        Span::Own(content.into())
    }

    /// A transcluded span: the whole of the `source` cell's raw committed content.
    pub fn transclude(source: DreggUri) -> Self {
        Span::Transcluded {
            source,
            range: SpanRange::whole(),
            asset: None,
        }
    }

    /// A transcluded span: a byte `range` of the `source` cell's raw committed content.
    pub fn transclude_range(source: DreggUri, range: SpanRange) -> Self {
        Span::Transcluded {
            source,
            range,
            asset: None,
        }
    }

    /// A transcluded span: a byte `range` within a NAMED `asset` of the `source`
    /// BUNDLE cell (the DOM-level span — quote a range of a published bundle's
    /// `index.html`, say).
    pub fn transclude_asset_range(
        source: DreggUri,
        asset: impl Into<String>,
        range: SpanRange,
    ) -> Self {
        Span::Transcluded {
            source,
            range,
            asset: Some(asset.into()),
        }
    }

    /// Whether this span is a transcluded span (vs. OWN content).
    pub fn is_transcluded(&self) -> bool {
        matches!(self, Span::Transcluded { .. })
    }
}

/// A **dreggverse document** — an ordered EDL of [`Span`]s (Xanadu's actual
/// document, made honest).
///
/// The document is *defined* by its EDL: a `Vec<Span>` of OWN content interleaved
/// with transcluded spans of other cells. It carries no resolved bytes for the
/// transcluded spans — those are re-fetched + verified at [`DreggverseDocument::resolve`],
/// so the document tracks its sources (amend a source ⇒ the next resolve shows the new
/// value). The document's identity is its EDL, not a frozen render.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct DreggverseDocument {
    /// The ordered edit-decision-list: the spans, in document order.
    spans: Vec<Span>,
}

impl DreggverseDocument {
    /// An empty document (no spans).
    pub fn new() -> Self {
        DreggverseDocument { spans: Vec::new() }
    }

    /// Build a document from an ordered list of spans (the EDL).
    pub fn from_spans(spans: Vec<Span>) -> Self {
        DreggverseDocument { spans }
    }

    /// Append a span to the EDL (authoring the document, left to right). Returns
    /// `&mut self` so spans chain.
    pub fn push(&mut self, span: Span) -> &mut Self {
        self.spans.push(span);
        self
    }

    /// The document's EDL — its ordered spans (read-only).
    pub fn spans(&self) -> &[Span] {
        &self.spans
    }

    /// How many spans the EDL has.
    pub fn len(&self) -> usize {
        self.spans.len()
    }

    /// Whether the EDL is empty.
    pub fn is_empty(&self) -> bool {
        self.spans.is_empty()
    }

    /// How many of the document's spans are transcluded (vs. OWN) — the count of
    /// live cross-cell quotes the document is composed from.
    pub fn transcluded_count(&self) -> usize {
        self.spans.iter().filter(|s| s.is_transcluded()).count()
    }

    /// **Resolve the document** — compose OWN content with each transcluded span's
    /// VERIFIED, provenance-bearing quote, in document order. The full-authority
    /// render (the author's own view): every transcluded span is the REAL verified
    /// cross-cell finalized read of its source's range.
    ///
    /// Each transcluded span runs the REAL [`TranscludedField::include`] (the genuine
    /// `dregg://` attested fetch + the `content→commitment→receipt→receipt-stream-root→
    /// quorum` verification — a forged / absent / un-finalized source is REFUSED), then
    /// selects the span's byte range of the source's COMMITTED bytes. The rendered span
    /// bytes ARE the source's committed bytes in that range, carrying the source's
    /// receipt-pinned [`Provenance`]. A failure on ANY transcluded span fails the whole
    /// resolve (a document that cites a forged or vanished source does not silently
    /// render half — confinement before content).
    pub fn resolve(&self, web: &WebOfCells) -> Result<RenderedDocument, DocumentError> {
        let mut rendered = Vec::with_capacity(self.spans.len());
        for (index, span) in self.spans.iter().enumerate() {
            rendered.push(resolve_span(span, index, web)?);
        }
        Ok(RenderedDocument { spans: rendered })
    }

    /// **Resolve the document PER-VIEWER, through the membrane** — the per-viewer
    /// docuverse: compose the document for a viewer whose authority may be WEAKER than
    /// the author's, darkening (never forging) the spans the viewer cannot read.
    ///
    /// For each transcluded span, the source's `lineage` (the authority the span is
    /// served under) is met with the `viewer` membrane through the REAL
    /// [`Membrane::project`]:
    ///
    /// - if the projection **succeeds** AND the projected surface's fetch-allowlist
    ///   permits the source span's origin (the GENUINE [`SurfaceCapability::may_fetch`]),
    ///   the span resolves to the verified source bytes (exactly as [`Self::resolve`]),
    ///   carrying its provenance;
    /// - if the projection is **refused** (an incomparable identity —
    ///   [`RehydrateError::Amplification`]) OR the projected fetch-allowlist does NOT
    ///   permit the source span's origin, the span is **darkened**: rendered as a
    ///   [`RenderedSpan::Darkened`] placeholder that carries the span's PROVENANCE (the
    ///   source ref + cited receipt + byte range — so the document's SHAPE and citations
    ///   remain visible) but NONE of the source bytes the viewer lacks authority to read.
    ///
    /// OWN spans always render (they are the author's own content, served under the
    /// document's own authority). The provenance map a weaker viewer sees is the same
    /// docuverse skeleton; only the *bytes* of unreachable spans are withheld — never
    /// forged, never substituted. `lineage` is the source-side authority the document's
    /// transcluded spans are published under (typically the publisher's lineage over the
    /// source cells); a single lineage is used for every span here (the common case: one
    /// publisher's docuverse), matching the membrane-meet shape `rehydrate` uses.
    pub fn resolve_for(
        &self,
        web: &WebOfCells,
        viewer: &Membrane,
        lineage: &SurfaceCapability,
    ) -> Result<RenderedDocument, DocumentError> {
        let mut rendered = Vec::with_capacity(self.spans.len());
        for (index, span) in self.spans.iter().enumerate() {
            match span {
                // OWN content always renders (the author's own, under the document's
                // own authority).
                Span::Own(_) => rendered.push(resolve_span(span, index, web)?),
                Span::Transcluded {
                    source,
                    range,
                    asset,
                } => {
                    // The per-viewer meet: project the source's lineage through the
                    // viewer's membrane (the REAL is_attenuation lattice). An
                    // incomparable identity is refused here → the span darkens.
                    let projection = viewer.project(lineage);
                    // The source span's stable origin (the same origin key the
                    // rehydrate per-asset gate uses). For a bundle-asset span it is the
                    // asset's origin; for a raw-cell span it is the cell's own origin.
                    let origin = span_origin(source, asset.as_deref());

                    let reachable = match &projection {
                        Ok(surface) => surface.may_fetch(&origin),
                        Err(RehydrateError::Amplification) => false,
                        // Any other projection failure is a hard error, not a
                        // darkening (it is not a "you lack authority" but a structural
                        // failure of the meet) — surface it.
                        Err(e) => return Err(DocumentError::Projection(index, e.clone())),
                    };

                    if reachable {
                        // The viewer's projection reaches this span: resolve it for
                        // real (verified bytes + provenance), exactly as `resolve`.
                        rendered.push(resolve_span(span, index, web)?);
                    } else {
                        // Darkened: the span the viewer cannot read. We still want its
                        // PROVENANCE (so the document's shape + citation survive), but
                        // we must NOT hand the viewer the source bytes. We resolve the
                        // provenance from the REAL verified read (the citation is public
                        // — it is the source ref + receipt the author cited), then drop
                        // the bytes. If even the citation cannot be formed (the source
                        // vanished), that is a genuine resolve error.
                        let provenance = cite_only(source, web)
                            .map_err(|e| DocumentError::Transclusion(index, e))?;
                        rendered.push(RenderedSpan::Darkened {
                            provenance,
                            range: *range,
                            asset: asset.clone(),
                        });
                    }
                }
            }
        }
        Ok(RenderedDocument { spans: rendered })
    }
}

/// Resolve a single span to its rendered form (OWN bytes verbatim; a transcluded span
/// via the REAL verified cross-cell read of its source's range). The shared full-read
/// path of [`DreggverseDocument::resolve`] and the reachable branch of
/// [`DreggverseDocument::resolve_for`].
fn resolve_span(
    span: &Span,
    index: usize,
    web: &WebOfCells,
) -> Result<RenderedSpan, DocumentError> {
    match span {
        Span::Own(content) => Ok(RenderedSpan::Own(content.clone())),
        Span::Transcluded {
            source,
            range,
            asset,
        } => {
            // (1) THE FINALIZED READ — the REAL verified cross-cell observation of the
            //     source cell. Verifies the provenance chain + refuses a forged/absent/
            //     un-finalized quote (no opened provenance ⇒ no span).
            let field = TranscludedField::include(web, source)
                .map_err(|e| DocumentError::Transclusion(index, e))?;

            // (2) The source content the range is taken over: either a NAMED bundle
            //     asset's bytes (a DOM-level span), or the source cell's raw committed
            //     bytes (a non-bundle span). Both are drawn from the VERIFIED quoted
            //     bytes (content-addressed) — never a copy.
            let source_content: Vec<u8> = match asset {
                Some(asset_name) => {
                    // The source is a deos-web-cells bundle: decode the verified bundle
                    // and take the named asset's bytes.
                    let bundle = WebBundle::decode(field.quoted_bytes())
                        .map_err(|e| DocumentError::Bundle(index, format!("{e:?}")))?;
                    let a = bundle
                        .asset(asset_name)
                        .ok_or_else(|| DocumentError::NoSuchAsset {
                            index,
                            asset_name: asset_name.clone(),
                        })?;
                    a.bytes.clone()
                }
                None => field.quoted_bytes().to_vec(),
            };

            // (3) Select the EDL span's byte range of the source content (clamped to
            //     the source's length — a span never reads outside what it cites).
            let bytes = range.select(&source_content).to_vec();

            Ok(RenderedSpan::Transcluded {
                bytes,
                provenance: field.cite().clone(),
                range: *range,
                asset: asset.clone(),
            })
        }
    }
}

/// Resolve ONLY the provenance citation of a source — the REAL verified read, kept for
/// its [`Provenance`] but with the source bytes DROPPED. Used by the darkened branch:
/// the citation (source ref + cited receipt + content commitment) is the public part of
/// a quote (it is what the author cited), so a darkened span can still show its
/// provenance without leaking the bytes the viewer lacks authority to read.
fn cite_only(source: &DreggUri, web: &WebOfCells) -> Result<Provenance, TransclusionError> {
    let field = TranscludedField::include(web, source)?;
    Ok(field.cite().clone())
}

/// The stable origin key for a transcluded span's source — the SAME origin the
/// rehydrate per-asset gate ([`WebBundle::asset_origin`]) uses for a bundle asset, and
/// a per-cell origin for a raw-cell span. This is what the viewer's projected
/// fetch-allowlist is checked against in [`DreggverseDocument::resolve_for`] — so span
/// reachability rides the GENUINE [`SurfaceCapability::may_fetch`] meet, never a
/// parallel filter.
fn span_origin(source: &DreggUri, asset: Option<&str>) -> String {
    match asset {
        Some(asset_name) => WebBundle::asset_origin(source.cell, asset_name),
        // A raw-cell span's origin: the bundle-asset origin shape with a stable
        // "(document)" asset name, so a per-cell span composes with the same allowlist
        // grammar a bundle asset does.
        None => WebBundle::asset_origin(source.cell, "(document)"),
    }
}

/// One **rendered span** of a resolved document — the composed output of one EDL span.
///
/// OWN content renders as itself; a transcluded span renders as the source's verified
/// bytes in the cited range, carrying its receipt-pinned provenance; a span a weaker
/// viewer cannot read renders DARKENED — its provenance survives (the document's shape +
/// citation), its bytes withheld (never forged).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RenderedSpan {
    /// The author's OWN content, verbatim.
    Own(Vec<u8>),
    /// A transcluded span: the source's VERIFIED bytes in the cited range, with the
    /// source's receipt-pinned provenance.
    Transcluded {
        /// The source's committed bytes in the cited range — the live quote. These ARE
        /// the source's bytes (content-addressed via the verified read), not a copy.
        bytes: Vec<u8>,
        /// The receipt-pinned citation: the source ref + content commitment + cited
        /// receipt + finalized. The honest, dated provenance of this span.
        provenance: Provenance,
        /// The EDL byte range this span selected of the source.
        range: SpanRange,
        /// For a bundle-asset span: the named asset the range was within.
        asset: Option<String>,
    },
    /// A **darkened** span — a transcluded span the viewer's projection cannot reach
    /// (an incomparable identity, or a source its projected fetch-allowlist does not
    /// permit). It carries the span's PROVENANCE (so the document's shape + citation
    /// stay visible) but NONE of the source bytes: never the source value the viewer
    /// lacks, never a forgery.
    Darkened {
        /// The provenance of the span the viewer cannot read (the source ref + cited
        /// receipt + content commitment) — the citation survives even when the bytes
        /// are withheld.
        provenance: Provenance,
        /// The EDL byte range the (withheld) span would have selected.
        range: SpanRange,
        /// For a bundle-asset span: the named asset the (withheld) range was within.
        asset: Option<String>,
    },
}

impl RenderedSpan {
    /// Whether this span was darkened (the viewer could not read it).
    pub fn is_darkened(&self) -> bool {
        matches!(self, RenderedSpan::Darkened { .. })
    }

    /// The bytes this span contributes to the composed document — the OWN content, the
    /// transcluded source's cited-range bytes, or (for a DARKENED span) NOTHING (an
    /// empty slice: the viewer gets no source bytes it lacks authority to read).
    pub fn bytes(&self) -> &[u8] {
        match self {
            RenderedSpan::Own(b) => b,
            RenderedSpan::Transcluded { bytes, .. } => bytes,
            RenderedSpan::Darkened { .. } => &[],
        }
    }

    /// The provenance this span carries, if it is a quote (transcluded or darkened) —
    /// `None` for OWN content (which has no foreign source). The per-span citation the
    /// parallel-source view renders beside the span.
    pub fn provenance(&self) -> Option<&Provenance> {
        match self {
            RenderedSpan::Own(_) => None,
            RenderedSpan::Transcluded { provenance, .. } => Some(provenance),
            RenderedSpan::Darkened { provenance, .. } => Some(provenance),
        }
    }

    /// The **parallel-source link** for this span — the navigable anchor the EEL /
    /// parallel-source view (the named UX follow-on) uses to render the SOURCE column
    /// beside the document, with the quoted range highlit.
    ///
    /// For a quote (transcluded or darkened) it is `Some((source ref, range))` — "jump
    /// to `dregg://<cell>` and highlight bytes `range`"; for OWN content it is `None`
    /// (own content has no parallel source). This is the per-span half of Nelson's
    /// two-way link, drawn from the verified citation (not a hand-maintained index).
    pub fn source_link(&self) -> Option<(DreggUri, SpanRange)> {
        match self {
            RenderedSpan::Own(_) => None,
            RenderedSpan::Transcluded {
                provenance, range, ..
            } => Some((provenance.source.clone(), *range)),
            RenderedSpan::Darkened {
                provenance, range, ..
            } => Some((provenance.source.clone(), *range)),
        }
    }
}

/// A **rendered document** — the resolved composition of a [`DreggverseDocument`]: the
/// ordered rendered spans (OWN + verified quotes + any darkened spans), each carrying
/// its provenance.
///
/// This is the document made viewable: [`RenderedDocument::composed_bytes`] is the
/// edge-to-edge text; the per-span [`Provenance`] is the bibliography that renders; the
/// per-span [`RenderedSpan::source_link`] is the EEL the parallel-source view consumes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RenderedDocument {
    /// The rendered spans, in document order.
    spans: Vec<RenderedSpan>,
}

impl RenderedDocument {
    /// The rendered spans, in document order (read-only).
    pub fn spans(&self) -> &[RenderedSpan] {
        &self.spans
    }

    /// The **composed document bytes** — every span's contribution concatenated in
    /// document order (OWN content + each transcluded span's cited-range bytes; a
    /// darkened span contributes nothing). The text a reader sees.
    pub fn composed_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for span in &self.spans {
            out.extend_from_slice(span.bytes());
        }
        out
    }

    /// The composed bytes as a UTF-8 string, if the composition is valid UTF-8 (a
    /// convenience for text documents). `None` if any span carried non-UTF-8 bytes.
    pub fn composed_text(&self) -> Option<String> {
        String::from_utf8(self.composed_bytes()).ok()
    }

    /// The **per-span provenance map** — for every span, its provenance if it is a
    /// quote (`None` for OWN content). The document's bibliography: which spans are
    /// quoted, from where, at which cited receipt. The data the parallel-source view
    /// renders beside the columns.
    pub fn provenance_map(&self) -> Vec<Option<&Provenance>> {
        self.spans.iter().map(|s| s.provenance()).collect()
    }

    /// How many rendered spans were DARKENED (the viewer could not read them). `0` for
    /// a full-authority [`DreggverseDocument::resolve`]; positive for a weaker viewer
    /// whose projection withheld at least one span.
    pub fn darkened_count(&self) -> usize {
        self.spans.iter().filter(|s| s.is_darkened()).count()
    }

    /// Whether the document rendered FULLY (no spans darkened) — `true` for a
    /// full-authority render or a viewer whose projection reached every span.
    pub fn is_full(&self) -> bool {
        self.darkened_count() == 0
    }

    /// The **parallel-source links** — the per-span EEL: for every span, its
    /// `(source ref, range)` if it is a quote (`None` for OWN content). The navigable
    /// map the side-by-side parallel-source view renders the SOURCE column from.
    pub fn source_links(&self) -> Vec<Option<(DreggUri, SpanRange)>> {
        self.spans.iter().map(|s| s.source_link()).collect()
    }
}

/// What can go wrong resolving a [`DreggverseDocument`] — keyed by the span INDEX in
/// the EDL, so a failure names exactly which span did not resolve.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DocumentError {
    /// A transcluded span's source `dregg://` read did not resolve to a verified
    /// finalized read, or its provenance did not verify, or it was not quorum-finalized
    /// — the REAL [`TransclusionError`], carried through. No opened provenance ⇒ no
    /// span. Carries the span index.
    Transclusion(usize, TransclusionError),
    /// A transcluded span named a bundle asset, but the source's verified content did
    /// not decode as a `deos-web-cells` bundle (the source is not a bundle cell). The
    /// attestation held, but it is not a bundle. Carries the span index + the bundle
    /// error rendered.
    Bundle(usize, String),
    /// A transcluded span named a bundle asset the source bundle does not carry — you
    /// cannot quote a span of an asset that is not in the source. Carries the span
    /// index + the asset name.
    NoSuchAsset {
        /// The EDL span index.
        index: usize,
        /// The asset name the span requested but is not in the source bundle.
        asset_name: String,
    },
    /// The per-viewer projection of a transcluded span's lineage failed STRUCTURALLY
    /// (a membrane error that is not the `Amplification` "you lack authority" darkening
    /// — that case darkens the span rather than erroring). Carries the span index + the
    /// real [`RehydrateError`].
    Projection(usize, RehydrateError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bundle::{publish_bundle, BundleAsset, BundleKind};
    use crate::tests_support::cid;
    use starbridge_web_surface::rehydrate::InteractionLog;
    use starbridge_web_surface::AuthRequired;

    use std::collections::BTreeSet;

    fn origins(list: &[String]) -> BTreeSet<String> {
        list.iter().cloned().collect()
    }

    /// Publish a RAW (non-bundle) source cell carrying `body`, return (web-extended,
    /// ref). Uses the genuine `WebOfCells::publish` so the source is a real finalized
    /// read.
    fn publish_raw(web: &mut WebOfCells, seed: u8, body: &[u8]) -> DreggUri {
        web.publish(seed, body, "dregg://source")
    }

    // ── (1) A DOCUMENT COMPOSED FROM 2+ TRANSCLUDED SPANS + OWN CONTENT renders with
    //        per-span provenance. The core Xanadu-document shape. ──

    #[test]
    fn a_document_composes_own_and_two_transcluded_spans_with_provenance() {
        // Two source cells, each a real published finalized-read source.
        let mut web = WebOfCells::new(3);
        let src_a = publish_raw(&mut web, 1, b"the WHOLE of source A");
        let src_b = publish_raw(&mut web, 2, b"0123456789 source B has a range");

        // The EDL: OWN intro, the whole of A, OWN connective, a RANGE of B, OWN outro.
        let doc = DreggverseDocument::from_spans(vec![
            Span::own(b"INTRO: ".to_vec()),
            Span::transclude(src_a.clone()),
            Span::own(b" | ".to_vec()),
            // bytes 11..20 of B = "source B " (a sub-span of the source).
            Span::transclude_range(src_b.clone(), SpanRange::new(11, 20)),
            Span::own(b" :OUTRO".to_vec()),
        ]);
        assert_eq!(doc.len(), 5);
        assert_eq!(doc.transcluded_count(), 2);

        let rendered = doc.resolve(&web).expect("the document resolves");

        // The composed text: OWN + the whole of A + OWN + the B sub-span + OWN.
        assert_eq!(
            rendered.composed_text().unwrap(),
            "INTRO: the WHOLE of source A | source B  :OUTRO"
        );

        // PER-SPAN PROVENANCE: the two transcluded spans carry their source citations;
        // the three OWN spans carry none.
        let prov = rendered.provenance_map();
        assert_eq!(prov.len(), 5);
        assert!(prov[0].is_none(), "OWN intro has no foreign provenance");
        assert_eq!(prov[1].unwrap().source, src_a, "span 1 cites source A");
        assert!(
            prov[1].unwrap().finalized,
            "a published+attested source is finalized"
        );
        assert!(prov[2].is_none(), "OWN connective has no provenance");
        assert_eq!(prov[3].unwrap().source, src_b, "span 3 cites source B");
        assert!(prov[4].is_none(), "OWN outro has no provenance");

        // The full-authority render darkened nothing.
        assert!(rendered.is_full());
        assert_eq!(rendered.darkened_count(), 0);

        // The parallel-source links (the EEL): the two quotes carry (source, range);
        // OWN spans carry none.
        let links = rendered.source_links();
        assert_eq!(links[1], Some((src_a.clone(), SpanRange::whole())));
        assert_eq!(links[3], Some((src_b.clone(), SpanRange::new(11, 20))));
        assert!(links[0].is_none() && links[2].is_none() && links[4].is_none());
    }

    // ── A transcluded span can quote a RANGE within a NAMED BUNDLE ASSET (the
    //    DOM-level span). ──

    #[test]
    fn a_span_quotes_a_range_within_a_named_bundle_asset() {
        let bundle = WebBundle::new(
            BundleKind::StaticBundle,
            "index.html",
            vec![
                BundleAsset::new(
                    "index.html",
                    "text/html",
                    b"<h1>HELLO DREGGVERSE</h1>".to_vec(),
                ),
                BundleAsset::new("app.js", "application/javascript", b"run()".to_vec()),
            ],
        )
        .expect("valid bundle");
        let mut web = WebOfCells::new(3);
        let lineage = SurfaceCapability::root(cid(3), AuthRequired::Either);
        let (uri, _sr) =
            publish_bundle(&mut web, 3, &bundle, lineage, InteractionLog::new(), false);

        // Quote bytes 4..21 of the bundle's index.html = "HELLO DREGGVERSE".
        let doc = DreggverseDocument::from_spans(vec![
            Span::own(b"quote: <".to_vec()),
            Span::transclude_asset_range(uri.clone(), "index.html", SpanRange::new(4, 20)),
            Span::own(b">".to_vec()),
        ]);
        let rendered = doc.resolve(&web).expect("resolves the bundle-asset span");
        assert_eq!(
            rendered.composed_text().unwrap(),
            "quote: <HELLO DREGGVERSE>"
        );
        // The span cites the bundle source.
        assert_eq!(rendered.spans()[1].provenance().unwrap().source, uri);
    }

    // ── (2) THE UNBREAKABLE LINK: amending a SOURCE updates that span's quoted content
    //        LIVE, every other span untouched. ──

    #[test]
    fn amending_a_source_updates_that_span_live_others_untouched() {
        let mut web = WebOfCells::new(3);
        let constitution = publish_raw(&mut web, 4, b"threshold = 3");
        let stable = publish_raw(&mut web, 5, b"STABLE PREAMBLE");

        let doc = DreggverseDocument::from_spans(vec![
            Span::transclude(stable.clone()),
            Span::own(b" / current: ".to_vec()),
            Span::transclude(constitution.clone()),
        ]);

        // v0: the document quotes the original constitution.
        let r0 = doc.resolve(&web).expect("v0 resolves");
        assert_eq!(
            r0.composed_text().unwrap(),
            "STABLE PREAMBLE / current: threshold = 3"
        );
        let cited_receipt_v0 = r0.spans()[2].provenance().unwrap().receipt_hash;

        // AMEND the constitution source (the REAL WebOfCells::amend — a verified state
        // advance; the dregg:// ref is UNCHANGED).
        web.amend(&constitution, b"threshold = 5")
            .expect("amend resolves");

        // v1: the SAME document, re-resolved, now shows the source's NEW value in that
        // span — the unbreakable link. The other spans are untouched.
        let r1 = doc.resolve(&web).expect("v1 resolves (same EDL)");
        assert_eq!(
            r1.composed_text().unwrap(),
            "STABLE PREAMBLE / current: threshold = 5",
            "the quoted span tracked the amended source live"
        );
        // The cited receipt for that span ADVANCED (a distinct cited point — a holder
        // can SEE the source moved; no silent live read).
        let cited_receipt_v1 = r1.spans()[2].provenance().unwrap().receipt_hash;
        assert_ne!(
            cited_receipt_v1, cited_receipt_v0,
            "the cited receipt advanced"
        );
        // The OTHER transcluded span (the stable preamble) is byte-identical AND cites
        // the SAME receipt — amending one source touched only its span.
        assert_eq!(r1.spans()[0].bytes(), b"STABLE PREAMBLE");
        assert_eq!(
            r0.spans()[0].provenance().unwrap().receipt_hash,
            r1.spans()[0].provenance().unwrap().receipt_hash,
            "the unrelated span's citation is unchanged"
        );
    }

    // ── (3) A FORGED SPAN IS REFUSED — no opened provenance ⇒ no document. ──

    #[test]
    fn a_forged_span_is_refused() {
        // (a) ABSENT: a span citing a never-published source does not resolve to a
        //     finalized read — the whole document resolve is refused at that span.
        let mut web = WebOfCells::new(3);
        let real = publish_raw(&mut web, 6, b"real content");
        let absent = DreggUri::new(cid(222));
        let doc_absent = DreggverseDocument::from_spans(vec![
            Span::own(b"before ".to_vec()),
            Span::transclude(absent.clone()),
            Span::transclude(real.clone()),
        ]);
        let r = doc_absent.resolve(&web);
        assert!(
            matches!(
                &r,
                Err(DocumentError::Transclusion(1, TransclusionError::Fetch(_)))
            ),
            "a span citing an absent source refuses the document at span 1, got {r:?}"
        );

        // (b) FORGED: the property the resolve relies on — the verification chain
        //     catches a tampered source. We take a genuine attested resource and tamper
        //     its bytes; verify() refuses, so the span's include (which runs exactly
        //     this verify) would refuse. We assert the gate's polarity directly.
        let (mut resource, _chrome) = web.fetch(&real).expect("genuine fetch");
        resource.content_bytes = b"FORGED - bytes the source never committed".to_vec();
        assert!(
            resource.verify().is_err(),
            "a forged span's tampered bytes fail the provenance chain (so include refuses)"
        );
    }

    // ── A span naming an asset NOT in the source bundle is refused. ──

    #[test]
    fn a_span_naming_a_missing_bundle_asset_is_refused() {
        let bundle = WebBundle::static_html(b"<h1>doc</h1>".to_vec());
        let mut web = WebOfCells::new(3);
        let lineage = SurfaceCapability::root(cid(7), AuthRequired::Either);
        let (uri, _sr) =
            publish_bundle(&mut web, 7, &bundle, lineage, InteractionLog::new(), false);
        let doc = DreggverseDocument::from_spans(vec![Span::transclude_asset_range(
            uri,
            "nonexistent.js",
            SpanRange::whole(),
        )]);
        let r = doc.resolve(&web);
        assert!(
            matches!(&r, Err(DocumentError::NoSuchAsset { index: 0, asset_name }) if asset_name == "nonexistent.js"),
            "a span naming a missing asset is refused, got {r:?}"
        );
    }

    // ── (4) A WEAKER VIEWER sees the document with DARKENED spans — NOT the source
    //        values it lacks, NEVER a forgery. ──

    #[test]
    fn a_weaker_viewer_sees_darkened_spans_not_the_source_values() {
        // Two source spans published into the web. The document's transclude lineage is
        // scoped to BOTH source spans' origins (so a full-authority viewer reaches
        // both); a WEAKER viewer is scoped to only ONE — the other span darkens.
        let mut web = WebOfCells::new(3);
        let public_src = publish_raw(&mut web, 8, b"PUBLIC paragraph");
        let secret_src = publish_raw(&mut web, 9, b"SECRET paragraph");

        let public_origin = span_origin(&public_src, None);
        let secret_origin = span_origin(&secret_src, None);

        // The source-side lineage the document's spans are served under: permits BOTH
        // span origins (Either authority). (One publisher's docuverse.)
        let lineage = SurfaceCapability::scoped(
            public_src.cell,
            AuthRequired::Either,
            origins(&[public_origin.clone(), secret_origin.clone()]),
            [],
        );

        let doc = DreggverseDocument::from_spans(vec![
            Span::own(b"DOC: ".to_vec()),
            Span::transclude(public_src.clone()),
            Span::own(b" + ".to_vec()),
            Span::transclude(secret_src.clone()),
        ]);

        // A FULL-authority viewer (wildcard fetch, Either rights) reaches BOTH spans:
        // the document renders fully, both quotes present + provenanced.
        let full_viewer = Membrane::new(SurfaceCapability::root(cid(20), AuthRequired::Either));
        let full = doc
            .resolve_for(&web, &full_viewer, &lineage)
            .expect("full viewer resolves");
        assert!(full.is_full(), "the full-authority viewer darkens nothing");
        assert_eq!(
            full.composed_text().unwrap(),
            "DOC: PUBLIC paragraph + SECRET paragraph"
        );
        assert_eq!(full.darkened_count(), 0);

        // A WEAKER viewer scoped to ONLY the public span's origin (Either rights, but a
        // finite fetch-allowlist that excludes the secret span). The membrane meet
        // permits the public span and DARKENS the secret one.
        let weaker = Membrane::new(SurfaceCapability::scoped(
            cid(30),
            AuthRequired::Either,
            origins(std::slice::from_ref(&public_origin)),
            [],
        ));
        let weak = doc
            .resolve_for(&web, &weaker, &lineage)
            .expect("weaker viewer resolves (with a darkened span)");

        // The document SHAPE is intact (5? no — 4 spans), but the secret span is
        // DARKENED: the viewer sees the public paragraph + a darkened placeholder, NOT
        // the secret bytes.
        assert!(!weak.is_full());
        assert_eq!(weak.darkened_count(), 1);
        // The composed text carries the OWN content + the public span + the connective,
        // but NOTHING for the darkened secret span (the viewer gets no source bytes it
        // lacks authority to read).
        assert_eq!(weak.composed_text().unwrap(), "DOC: PUBLIC paragraph + ");
        // The public span resolved for real…
        assert!(!weak.spans()[1].is_darkened());
        assert_eq!(weak.spans()[1].bytes(), b"PUBLIC paragraph");
        // …and the secret span is DARKENED: NO source bytes…
        assert!(weak.spans()[3].is_darkened());
        assert_eq!(
            weak.spans()[3].bytes(),
            b"",
            "a darkened span yields NO source bytes"
        );
        // The viewer NEVER sees the secret value (the anti-forgery tooth: not the
        // bytes, and not a substituted forgery either — the darkened span is opaque).
        assert!(
            !weak
                .composed_bytes()
                .windows(b"SECRET".len())
                .any(|w| w == b"SECRET"),
            "the weaker viewer never sees the source value it lacks authority to read"
        );
        // …BUT the darkened span STILL carries its PROVENANCE (the document's shape +
        // citation survive — the docuverse skeleton is visible, only the bytes withheld).
        let dark_prov = weak.spans()[3]
            .provenance()
            .expect("a darkened span keeps its citation");
        assert_eq!(
            dark_prov.source, secret_src,
            "the darkened span still cites its source"
        );
        assert!(dark_prov.finalized);
        // And the parallel-source link survives (the EEL navigates to the source even
        // for a darkened span — "you may not read this, but here is what it cites").
        assert_eq!(
            weak.spans()[3].source_link(),
            Some((secret_src.clone(), SpanRange::whole()))
        );
    }

    // ── A viewer with an INCOMPARABLE identity darkens the transcluded span (the
    //    membrane refuses the projection — Amplification — which the document treats as
    //    "cannot read", darkening rather than erroring). ──

    #[test]
    fn an_incomparable_identity_viewer_darkens_the_span() {
        let mut web = WebOfCells::new(3);
        let src = publish_raw(&mut web, 10, b"confidential span");
        // The lineage carries a DISTINCT Custom identity; the viewer a DIFFERENT
        // incomparable one. is_attenuation holds NEITHER way → project() refuses →
        // the span darkens (not the whole document erroring).
        let lineage = SurfaceCapability::root(
            src.cell,
            AuthRequired::Custom {
                vk_hash: [0xAA; 32],
            },
        );
        let doc = DreggverseDocument::from_spans(vec![
            Span::own(b"[".to_vec()),
            Span::transclude(src.clone()),
            Span::own(b"]".to_vec()),
        ]);
        let incomparable = Membrane::new(SurfaceCapability::root(
            cid(41),
            AuthRequired::Custom {
                vk_hash: [0xBB; 32],
            },
        ));
        let r = doc
            .resolve_for(&web, &incomparable, &lineage)
            .expect("an incomparable identity darkens the span, not errors");
        assert_eq!(r.darkened_count(), 1);
        assert!(r.spans()[1].is_darkened());
        // The OWN brackets still render; the confidential span is withheld.
        assert_eq!(r.composed_text().unwrap(), "[]");
        assert!(
            !r.composed_bytes()
                .windows(b"confidential".len())
                .any(|w| w == b"confidential"),
            "an incomparable viewer never sees the confidential span"
        );
        // The citation still survives (the darkened span knows its source).
        assert_eq!(r.spans()[1].provenance().unwrap().source, src);
    }

    // ── A SpanRange clamps to the source (a range past the end reads only what
    //    exists; it never reads outside the cited source). ──

    #[test]
    fn a_span_range_clamps_to_the_source_length() {
        let mut web = WebOfCells::new(3);
        let src = publish_raw(&mut web, 11, b"short"); // 5 bytes
                                                       // A range 2..100 of a 5-byte source selects "ort" (clamped), never OOB.
        let doc = DreggverseDocument::from_spans(vec![Span::transclude_range(
            src.clone(),
            SpanRange::new(2, 100),
        )]);
        let r = doc.resolve(&web).expect("resolves with a clamped range");
        assert_eq!(r.composed_text().unwrap(), "ort");
        // A range entirely past the end selects nothing (an empty span — still a valid,
        // provenanced span, just empty).
        let doc2 = DreggverseDocument::from_spans(vec![Span::transclude_range(
            src.clone(),
            SpanRange::new(50, 100),
        )]);
        let r2 = doc2.resolve(&web).expect("resolves an out-of-range span");
        assert_eq!(r2.composed_text().unwrap(), "");
        assert_eq!(
            r2.spans()[0].provenance().unwrap().source,
            src,
            "still provenanced"
        );
    }

    // ── An empty document resolves to empty (no spans, no error). ──

    #[test]
    fn an_empty_document_resolves_to_empty() {
        let web = WebOfCells::new(3);
        let doc = DreggverseDocument::new();
        let r = doc.resolve(&web).expect("an empty document resolves");
        assert!(r.spans().is_empty());
        assert_eq!(r.composed_bytes(), Vec::<u8>::new());
        assert!(r.is_full());
    }
}
