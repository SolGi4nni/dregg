//! The WEB-OF-CELLS browser — the cockpit as a native browser of the `dregg://`
//! docuverse.
//!
//! The cockpit ([`crate::cockpit`]) is the live verified image; the
//! [`starbridge_web_surface`] crate is the **web of cells**: a `dregg://<cell>`
//! link is a *capability into a cell*, "fetching" it is a **verified, attested
//! cross-cell read** (a receipt + a quorum-signed `AttestedRoot` the client
//! checks), a cell publishes typed **affordances** (cap-gated effect-templates —
//! htmx-on-crack), and "opening" a surface re-acquires a per-viewer projection
//! whose `Rehydration` liveness-type is *derived*, never hand-set. This module
//! fuses the two: it BROWSES the web of cells from inside the cockpit's own live
//! [`World`].
//!
//! Like [`crate::landing`], this is the browser's pure, gpui-free **text MODEL**:
//! a projection of the live image into addressable cells, each with its
//! trusted-path origin chrome, its per-viewer affordance surface, and its
//! rehydration liveness-type. The cockpit renders this model with native gpui —
//! but because the *content* is built here, gpui-free, it is `cargo test`-able:
//! a test asserts the browser speaks real, attested, cap-projected text about the
//! real cells, so "the cockpit browses the web of cells" is proven without a GPU.
//!
//! ## Everything here is the REAL web-of-cells, never a parallel model
//!
//! - The addressing + fetch is the genuine [`WebOfCells`] / [`DreggUri`]: each
//!   live World cell is published as a `dregg://` page and FETCHED back through
//!   the real attested-fetch path, so each row carries a real [`AttestedResource`]
//!   (content-addressed + receipt-in-stream + quorum-signed root, verified by the
//!   real [`AttestedResource::verify`]) and a real [`OriginChrome`] (drawn from
//!   the LEDGER, never the page — the structural anti-phishing badge).
//! - The affordance surface is the genuine web-surface
//!   [`web_aff::AffordanceSurface`]; the per-viewer rows are
//!   [`web_aff::AffordanceSurface::project_for`] through a real
//!   [`web_aff::SurfaceCapability`] — progressive enhancement becomes progressive
//!   **attenuation**, gated by the proven [`is_attenuation`] lattice. A viewer
//!   sees exactly the affordances its caps authorize.
//! - The liveness-type is the genuine [`web_aff::Rehydration`], **DERIVED** via
//!   [`web_aff::Rehydration::classify`] from a real [`web_aff::InteractionLog`] of
//!   the attested fetch — not a hand-assigned field.
//! - **Firing** an affordance does NOT stop at a modeled dispatch: the effect the
//!   web-surface affordance carries is the SAME real [`dregg_turn::Effect`] the
//!   cockpit's own [`crate::affordance::AffordanceIntent::fire_through_world`]
//!   runs through the embedded executor. [`WebCellsBrowser::fire_affordance`]
//!   lifts the projected effect across that one-type bridge and commits it as a
//!   REAL verified turn through the live [`World`] — the seam the web crate could
//!   only name is CLOSED here, because this process embeds the executor.
//!
//! ## What integrated vs. what is named-next
//!
//! - **Integrated (here):** the cockpit browses the web of cells natively — it
//!   lists the addressable `dregg://` cells with their attested origin chrome,
//!   opens one to its per-viewer affordance surface (the real `project_for`
//!   attenuation), shows its rehydration liveness-type + provenance, and FIRES an
//!   affordance through the real embedded executor.
//! - **Named-next (the SERVO layer):** the browser renders affordance *surfaces*
//!   natively today; embedding **servo** to render actual `dregg://` web *content*
//!   (the `WebViewDelegate` cap-gate, where the web-surface crate's `MockSurface`
//!   stands today) is the next layer — the servo Stage-A renderer lane.
//!   [`WebCellsBrowser::servo_layer_note`] states it in the model so it is visible
//!   in the panel, not buried.
//! - **Named-next (the TRANSCLUSION affordance):** [`Transclusion`] here shows ONE
//!   Ted-Nelson transcluded field — a cell that INCLUDES another cell's finalized
//!   content commitment, with the provenance receipt shown — built on the cleanly
//!   reachable web-of-cells `OriginChrome` provenance. The *verified cross-cell
//!   observation* form (the protocol's `ObservedFieldEquals` predicate, which
//!   lives below the web-surface crate's public API in `dregg_cell::predicate`)
//!   is named as the increment that hardens it into an in-circuit observation.

use starbridge_web_surface as web_aff;
use web_aff::{
    AffordanceSurface as WebAffordanceSurface, AttestedResource, AuthRequired, CellAffordance,
    DreggUri, Effect, InteractionLog, Membrane, OriginChrome, Rehydration, SurfaceCapability,
    WebOfCells,
};
// The REAL verified transclusion — "Xanadu that shipped": a transclusion IS a
// verified cross-cell finalized read (content→commitment→receipt→receipt-stream
// root→quorum). We USE it, never reinvent the provenance.
use web_aff::transclusion::{TranscludedField, TransclusionError};

// THE DREGGVERSE DOCUMENT — Xanadu's EDL made honest: an ordered list of `Span`s
// (OWN content interleaved with byte-RANGE transclusions of peer cells), resolved
// PER-VIEWER through the REAL `Membrane`. `deos_web_cells`'s `DreggUri`/`WebOfCells`/
// `Provenance` ARE this module's `starbridge_web_surface` ones (cargo resolves
// IDENTICAL crate instances — same path-dep, same plonky3-recursion `[patch]`), so a
// `Span::transclude_range` over the SAME `web` the browser already built renders here
// with no parallel fetch, no parallel attestation. We render the rich EDL span model
// the cockpit's whole-field `Transclusion` could not.
use deos_web_cells::{DreggverseDocument, RenderedSpan, Span, SpanRange};

use dregg_cell::CellId;

use crate::affordance::FireOutcome;
use crate::reflect;
use crate::world::World;

/// One **addressable cell** in the web of cells — a `dregg://` row the browser
/// lists. Every field is a real read of the attested fetch / the ledger-drawn
/// origin chrome, never a hand-set string.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellRow {
    /// The backing World cell this `dregg://` page denotes.
    pub cell: CellId,
    /// The `dregg://<hex>` address as it appears in the address bar — the
    /// content-addressed cell id, the access grant AND the identity.
    pub uri: String,
    /// The TRUSTED-PATH origin chrome badge — drawn from the LEDGER (cell id +
    /// committed URL + rights lineage + finality), never the page. dregg's
    /// structural answer to browser-chrome phishing.
    pub chrome_badge: String,
    /// Whether the full client-side attestation chain VERIFIED (content-addressed
    /// + receipt-in-stream + real receipt-stream-root reconstruction + quorum).
    /// The page renders only on `true`.
    pub attested: bool,
    /// The finalized content commitment (`blake3` of the served bytes), short-hex
    /// — the field a transclusion would include, and the page's self-certifying
    /// identity.
    pub content_commitment: String,
    /// The committed URL the origin cell carries (its trusted-chrome source).
    pub committed_url: Option<String>,
    /// A one-line human preview of the served page body (the real attested bytes).
    pub preview: String,
}

/// One affordance row in an opened cell's surface, AS PROJECTED FOR THE VIEWER.
/// Present in the list iff the viewer's caps authorize it — the rows the viewer
/// is NOT cleared for are absent (progressive attenuation), and the model records
/// how many were attenuated away.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffordanceRow {
    /// The affordance name (the deos analogue of htmx's `hx-post` path).
    pub name: String,
    /// The authority a viewer must HOLD to fire it (`required ⊆ held`).
    pub required: String,
    /// The REAL effect this affordance would fire, summarized (`SetField` /
    /// `EmitEvent` / `GrantCapability` …) — the genuine turn the executor runs.
    pub effect: String,
}

/// The Ted-Nelson **transclusion** row — a cell surface that INCLUDES another
/// cell's finalized field, with the provenance receipt shown. Built from the REAL
/// [`TranscludedField`] (the verified cross-cell finalized read), so the displayed
/// commitment + receipt are drawn from a genuine, verified, quorum-finalized fetch
/// — a forged or un-finalized quote could not have been opened.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transclusion {
    /// The host cell (the page doing the including).
    pub host: CellId,
    /// The source cell (the page whose field is transcluded).
    pub source: CellId,
    /// The transcluded field — the source's finalized content commitment
    /// (short-hex), drawn from the real [`web_aff::transclusion::Provenance`]; the
    /// field the host includes by reference (`content_hash == blake3(bytes)`).
    pub transcluded_field: String,
    /// The provenance RECEIPT: the cited receipt-stream Merkle leaf (short-hex) the
    /// quote is pinned to — the immutable past the citation dates, verified to be
    /// in the committed stream. Shown so the inclusion is checkable, not trusted.
    pub provenance_receipt: String,
    /// Whether the source's read was quorum-FINALIZED — the real
    /// [`TranscludedField::include`] REFUSES a non-finalized read, so this is
    /// always `true` for an opened transclusion (a transclusion quotes finalized
    /// state); a non-finalized source becomes `name`d-next, not shown.
    pub source_finalized: bool,
}

/// **Semi-reinteractive transclusion = powerbox × transclusion.**
///
/// A plain [`Transclusion`] is **read-only**: it is the verified cross-cell finalized
/// READ (the bytes the source committed, with provenance), and that read is *free* —
/// no authority over the source is conferred by quoting it (the membrane non-amp:
/// `TranscludedField::project_for` hands a viewer at most their own held authority).
/// A quote is a read, never a key.
///
/// **Semi-reinteractive** lifts exactly one rung higher, and ONLY through the
/// powerbox: if the user designates it, the transclusion carries an **attenuated
/// AFFORDANCE capability** — the host document can FIRE one of the source's
/// affordances (attenuated to what the user conferred), not merely read it. The read
/// stays the free verified observation; the *interact* is a powerbox-mediated
/// attenuated grant (a real [`crate::powerbox::Powerbox::grant`] turn that mints a
/// cap reaching the source into the host's c-list). So:
///
/// - a plain transclusion → read-only (no affordance fires);
/// - a powerbox-upgraded transclusion → fires EXACTLY the granted (attenuated)
///   affordance and **no more** (an affordance needing wider authority than the user
///   conferred is still refused, by the same real `is_attenuation` the affordance
///   surface gates on).
///
/// This is the powerbox's whole guarantee applied to a quote: the host never sees the
/// source's namespace, gets precisely the one designated, attenuated affordance, and
/// the grant is a real verified turn. It reinvents nothing — it composes the proven
/// [`TranscludedField`] read with the proven powerbox grant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemiReinteractiveTransclusion {
    /// The underlying read-only transclusion (the verified finalized READ). Always
    /// present — the read is free and unconditional.
    pub read: Transclusion,
    /// Whether the powerbox has UPGRADED this quote to interactive. `false` = a plain
    /// read-only transclusion (the default); `true` = the user designated it and the
    /// host now holds an attenuated affordance cap reaching the source.
    pub interactive: bool,
    /// IF upgraded: the single affordance name the host may now fire on the source
    /// (the one the user designated). `None` for a read-only transclusion.
    pub granted_affordance: Option<String>,
    /// IF upgraded: the attenuated authority the powerbox conferred over the source —
    /// the ceiling the granted affordance fires at. The host can fire affordances
    /// whose `required ⊆ conferred`, and NO wider ones (the same real `is_attenuation`
    /// gate). `None` for a read-only transclusion.
    pub conferred_rights: Option<AuthRequired>,
}

impl SemiReinteractiveTransclusion {
    /// A plain, **read-only** transclusion — the verified finalized read, no interact.
    /// This is what a transclusion is by default: a quote you can check, not act on.
    pub fn read_only(read: Transclusion) -> Self {
        SemiReinteractiveTransclusion {
            read,
            interactive: false,
            granted_affordance: None,
            conferred_rights: None,
        }
    }

    /// Is this quote read-only (no powerbox upgrade)? Then no affordance may fire.
    pub fn is_read_only(&self) -> bool {
        !self.interactive
    }

    /// A one-line readout of the read-vs-interact state (for the panel + tests).
    pub fn affordance_note(&self) -> String {
        match (&self.granted_affordance, &self.conferred_rights) {
            (Some(name), Some(rights)) => format!(
                "INTERACTIVE (powerbox-upgraded): may fire `{name}` on the source, attenuated to {rights:?} — and no wider affordance"
            ),
            _ => "READ-ONLY: the verified quote is free; firing an affordance on the source needs a powerbox grant".to_string(),
        }
    }
}

/// One **rendered span** of a dreggverse document, projected to the panel — the
/// gpui-free row the cockpit renders for a single EDL [`Span`].
///
/// Each row is a real read of [`deos_web_cells::RenderedSpan`] (the resolved output of
/// [`DreggverseDocument::resolve_for`] through the viewer's [`Membrane`]): OWN content
/// renders its bytes verbatim; a reachable transcluded span renders the source's
/// VERIFIED cited-range bytes + its receipt-pinned provenance; a span the viewer cannot
/// read renders DARKENED — its provenance survives (the citation), its bytes withheld
/// (never forged, never substituted). Nothing here is hand-set — every field is drawn
/// from the genuine resolved span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DocumentSpanRow {
    /// The span kind, one of `own` / `quote` / `darkened` — what the reader sees.
    pub kind: DocumentSpanKind,
    /// The span's contributed TEXT: OWN content, the verified cited-range bytes, or
    /// (for a darkened span) the empty string (the viewer gets NO source bytes it
    /// lacks authority to read). UTF-8-lossy of the real `RenderedSpan::bytes()`.
    pub text: String,
    /// For a QUOTE or DARKENED span: the source `dregg://<cell>` it cites (the EEL
    /// anchor — "jump to source"). `None` for OWN content (no foreign source).
    pub source: Option<String>,
    /// For a QUOTE or DARKENED span: the cited byte range of the source (the EDL's
    /// "range r"), as `start..end` (or `start..` for whole). `None` for OWN content.
    pub range: Option<String>,
    /// For a QUOTE or DARKENED span: the receipt-pinned provenance — the source's
    /// content commitment (short-hex), so the quote is datable + recomputable. Drawn
    /// from the REAL [`deos_web_cells::Provenance`]. `None` for OWN content.
    pub content_commitment: Option<String>,
    /// For a QUOTE or DARKENED span: the cited receipt-stream leaf (short-hex) — the
    /// immutable past the citation is pinned to. `None` for OWN content.
    pub provenance_receipt: Option<String>,
}

/// What kind of rendered span a [`DocumentSpanRow`] is — the discriminant the panel
/// styles on (own content / a verified quote / a per-viewer darkened span).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DocumentSpanKind {
    /// The author's OWN content — bytes that belong to THIS document, no foreign
    /// provenance.
    Own,
    /// A verified transcluded span — the source's cited-range bytes, with provenance.
    Quote,
    /// A span the viewer's projection could not reach — DARKENED: provenance kept,
    /// bytes withheld (never forged).
    Darkened,
}

impl DocumentSpanKind {
    /// The one-word badge the panel shows for this span kind.
    pub fn badge(&self) -> &'static str {
        match self {
            DocumentSpanKind::Own => "own",
            DocumentSpanKind::Quote => "quote",
            DocumentSpanKind::Darkened => "darkened",
        }
    }
}

/// THE DREGGVERSE-DOCUMENT VIEW — a multi-span Xanadu document (Nelson's EDL made
/// honest) resolved PER-VIEWER, projected to the panel.
///
/// This is the rich EDL span model the cockpit's whole-field [`Transclusion`] could
/// not express: a document is an ordered list of [`Span`]s — OWN content interleaved
/// with byte-RANGE transclusions of peer cells — and it is resolved THROUGH the
/// viewer's [`Membrane`] by the REAL [`DreggverseDocument::resolve_for`]. A span the
/// viewer's projected fetch-allowlist cannot reach DARKENS (its provenance survives,
/// its bytes withheld). Everything load-bearing is the genuine machinery: the per-span
/// quote is the REAL verified cross-cell finalized read; the per-viewer darkening is
/// the REAL membrane projection meet ([`SurfaceCapability::may_fetch`]); the document
/// rides the SAME `web` [`WebOfCells`] the browser already built (no parallel fetch).
///
/// The view is built gpui-free (so it is `cargo test`-able — a test asserts the
/// composed text + the darkened span + the surviving provenance are real); the cockpit
/// renders exactly these rows.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DreggverseDocumentView {
    /// The document's title (a short label for the panel section).
    pub title: String,
    /// The rendered spans, in document order — the panel renders these edge-to-edge.
    pub spans: Vec<DocumentSpanRow>,
    /// The **composed text** the viewer sees — every span's contribution concatenated
    /// in document order (OWN content + each reachable quote's cited bytes; a darkened
    /// span contributes NOTHING). The honest per-viewer render. Drawn from the REAL
    /// [`deos_web_cells::RenderedDocument::composed_text`].
    pub composed_text: String,
    /// How many spans the EDL has in total (the document's full shape).
    pub span_count: usize,
    /// How many spans rendered as QUOTES the viewer COULD read (verified, present).
    pub quote_count: usize,
    /// How many spans were DARKENED for this viewer (could not read — bytes withheld).
    /// `0` for a full-authority render; positive for a weaker viewer whose projection
    /// withheld at least one span.
    pub darkened_count: usize,
    /// Whether the document rendered FULLY for this viewer (no spans darkened).
    pub full: bool,
    /// The viewer's authority note — a one-line readout of WHY some spans may be
    /// darkened (the per-viewer fetch-allowlist the membrane projected).
    pub viewer_note: String,
}

/// THE WEB-OF-CELLS BROWSER MODEL — the whole `dregg://` docuverse as the cockpit
/// browses it, built fresh from the live [`World`]. The numbers + addresses +
/// attestations it shows are the running image's actual cells.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WebCellsBrowser {
    /// The viewer identity the surface is projected FOR (the cockpit's own
    /// principal) — short-hex. The affordance rows are exactly what THIS identity
    /// is cleared for.
    pub viewer: CellId,
    /// The viewer's authority tier name (the `AuthRequired` the cockpit holds over
    /// the surface) — what decides the progressive attenuation.
    pub viewer_tier: String,
    /// Every addressable `dregg://` cell in the web of cells (one per live World
    /// cell), with its attested origin chrome.
    pub cells: Vec<CellRow>,
    /// The currently-opened cell's address (the focused row), if any.
    pub opened: Option<CellId>,
    /// The opened cell's affordance surface, AS PROJECTED FOR THE VIEWER — only
    /// the affordances the cockpit's caps authorize (progressive attenuation).
    pub affordances: Vec<AffordanceRow>,
    /// How many affordances the surface declares in total (so the panel can show
    /// "you see N of M — the rest are attenuated away by your caps").
    pub affordances_declared: usize,
    /// The opened surface's REHYDRATION liveness-type badge — DERIVED from the
    /// attested fetch's interaction log (LIVE / REPLAYED-DETERMINISTIC /
    /// RECONSTRUCTED-APPROXIMATE), so the system cannot lie about which kind of
    /// true the reacquisition is.
    pub rehydration_badge: String,
    /// ONE Ted-Nelson transclusion (the host cell including the source cell's
    /// finalized field with provenance), if at least two cells exist.
    pub transclusion: Option<Transclusion>,
    /// A MULTI-SPAN dreggverse document (Nelson's EDL made honest), resolved
    /// PER-VIEWER through the real membrane — OWN content + byte-range quotes of peer
    /// cells, with any unreachable span DARKENED for this viewer. The rich EDL span
    /// model the whole-field [`Transclusion`] above could not express. `None` only if
    /// the web has too few cells to compose a multi-source document.
    pub document: Option<DreggverseDocumentView>,
    /// THE SERVO LAYER, LIVE (feature `servo`): the opened cell's attested
    /// `dregg://` page rasterized to a real, cap-gated SWGL [`RgbaFrame`] —
    /// the FIRST real rendered `dregg://` CONTENT in the tab (what
    /// [`WebCellsBrowser::servo_layer_note`] only NAMED). Populated in
    /// [`WebCellsBrowser::build`] via `servo_render::render_dregg_page`
    /// through the SAME held [`SurfaceCapability`] the affordance projection
    /// uses (an out-of-cap origin is refused in-band → `None`). The cockpit
    /// paints it with a gpui `img()`; `None`/feature-off falls back to the
    /// `servo_layer_note()` placeholder. Absent in the default build.
    #[cfg(feature = "servo")]
    pub rendered_tile: Option<servo_render::RgbaFrame>,
}

impl WebCellsBrowser {
    /// Build the browser model from the live world, opening `opened` (if any) to
    /// its per-viewer affordance surface. `viewer` is the cockpit's own principal
    /// (the identity the surface is projected for); `viewer_rights` is the
    /// authority it holds over the surface (what gates the attenuation).
    ///
    /// This is the single source of the panel's content — the cockpit renders
    /// exactly these rows, so the `cargo test` that asserts they are real +
    /// attested + cap-projected proves the rendered tree browses the real web of
    /// cells.
    pub fn build(
        world: &World,
        viewer: CellId,
        viewer_rights: AuthRequired,
        opened: Option<CellId>,
    ) -> Self {
        // Build a REAL web of cells: publish each live World cell as a dregg://
        // page whose content is a genuine description of the cell (drawn from live
        // ledger state — its balance, its cap count, its address), then FETCH each
        // back through the real attested-fetch path. Each row carries a real
        // AttestedResource (verified) + a real OriginChrome (ledger-drawn).
        let mut web = WebOfCells::new(3);

        // Stable per-cell seeds so the published origin cells are deterministic
        // across frames (the browser address bar is stable as the image evolves).
        let mut rows: Vec<CellRow> = Vec::new();
        let mut published: Vec<(CellId, DreggUri, AttestedResource, OriginChrome)> = Vec::new();

        let ledger_cells: Vec<(CellId, i64, usize)> = world
            .ledger()
            .iter()
            .map(|(id, c)| (*id, c.state.balance(), c.capabilities.len()))
            .collect();

        for (seed, (cell, balance, caps)) in ledger_cells.iter().enumerate() {
            let body = page_body_for_cell(cell, *balance, *caps);
            let url = format!("dregg://cell/{}", reflect::short_hex(&cell.0));
            // publish() seeds a FRESH origin cell (the dregg:// page is its own
            // cell); we key the row by the WORLD cell it describes.
            let uri = web.publish(seed as u8, body.as_bytes(), &url);
            match web.fetch(&uri) {
                Ok((resource, chrome)) => {
                    let attested = resource.verify().is_ok();
                    rows.push(CellRow {
                        cell: *cell,
                        uri: uri.to_uri_string(),
                        chrome_badge: chrome.badge(),
                        attested,
                        content_commitment: reflect::short_hex(&resource.content_hash),
                        committed_url: chrome.committed_url.clone(),
                        preview: preview_of(&resource.content_bytes),
                    });
                    published.push((*cell, uri, resource, chrome));
                }
                Err(e) => {
                    // A dead/unattested link is shown honestly, never hidden.
                    rows.push(CellRow {
                        cell: *cell,
                        uri: uri.to_uri_string(),
                        chrome_badge: format!("dregg:// (fetch failed: {e:?})"),
                        attested: false,
                        content_commitment: "—".to_string(),
                        committed_url: Some(url),
                        preview: format!("(no attested content: {e:?})"),
                    });
                }
            }
        }

        // Resolve the opened cell (default: the first addressable cell, so the
        // panel always shows a live surface rather than an empty pane).
        let opened = opened
            .filter(|o| rows.iter().any(|r| &r.cell == o))
            .or_else(|| rows.first().map(|r| r.cell));

        // Project the opened cell's affordance surface FOR THE VIEWER. The surface
        // is the genuine web-surface AffordanceSurface; the viewer's authority is a
        // real web-surface SurfaceCapability over the cell; project_for runs the
        // real is_attenuation gate.
        let mut affordances = Vec::new();
        let mut affordances_declared = 0;
        let mut rehydration_badge =
            Rehydration::ReconstructedApproximate.badge().to_string();
        // THE SERVO LAYER: the opened cell's attested page rasterized to a real,
        // cap-gated SWGL frame (feature `servo`). Populated in the opened block.
        #[cfg(feature = "servo")]
        let mut rendered_tile: Option<servo_render::RgbaFrame> = None;

        if let Some(cell) = opened {
            let surface = affordance_surface_for(cell, viewer);
            affordances_declared = surface.affordances.len();

            let held = SurfaceCapability::root(cell, viewer_rights.clone());
            for aff in surface.project_for(&held) {
                affordances.push(AffordanceRow {
                    name: aff.name.clone(),
                    required: format!("{:?}", aff.required_rights),
                    effect: effect_label(&aff.effect_template),
                });
            }

            // DERIVE the rehydration liveness-type from the attested fetch's
            // interaction log: the opened surface's content arrived via a dregg://
            // ATTESTED fetch (witnessed in the graph), so — with the source
            // context gone (a snapshot, not the live scene) — it replays
            // deterministically. The value is COMPUTED, never assigned.
            if let Some((_, uri, resource, _)) = published.iter().find(|(c, ..)| *c == cell) {
                let mut log = InteractionLog::new();
                log.record_attested_fetch(uri.clone(), resource.attested_root.clone());
                // sources_reachable = false: a browsed surface is a snapshot we
                // re-acquire, not a live socket to the origin context. The fetch
                // being witnessed makes it REPLAYED-DETERMINISTIC (confined), the
                // honest "every interaction went through the membrane" type.
                rehydration_badge = Rehydration::classify(&log, false).badge().to_string();

                // THE SERVO SEAM CALL: render the SAME attested page bytes the row
                // already verified into a real, cap-gated SWGL frame, through the
                // SAME held SurfaceCapability the affordance projection ran. The cap
                // gate is IN FRONT of the render — an out-of-cap origin is refused
                // in-band (then `frame()` is `None`, and the tab falls back to the
                // servo_layer_note placeholder). The frame is content-bound (distinct
                // attested bytes → a visibly distinct tile). 640×400 is a sane tab
                // surface; the SWGL rasterizer owns the buffer.
                #[cfg(feature = "servo")]
                {
                    let outcome = servo_render::render_dregg_page(
                        &held,
                        &uri.to_uri_string(),
                        &resource.content_bytes,
                        640,
                        400,
                    );
                    rendered_tile = outcome.frame().cloned();
                }
            }
        }

        // ONE Ted-Nelson transclusion via the REAL verified finalized read: the
        // opened (host) cell includes the NEXT addressable cell's finalized field
        // by reference, through `TranscludedField::include` (the genuine
        // content→commitment→receipt→root→quorum chain) — a forged/un-finalized
        // quote could not be opened.
        let transclusion = build_transclusion(&web, opened, &published);

        // A MULTI-SPAN dreggverse document (Nelson's EDL made honest), resolved
        // PER-VIEWER (the viewer = the cockpit's principal at `viewer_rights`)
        // through the REAL `DreggverseDocument::resolve_for`: OWN content + byte-range
        // quotes of two peer cells, with the span the viewer's projected
        // fetch-allowlist cannot reach DARKENED. This rides the SAME `web` the browser
        // already built (no parallel fetch); it is the rich EDL span model the
        // whole-field `transclusion` above cannot express.
        let document = build_document(&mut web, &published, viewer, &viewer_rights);

        WebCellsBrowser {
            viewer,
            viewer_tier: format!("{viewer_rights:?}"),
            cells: rows,
            opened,
            affordances,
            affordances_declared,
            rehydration_badge,
            transclusion,
            document,
            #[cfg(feature = "servo")]
            rendered_tile,
        }
    }

    /// **Fire an affordance through the REAL embedded executor.** This is the
    /// seam the web crate could only model, CLOSED: the affordance the web-surface
    /// surface projects carries a real [`dregg_turn::Effect`]; we instantiate it
    /// and hand it to the cockpit's [`crate::affordance::AffordanceIntent::fire_through_world`]
    /// — a verified turn through the live [`World`]. The executor EITHER commits (a
    /// real receipt) OR rejects (a guarantee fired) — both surfaced.
    ///
    /// The cap-gate that decides whether the affordance may fire AT ALL is the
    /// REAL `is_attenuation` (run by [`WebAffordanceSurface::fire`]); the gate that
    /// decides whether the resulting TURN commits is the real executor. Neither is
    /// faked. Returns the executor outcome, or the in-band `FireError` text if the
    /// viewer was not authorized for the affordance (the anti-ghost tooth).
    pub fn fire_affordance(
        world: &mut World,
        cell: CellId,
        viewer: CellId,
        viewer_rights: AuthRequired,
        affordance_name: &str,
    ) -> Result<FireOutcome, String> {
        let surface = affordance_surface_for(cell, viewer);
        let held = SurfaceCapability::root(cell, viewer_rights);
        // The web-surface fire runs the REAL is_attenuation gate (anti-ghost): an
        // unauthorized fire is refused IN-BAND here, before any executor turn.
        let intent = surface
            .fire(affordance_name, viewer, &held)
            .map_err(|e| format!("{e:?}"))?;

        // Lift the projected effect across the one-type bridge: the web-surface
        // affordance's effect IS the same dregg_turn::Effect the cockpit's
        // executor runs. Re-mint it as the cockpit's own AffordanceIntent and fire
        // it through the embedded executor (the closed seam).
        let cockpit_intent = crate::affordance::AffordanceIntent {
            surface_cell: cell,
            affordance: affordance_name.to_string(),
            actor: viewer,
            effect: intent.effect,
        };
        Ok(cockpit_intent.fire_through_world(world))
    }

    // ── SEMI-REINTERACTIVE TRANSCLUSION (powerbox × transclusion) ──────────────

    /// **Upgrade a read-only transclusion to interactive — through the POWERBOX.**
    ///
    /// The read ([`Transclusion`]) is already the free verified observation. This lifts
    /// it one rung: it runs a REAL [`crate::powerbox::Powerbox::grant`] so the granting
    /// `principal` (the cockpit user) confers an ATTENUATED cap reaching the
    /// transclusion's SOURCE into its HOST document's c-list. The host can then fire one
    /// of the source's affordances, attenuated to `confer_rights` — but ONLY if the user
    /// actually holds authority over the source (`mint_needs_held_factory`) and
    /// `confer_rights ⊆` the user's held authority (`gen_conferral_is_attenuation`),
    /// both enforced by the real powerbox + executor.
    ///
    /// Returns the upgraded [`SemiReinteractiveTransclusion`] (with the conferred rights
    /// + the affordance the host may now fire) on a real grant, or the read-only quote
    /// UNCHANGED plus the denial reason if the powerbox refused (no authority conferred —
    /// the read is still free, the interact is simply not unlocked).
    pub fn upgrade_transclusion_via_powerbox(
        world: &mut World,
        read: Transclusion,
        principal: CellId,
        affordance_name: &str,
        confer_rights: AuthRequired,
    ) -> Result<SemiReinteractiveTransclusion, (SemiReinteractiveTransclusion, String)> {
        // The interact is a powerbox-mediated grant: confer an attenuated cap reaching
        // the SOURCE into the HOST document. The powerbox enforces held-authority +
        // non-amplification; the executor is the backstop. A denial leaves the read
        // free and the quote read-only.
        let outcome = crate::powerbox::Powerbox::grant(
            world,
            principal,
            read.host,   // the host document is the grantee (it gains the affordance cap)
            read.source, // reaching the transcluded source cell
            confer_rights.clone(),
        );
        match outcome {
            crate::powerbox::PowerboxOutcome::Granted { conferred, .. } => {
                Ok(SemiReinteractiveTransclusion {
                    read,
                    interactive: true,
                    granted_affordance: Some(affordance_name.to_string()),
                    conferred_rights: Some(conferred.conferred_rights),
                })
            }
            crate::powerbox::PowerboxOutcome::Denied { reason } => {
                Err((SemiReinteractiveTransclusion::read_only(read), reason))
            }
        }
    }

    /// **Fire an affordance on the transcluded SOURCE — only what the powerbox granted.**
    ///
    /// On a READ-ONLY transclusion this is refused immediately (a quote is a read, not a
    /// key): no powerbox grant, no interact. On an INTERACTIVE (powerbox-upgraded)
    /// transclusion, the host fires the source's affordance at the CONFERRED attenuation
    /// — so an affordance whose `required ⊆ conferred` fires (through the real embedded
    /// executor, a verified turn), and a WIDER affordance is refused IN-BAND by the same
    /// real `is_attenuation` the affordance surface gates on (the anti-ghost tooth). The
    /// host can fire exactly the granted affordance and no more.
    pub fn fire_transcluded_affordance(
        world: &mut World,
        upgraded: &SemiReinteractiveTransclusion,
        affordance_name: &str,
    ) -> Result<FireOutcome, String> {
        let Some(conferred) = upgraded.conferred_rights.clone() else {
            return Err(
                "READ-ONLY transclusion: a quote is a read, not a key — firing an affordance on \
                 the source needs a powerbox grant first (no authority was conferred)"
                    .to_string(),
            );
        };
        // The host now fires the SOURCE's affordance surface, but holding ONLY the
        // conferred (attenuated) authority — so the real is_attenuation gate admits
        // exactly the affordances `required ⊆ conferred`, and refuses anything wider.
        // The host (the upgraded read's host) is the actor; the source is the surface.
        Self::fire_affordance(
            world,
            upgraded.read.source,
            upgraded.read.host,
            conferred,
            affordance_name,
        )
    }

    /// The SERVO layer note — stated in the model so it is VISIBLE in the panel,
    /// not buried in a doc. The browser renders affordance SURFACES natively
    /// today; embedding servo to render actual `dregg://` web CONTENT is the
    /// named next layer.
    pub fn servo_layer_note(&self) -> &'static str {
        "NATIVE today: this browser renders cap-gated affordance SURFACES (the \
         dregg:// addressing, the attested fetch, the per-viewer attenuation, the \
         rehydration liveness-type). NEXT layer: embed servo to render actual \
         dregg:// web CONTENT — the WebViewDelegate cap-gate (where the \
         web-surface crate's MockSurface stands), the servo Stage-A renderer lane."
    }

    /// Every line of real text the browser renders, flattened — used by tests to
    /// assert the panel speaks real, attested, cap-projected text about the real
    /// cells (the exact gpui tree content, so non-empty here == non-empty tree).
    pub fn all_text(&self) -> Vec<String> {
        let mut out = Vec::new();
        out.push(format!(
            "web of cells — viewer {} holds {} over the surface",
            reflect::short_hex(&self.viewer.0),
            self.viewer_tier
        ));
        for r in &self.cells {
            out.push(r.uri.clone());
            out.push(r.chrome_badge.clone());
            out.push(format!(
                "attested={} · commitment {} · {}",
                r.attested, r.content_commitment, r.preview
            ));
        }
        if let Some(o) = self.opened {
            out.push(format!("opened dregg://{}", reflect::short_hex(&o.0)));
        }
        out.push(format!(
            "affordances projected for you: {} of {} declared (the rest attenuated by your caps)",
            self.affordances.len(),
            self.affordances_declared
        ));
        for a in &self.affordances {
            out.push(format!("· {} (requires {}) → {}", a.name, a.required, a.effect));
        }
        out.push(format!("rehydration: {}", self.rehydration_badge));
        if let Some(t) = &self.transclusion {
            out.push(format!(
                "transcludes field {} from dregg://{} (receipt {}, finalized={})",
                t.transcluded_field,
                reflect::short_hex(&t.source.0),
                t.provenance_receipt,
                t.source_finalized
            ));
        }
        out.push(self.servo_layer_note().to_string());
        out
    }
}

// ── the model-building helpers (pure; each names the real web-of-cells primitive) ──

/// The page body a `dregg://` cell serves: a real, human-readable description of
/// the World cell drawn from LIVE ledger state. This is the attested content —
/// the bytes the receipt + quorum-signed root bind.
fn page_body_for_cell(cell: &CellId, balance: i64, caps: usize) -> String {
    format!(
        "<dregg-cell id=\"{}\"><balance>{}</balance><capabilities>{}</capabilities>\
         <p>A live capability-secured cell in the verified image. Every interaction \
         with it is a verified turn; this page is served from its committed state.</p>\
         </dregg-cell>",
        reflect::short_hex(&cell.0),
        balance,
        caps
    )
}

/// A one-line preview of the served page bytes (the real attested content).
fn preview_of(bytes: &[u8]) -> String {
    let s = String::from_utf8_lossy(bytes);
    let trimmed: String = s.chars().take(72).collect();
    if s.len() > 72 {
        format!("{trimmed}…")
    } else {
        trimmed
    }
}

/// Build the genuine web-surface [`AffordanceSurface`] a cell publishes — the
/// canonical doc-cell surface {view, comment, edit, admin} on the clean three-tier
/// rights chain `Signature ⊂ Either ⊂ None`, each carrying a REAL
/// [`dregg_turn::Effect`] template (the turn the executor would run). `viewer` is
/// the grantee an `admin` grant would target. This is the web-surface
/// `AffordanceSurface`, NOT a parallel one — its `project_for` runs the real
/// `is_attenuation`, and its effects are the genuine `Effect` the cockpit's
/// executor fires.
fn affordance_surface_for(cell: CellId, viewer: CellId) -> WebAffordanceSurface {
    WebAffordanceSurface::new(cell)
        // view: tier-1 (any authenticated reader holds Signature) → logs an access
        // event (a real EmitEvent turn).
        .declare(CellAffordance::new(
            "view",
            AuthRequired::Signature,
            emit_event(cell),
        ))
        // comment: tier-2 (the editor tier holds Either) → an EmitEvent turn.
        .declare(CellAffordance::new(
            "comment",
            AuthRequired::Either,
            emit_event(cell),
        ))
        // edit: tier-2 → writes a state field (a real SetField turn).
        .declare(CellAffordance::new(
            "edit",
            AuthRequired::Either,
            set_field(cell, 1),
        ))
        // admin: tier-3 (only a root holder of None clears it) → hands out a
        // capability (a real GrantCapability turn).
        .declare(CellAffordance::new(
            "admin",
            AuthRequired::None,
            grant_cap(cell, viewer),
        ))
}

/// A read logs an access event — a real [`Effect::EmitEvent`] turn.
fn emit_event(cell: CellId) -> Effect {
    Effect::EmitEvent {
        cell,
        event: web_aff::dregg_turn_reexport::Event {
            topic: [1u8; 32],
            data: vec![],
        },
    }
}

/// An edit writes a state field — a real [`Effect::SetField`] turn.
fn set_field(cell: CellId, index: usize) -> Effect {
    Effect::SetField {
        cell,
        index,
        value: [7u8; 32],
    }
}

/// An admin grant hands out a capability — a real [`Effect::GrantCapability`]
/// turn (the genuine grant the executor's no-amplification gate checks).
fn grant_cap(from: CellId, to: CellId) -> Effect {
    Effect::GrantCapability {
        from,
        to,
        cap: web_aff::dregg_turn_reexport::CapabilityRef {
            target: to,
            slot: 0,
            permissions: AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    }
}

/// A stable, human label for a real [`Effect`] (the `Effect` enum is not
/// `PartialEq`/`Display`; this is the readout the panel shows). Uses the
/// web-surface [`web_aff::EffectSummary`] — a readout of the GENUINE template.
fn effect_label(effect: &Effect) -> String {
    match web_aff::EffectSummary::of(effect) {
        web_aff::EffectSummary::SetField { index, .. } => format!("SetField(slot {index})"),
        web_aff::EffectSummary::EmitEvent { .. } => "EmitEvent".to_string(),
        web_aff::EffectSummary::GrantCapability { .. } => "GrantCapability".to_string(),
        web_aff::EffectSummary::Transfer { amount, .. } => format!("Transfer({amount})"),
        web_aff::EffectSummary::RevokeCapability { slot, .. } => format!("RevokeCapability(slot {slot})"),
        web_aff::EffectSummary::IncrementNonce { .. } => "IncrementNonce".to_string(),
        web_aff::EffectSummary::Other { tag } => tag.to_string(),
    }
}

/// Build ONE Ted-Nelson transclusion via the REAL [`TranscludedField::include`]:
/// the opened (host) cell includes the NEXT addressable cell's finalized field BY
/// REFERENCE — a genuine VERIFIED cross-cell finalized read
/// (content→commitment→receipt→receipt-stream root→quorum). The displayed
/// commitment + cited receipt are drawn from the real
/// [`web_aff::transclusion::Provenance`]; a forged or un-finalized quote could not
/// have been opened. Returns `None` if fewer than two cells exist (nothing to
/// transclude) or if the source read does not verify/finalize (then the
/// transclusion is honestly absent, never a faked inclusion).
fn build_transclusion(
    web: &WebOfCells,
    opened: Option<CellId>,
    published: &[(CellId, DreggUri, AttestedResource, OriginChrome)],
) -> Option<Transclusion> {
    let host = opened?;
    let host_idx = published.iter().position(|(c, ..)| *c == host)?;
    // The source is the NEXT addressable cell (wrap to the first), so a host
    // always has a distinct source when ≥2 cells exist.
    if published.len() < 2 {
        return None;
    }
    let source_idx = (host_idx + 1) % published.len();
    let (source_cell, source_uri, ..) = &published[source_idx];

    // THE REAL VERIFIED FINALIZED READ — `transclusion_is_observed_finalized_read`.
    // This re-fetches the source through the attested path, runs the genuine
    // provenance chain, and REFUSES a forged (`ProvenanceUnverified`) or
    // un-finalized (`NotFinalized`) quote. We show a transclusion ONLY on success.
    match TranscludedField::include(web, source_uri) {
        Ok(field) => {
            let cite = field.cite();
            Some(Transclusion {
                host,
                source: *source_cell,
                transcluded_field: reflect::short_hex(&cite.content_hash),
                provenance_receipt: reflect::short_hex(&cite.receipt_hash),
                source_finalized: cite.finalized,
            })
        }
        // A source that does not verify/finalize is honestly NOT transcluded (the
        // quote could not be opened) — never a faked inclusion.
        Err(TransclusionError::Fetch(_))
        | Err(TransclusionError::ProvenanceUnverified(_))
        | Err(TransclusionError::NotFinalized) => None,
    }
}

/// The stable per-viewer fetch-allowlist origin of a transcluded span's source cell —
/// the SAME origin grammar [`DreggverseDocument::resolve_for`] checks the viewer's
/// projected fetch-allowlist against (`deos_web_cells`'s `span_origin` for a raw-cell
/// span: the bundle-asset origin shape with a stable `(document)` asset name). We name
/// it through the crate's PUBLIC [`deos_web_cells::WebBundle::asset_origin`] so the
/// allowlist we hand the viewer membrane is the GENUINE one `resolve_for` meets — never
/// a parallel key.
fn doc_span_origin(cell: CellId) -> String {
    deos_web_cells::WebBundle::asset_origin(cell, "(document)")
}

/// Build a MULTI-SPAN dreggverse document (Nelson's EDL made honest), resolved
/// PER-VIEWER through the REAL [`Membrane`], and project it to gpui-free panel rows.
///
/// This is the WELD: the rich EDL span model `deos-web-cells` ships
/// ([`DreggverseDocument`]) rendered in the cockpit's web-of-cells browser. It rides the
/// SAME `web` [`WebOfCells`] the browser already built (no parallel fetch, no parallel
/// attestation): we publish two NEW raw source cells into it (a PUBLIC paragraph and a
/// RESTRICTED paragraph), author a document that quotes BYTE RANGES of both interleaved
/// with the viewer's OWN content, then resolve it for the cockpit's viewer through
/// [`DreggverseDocument::resolve_for`].
///
/// The teeth, all REAL (no faked anything):
///
/// - **OWN bytes** — the document's own authored spans render verbatim (the author's,
///   under the document's own authority);
/// - **a verified peer quote** — the PUBLIC span is the REAL verified cross-cell
///   finalized read of the public source's cited byte range, carrying its
///   receipt-pinned provenance (a forged/absent/un-finalized source would be REFUSED);
/// - **a per-viewer DARKENED span** — the RESTRICTED span's origin is NOT in the
///   viewer's projected fetch-allowlist, so the REAL [`SurfaceCapability::may_fetch`]
///   meet withholds it: it renders darkened (its provenance survives — the citation —,
///   its bytes withheld; never forged, never substituted).
///
/// The `lineage` the document's spans are served under (one publisher's docuverse)
/// permits BOTH origins; the VIEWER membrane (the cockpit principal at `viewer_rights`)
/// is scoped to ONLY the public origin — so the meet darkens the restricted span. This
/// mirrors the `deos-web-cells` proven recipe
/// (`a_weaker_viewer_sees_darkened_spans_not_the_source_values`), against the live
/// browser's web. Returns `None` only if the web is too small to anchor the document's
/// publisher cell (no opened cells at all).
fn build_document(
    web: &mut WebOfCells,
    published: &[(CellId, DreggUri, AttestedResource, OriginChrome)],
    viewer: CellId,
    viewer_rights: &AuthRequired,
) -> Option<DreggverseDocumentView> {
    // The document needs a publisher anchor cell (any live cell of the image — the
    // lineage's backing surface). With no cells at all there is no docuverse to author.
    let publisher = published.first().map(|(c, ..)| *c)?;

    // (1) Publish two NEW raw source cells into the SAME web the browser built — a
    //     PUBLIC paragraph and a RESTRICTED paragraph. `publish` seeds a real surface
    //     cell committing the bytes (a genuine finalized read source). We pick seeds
    //     well clear of the per-cell page seeds (those are `0..ledger_cells.len()` as
    //     u8) so these document sources do not collide.
    let public_body: &[u8] = b"the PUBLIC paragraph anyone may read";
    let secret_body: &[u8] = b"the RESTRICTED paragraph - authority-gated";
    let public_src = web.publish(0xD0, public_body, "dregg://doc/public");
    let secret_src = web.publish(0xD1, secret_body, "dregg://doc/restricted");

    let public_origin = doc_span_origin(public_src.cell);
    let secret_origin = doc_span_origin(secret_src.cell);

    // (2) Author the EDL: OWN intro, a BYTE RANGE of the public source, OWN connective,
    //     a BYTE RANGE of the restricted source. The ranges quote a SPAN of each source
    //     (Nelson's "characters start..end of cell X"), not the whole — the rich span
    //     model. `"the PUBLIC paragraph anyone may read"` → bytes 4..20 = "PUBLIC paragraph".
    let public_quote = SpanRange::new(4, 20); // "PUBLIC paragraph"
    let secret_quote = SpanRange::new(4, 24); // "RESTRICTED paragraph"
    let doc = DreggverseDocument::from_spans(vec![
        Span::own(b"This document quotes ".to_vec()),
        Span::transclude_range(public_src.clone(), public_quote),
        Span::own(b" and a darkened ".to_vec()),
        Span::transclude_range(secret_src.clone(), secret_quote),
        Span::own(b".".to_vec()),
    ]);

    // (3) The source-side lineage the spans are served under (one publisher's
    //     docuverse): backed by the publisher cell, `Either` authority, fetch-allowlist
    //     permitting BOTH span origins. A full-authority viewer would reach both.
    let lineage = SurfaceCapability::scoped(
        publisher,
        AuthRequired::Either,
        [public_origin.clone(), secret_origin.clone()],
        [],
    );

    // (4) The VIEWER membrane — the cockpit's principal at its actual `viewer_rights`,
    //     scoped to ONLY the public span's origin. The restricted span's origin is
    //     absent from the viewer's fetch-allowlist, so the REAL membrane meet
    //     (`project` ∧ `may_fetch`) withholds it → it darkens. The rights still meet the
    //     `Either` lineage (Signature/Either/None all attenuate Either), so darkening is
    //     driven by the fetch-allowlist (the genuine `load_web_resource` gate), exactly
    //     as a confined viewer's reach is.
    let viewer_membrane = Membrane::new(SurfaceCapability::scoped(
        viewer,
        viewer_rights.clone(),
        [public_origin.clone()],
        [],
    ));

    // (5) RESOLVE PER-VIEWER through the REAL `resolve_for`. A structural failure
    //     (a vanished source) is honestly surfaced as no document rather than a faked
    //     render; the expected "viewer lacks authority" case is a DARKENED span, not an
    //     error (the whole point).
    let rendered = doc
        .resolve_for(web, &viewer_membrane, &lineage)
        .ok()?;

    // (6) Project the resolved spans to gpui-free rows — every field a real read of the
    //     genuine `RenderedSpan` (OWN bytes / verified quote bytes + provenance /
    //     darkened with surviving provenance, no bytes).
    let spans: Vec<DocumentSpanRow> = rendered
        .spans()
        .iter()
        .map(|s| match s {
            RenderedSpan::Own(bytes) => DocumentSpanRow {
                kind: DocumentSpanKind::Own,
                text: String::from_utf8_lossy(bytes).into_owned(),
                source: None,
                range: None,
                content_commitment: None,
                provenance_receipt: None,
            },
            RenderedSpan::Transcluded { bytes, provenance, range, .. } => DocumentSpanRow {
                kind: DocumentSpanKind::Quote,
                text: String::from_utf8_lossy(bytes).into_owned(),
                source: Some(provenance.source.to_uri_string()),
                range: Some(render_range(range)),
                content_commitment: Some(reflect::short_hex(&provenance.content_hash)),
                provenance_receipt: Some(reflect::short_hex(&provenance.receipt_hash)),
            },
            RenderedSpan::Darkened { provenance, range, .. } => DocumentSpanRow {
                // A darkened span yields NO source bytes (the viewer gets none it lacks
                // authority to read) — but its provenance + citation survive.
                kind: DocumentSpanKind::Darkened,
                text: String::new(),
                source: Some(provenance.source.to_uri_string()),
                range: Some(render_range(range)),
                content_commitment: Some(reflect::short_hex(&provenance.content_hash)),
                provenance_receipt: Some(reflect::short_hex(&provenance.receipt_hash)),
            },
        })
        .collect();

    let quote_count = spans
        .iter()
        .filter(|r| r.kind == DocumentSpanKind::Quote)
        .count();

    Some(DreggverseDocumentView {
        title: "A dreggverse document (Nelson's EDL, made honest)".to_string(),
        composed_text: rendered.composed_text().unwrap_or_default(),
        span_count: rendered.spans().len(),
        quote_count,
        darkened_count: rendered.darkened_count(),
        full: rendered.is_full(),
        viewer_note: format!(
            "viewer {} ({viewer_rights:?}) — fetch-allowlist permits the public source's \
             origin but NOT the restricted one, so the restricted span darkens \
             (provenance kept, bytes withheld; the REAL membrane meet, never a forgery)",
            reflect::short_hex(&viewer.0)
        ),
        spans,
    })
}

/// Render a [`SpanRange`] as the EDL's `start..end` (or `start..` when the range runs to
/// the end of the source) — the cited byte range a quote/darkened span shows.
fn render_range(range: &SpanRange) -> String {
    if range.end == usize::MAX {
        format!("{}..", range.start)
    } else {
        format!("{}..{}", range.start, range.end)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::demo_world;

    /// The viewer rights the cockpit holds for the tests (the EDITOR tier:
    /// `Either` clears view/comment/edit but NOT admin — a clean attenuation
    /// witness).
    fn editor_rights() -> AuthRequired {
        AuthRequired::Either
    }

    #[test]
    fn browser_lists_the_real_attested_dregg_cells_of_the_live_image() {
        let (world, anchors) = demo_world();
        let viewer = anchors[2]; // the "user" anchor — the cockpit's principal
        let browser = WebCellsBrowser::build(&world, viewer, editor_rights(), None);

        // One addressable dregg:// cell per live World cell.
        assert_eq!(
            browser.cells.len(),
            world.cell_count(),
            "every live cell is addressable in the web of cells"
        );
        assert!(!browser.cells.is_empty(), "the demo image has cells to browse");

        for row in &browser.cells {
            // Each row is a real dregg:// address (64 hex chars for the cell id).
            assert!(row.uri.starts_with("dregg://"), "a row is a dregg:// address");
            assert_eq!(row.uri.len(), "dregg://".len() + 64, "the address is the content-addressed cell id");
            // The full attestation chain VERIFIED — the page is the page the
            // origin committed (content-addressed + receipt-in-stream + quorum).
            assert!(row.attested, "every browsed cell's attestation chain verifies");
            // The trusted-path chrome is drawn from the LEDGER (a dregg:// badge),
            // never the page.
            assert!(
                row.chrome_badge.starts_with("dregg://"),
                "the origin chrome is the ledger-drawn trusted-path badge"
            );
        }
    }

    #[test]
    fn opening_a_cell_projects_only_the_affordances_the_viewer_is_cleared_for() {
        // THE attenuation witness: the EDITOR tier (Either) sees view/comment/edit
        // but NOT admin (which requires the root None tier). progressive
        // enhancement → progressive ATTENUATION, via the REAL is_attenuation.
        let (world, anchors) = demo_world();
        let viewer = anchors[2];
        let opened = Some(anchors[0]); // open the treasury cell
        let browser = WebCellsBrowser::build(&world, viewer, editor_rights(), opened);

        assert_eq!(browser.opened, opened, "the requested cell is opened");
        // The surface DECLARES four affordances {view, comment, edit, admin}.
        assert_eq!(browser.affordances_declared, 4, "the surface declares four affordances");

        let names: Vec<&str> = browser.affordances.iter().map(|a| a.name.as_str()).collect();
        // The editor tier is cleared for view/comment/edit …
        assert!(names.contains(&"view"), "editor sees view");
        assert!(names.contains(&"comment"), "editor sees comment");
        assert!(names.contains(&"edit"), "editor sees edit");
        // … but NOT admin (the anti-ghost attenuation: it requires the root tier).
        assert!(
            !names.contains(&"admin"),
            "the editor tier is ATTENUATED away from admin — it requires the root None tier"
        );
        assert_eq!(browser.affordances.len(), 3, "editor sees 3 of 4 (admin attenuated)");
    }

    #[test]
    fn a_root_viewer_sees_strictly_more_than_an_editor_the_lattice_proof() {
        // The same surface projected for the ROOT tier (None) sees ALL four,
        // including admin — strictly MORE than the editor. Two viewers at
        // different authority get DIFFERENT projections of the SAME surface.
        let (world, anchors) = demo_world();
        let viewer = anchors[2];
        let opened = Some(anchors[0]);

        let editor = WebCellsBrowser::build(&world, viewer, AuthRequired::Either, opened);
        let root = WebCellsBrowser::build(&world, viewer, AuthRequired::None, opened);

        let root_names: Vec<&str> = root.affordances.iter().map(|a| a.name.as_str()).collect();
        assert!(root_names.contains(&"admin"), "the root tier sees admin");
        assert_eq!(root.affordances.len(), 4, "root sees all four affordances");
        assert!(
            root.affordances.len() > editor.affordances.len(),
            "the root viewer sees STRICTLY MORE than the editor — the attenuation lattice"
        );
    }

    #[test]
    fn the_opened_surface_carries_a_derived_rehydration_liveness_type() {
        // The liveness-type is DERIVED from the attested fetch (not hand-set): the
        // surface's content arrived via a dregg:// ATTESTED fetch (witnessed), and
        // the source context is gone (a snapshot) → REPLAYED-DETERMINISTIC, the
        // confined "every interaction went through the membrane" type.
        let (world, anchors) = demo_world();
        let browser = WebCellsBrowser::build(&world, anchors[2], editor_rights(), Some(anchors[0]));
        assert!(
            browser.rehydration_badge.starts_with("REPLAYED-DETERMINISTIC"),
            "the attested fetch yields the confined replay liveness-type, got: {}",
            browser.rehydration_badge
        );
    }

    #[test]
    fn it_shows_one_transcluded_field_with_a_provenance_receipt() {
        // The Ted-Nelson seam: the host cell includes the source cell's finalized
        // content commitment, with the source's serve-receipt as provenance — both
        // real reads of the attested fetch.
        let (world, anchors) = demo_world();
        let browser = WebCellsBrowser::build(&world, anchors[2], editor_rights(), Some(anchors[0]));
        let t = browser.transclusion.expect("≥2 cells → one transclusion");
        assert_ne!(t.host, t.source, "a transclusion includes a DISTINCT source cell");
        assert!(t.transcluded_field.len() >= 4, "the transcluded field is a real commitment");
        assert!(t.provenance_receipt.len() >= 4, "the provenance receipt is real");
        assert!(t.source_finalized, "the source's attestation finalized (quorum)");
    }

    #[test]
    fn firing_an_affordance_commits_a_real_verified_turn_through_the_embedded_executor() {
        // THE CLOSED SEAM: firing the editor-authorized `edit` affordance dispatches
        // its REAL effect through the embedded executor → a real receipt. This is
        // the web crate's named-not-closed seam, CLOSED in the cockpit.
        let (mut world, anchors) = demo_world();
        let viewer = anchors[0]; // the treasury — a powerful operator principal
        let cell = anchors[0];
        let receipts_before = world.receipts().len();

        let outcome = WebCellsBrowser::fire_affordance(
            &mut world,
            cell,
            viewer,
            AuthRequired::None, // root tier: clears every affordance
            "edit",
        )
        .expect("the root viewer is authorized for edit (in-band gate passes)");

        // The executor either committed (a real receipt) or refused (a guarantee
        // fired) — both are real verified-turn outcomes, neither faked. For an
        // operator editing its own cell's slot, it commits.
        assert!(
            outcome.is_committed(),
            "the affordance fired a real verified turn through the embedded executor: {outcome:?}"
        );
        assert!(
            world.receipts().len() > receipts_before,
            "the fire added a real receipt to the chain"
        );
    }

    #[test]
    fn firing_an_unauthorized_affordance_is_refused_in_band_the_anti_ghost_tooth() {
        // The anti-ghost tooth: the EDITOR tier firing `admin` (which requires the
        // root tier) is REFUSED IN-BAND by the real is_attenuation, before any
        // executor turn — never silently run.
        let (mut world, anchors) = demo_world();
        let err = WebCellsBrowser::fire_affordance(
            &mut world,
            anchors[0],
            anchors[0],
            AuthRequired::Either, // editor tier: does NOT clear admin
            "admin",
        )
        .unwrap_err();
        assert!(
            err.contains("Unauthorized"),
            "the editor firing admin is refused in-band (anti-ghost), got: {err}"
        );
    }

    #[test]
    fn the_browser_speaks_real_attested_text_about_the_real_cells() {
        // The anti-blank guarantee, mirroring landing.rs: the rendered panel
        // contains many lines of real text naming the real dregg:// cells, their
        // attestation, the per-viewer affordances, the liveness-type, and the
        // servo-next note.
        let (world, anchors) = demo_world();
        let browser = WebCellsBrowser::build(&world, anchors[2], editor_rights(), Some(anchors[0]));
        let text = browser.all_text();
        assert!(text.len() >= 12, "the panel renders many lines of real text, got {}", text.len());
        for line in &text {
            assert!(!line.trim().is_empty(), "every panel line is non-empty real text");
        }
        let blob = text.join("\n");
        // It names the genuine web-of-cells machinery.
        assert!(blob.contains("dregg://"), "names the dregg:// addressing");
        assert!(blob.contains("attested="), "shows the attestation verdict");
        assert!(blob.to_lowercase().contains("attenuat"), "names the progressive attenuation");
        assert!(blob.contains("rehydration:"), "names the rehydration liveness-type");
        // It names the servo NEXT layer honestly (integrated vs named-next).
        assert!(blob.contains("servo"), "names the servo next layer");
    }

    // ── SEMI-REINTERACTIVE TRANSCLUSION (powerbox × transclusion) tests ────────

    use crate::world::{make_open_cell, World};

    /// A world for the semi-reinteractive flow: a HOST document, a SOURCE cell (whose
    /// affordance surface is the canonical {view@Signature, comment/edit@Either,
    /// admin@None}), and a granting PRINCIPAL that holds `Signature` authority over the
    /// source (so it can confer at most a Signature-tier affordance — a real attenuation
    /// ceiling). A read-only [`Transclusion`] of source-by-host is returned too.
    /// Returns `(world, principal, transclusion)`.
    fn semi_reinteractive_world() -> (World, CellId, Transclusion) {
        let mut w = World::new();
        let host = w.genesis_cell(0x40, 0); // the document doing the including
        let source = w.genesis_cell(0x50, 0); // the cell whose field is transcluded

        // The granting principal holds a real (Signature-tier) cap reaching the source —
        // it legitimately holds source authority, so the powerbox can confer it.
        let mut principal_cell = make_open_cell(0x5A, 0);
        principal_cell
            .capabilities
            .grant(source, AuthRequired::Signature)
            .expect("fresh c-list slot for the source cap");
        let principal = w.genesis_install(principal_cell);

        // A read-only transclusion: host includes source's finalized field. (The fields
        // are display strings; the host/source ids are what the interact path acts on.)
        let read = Transclusion {
            host,
            source,
            transcluded_field: "abcd".to_string(),
            provenance_receipt: "ef01".to_string(),
            source_finalized: true,
        };
        (w, principal, read)
    }

    #[test]
    fn a_plain_transclusion_is_read_only_no_affordance_fires() {
        // THE READ-VS-ACT DISTINCTION (read-only half): a plain transclusion is the
        // free verified READ — a quote is a read, not a key. Firing an affordance on the
        // source is refused: no powerbox grant, no interact.
        let (mut world, _principal, read) = semi_reinteractive_world();
        let plain = SemiReinteractiveTransclusion::read_only(read);
        assert!(plain.is_read_only(), "a plain transclusion is read-only");
        assert!(plain.granted_affordance.is_none(), "no affordance is granted on a plain quote");

        let err = WebCellsBrowser::fire_transcluded_affordance(&mut world, &plain, "view")
            .expect_err("a read-only transclusion refuses to fire");
        assert!(
            err.contains("READ-ONLY") && err.contains("powerbox grant"),
            "the refusal names the read-only/powerbox-grant boundary, got: {err}"
        );
        assert!(plain.affordance_note().starts_with("READ-ONLY"));
    }

    #[test]
    fn a_powerbox_upgraded_transclusion_fires_exactly_the_granted_affordance_and_no_more() {
        // THE READ-VS-ACT DISTINCTION (interact half): the user designates the quote
        // through the powerbox, conferring a Signature-tier affordance reaching the
        // source. The host can now fire `view` (Signature ⊆ Signature) as a REAL
        // verified turn — but NOT `admin` (which needs the wider root tier): exactly the
        // granted affordance and no more, by the same real is_attenuation gate.
        let (mut world, principal, read) = semi_reinteractive_world();
        let receipts_before = world.receipts().len();

        // Upgrade via the powerbox: confer Signature (= the user's held ceiling). The
        // host gains an attenuated affordance cap reaching the source — a real grant turn.
        let upgraded = WebCellsBrowser::upgrade_transclusion_via_powerbox(
            &mut world,
            read,
            principal,
            "view",
            AuthRequired::Signature,
        )
        .expect("the user holds Signature over the source → the powerbox grants");
        assert!(upgraded.interactive, "the quote is now interactive");
        assert_eq!(upgraded.granted_affordance.as_deref(), Some("view"));
        assert_eq!(upgraded.conferred_rights, Some(AuthRequired::Signature));
        assert!(upgraded.affordance_note().starts_with("INTERACTIVE"));

        // The powerbox upgrade itself was a REAL grant turn (a receipt landed).
        assert!(
            world.receipts().len() > receipts_before,
            "the powerbox upgrade is a real verified grant turn"
        );

        // FIRE the granted affordance: `view` requires Signature, conferred is Signature
        // → it fires through the real embedded executor (a verified turn, not a model).
        let fired = WebCellsBrowser::fire_transcluded_affordance(&mut world, &upgraded, "view")
            .expect("`view` (Signature) ⊆ the conferred Signature → it fires");
        assert!(
            fired.is_committed(),
            "the granted affordance fired a real verified turn on the source: {fired:?}"
        );

        // NO MORE: `admin` requires the root (None) tier — WIDER than the conferred
        // Signature — so it is REFUSED IN-BAND by the real is_attenuation (the host holds
        // only the attenuated affordance, never the source's full authority).
        let refused = WebCellsBrowser::fire_transcluded_affordance(&mut world, &upgraded, "admin")
            .expect_err("`admin` needs wider authority than was conferred → refused");
        assert!(
            refused.contains("Unauthorized"),
            "firing a wider affordance than granted is refused in-band (anti-ghost), got: {refused}"
        );
    }

    #[test]
    fn the_powerbox_refuses_to_upgrade_a_quote_the_user_lacks_authority_over() {
        // The upgrade is powerbox-mediated: if the user does NOT hold authority over the
        // source, the powerbox refuses (mint_needs_held_factory) — the read stays free,
        // the quote stays read-only, no affordance cap is conferred.
        let mut world = World::new();
        let host = world.genesis_cell(0x60, 0);
        let source = world.genesis_cell(0x70, 0);
        // A principal that holds NOTHING reaching the source.
        let empty_principal = world.genesis_cell(0x6A, 0);
        let read = Transclusion {
            host,
            source,
            transcluded_field: "1234".to_string(),
            provenance_receipt: "5678".to_string(),
            source_finalized: true,
        };
        let receipts_before = world.receipts().len();

        let (still_read_only, reason) = WebCellsBrowser::upgrade_transclusion_via_powerbox(
            &mut world,
            read,
            empty_principal,
            "view",
            AuthRequired::Signature,
        )
        .expect_err("the user holds no source authority → the powerbox refuses the upgrade");
        assert!(still_read_only.is_read_only(), "the quote stays read-only after a refused upgrade");
        assert!(still_read_only.conferred_rights.is_none(), "no affordance cap was conferred");
        assert!(
            reason.contains("mint_needs_held_factory") || reason.contains("does not hold"),
            "the refusal cites the held-authority requirement, got: {reason}"
        );
        // No grant turn ran (a refused upgrade confers nothing).
        assert_eq!(world.receipts().len(), receipts_before, "a refused upgrade runs no grant turn");

        // And firing on the still-read-only quote is refused (no interact unlocked).
        assert!(
            WebCellsBrowser::fire_transcluded_affordance(&mut world, &still_read_only, "view").is_err(),
            "a read-only quote (refused upgrade) fires nothing"
        );
    }

    // ── THE WELD: the rich EDL span model (deos-web-cells' DreggverseDocument)
    //    rendered in the cockpit's web-of-cells browser. A multi-span document with
    //    OWN bytes + a verified peer quote + a per-viewer DARKENED span. ──

    #[test]
    fn the_browser_renders_a_multi_span_dreggverse_document() {
        // The cockpit browses the live image; the browser now composes a multi-span
        // dreggverse document (Nelson's EDL made honest) over the SAME web it built.
        let (world, anchors) = demo_world();
        let viewer = anchors[2]; // the user anchor — the cockpit's principal
        let browser = WebCellsBrowser::build(&world, viewer, editor_rights(), None);

        let doc = browser
            .document
            .expect("the live image has cells → a dreggverse document composes");

        // The EDL has FIVE spans (OWN intro, public quote, OWN connective, restricted
        // quote, OWN outro) — the rich span model the whole-field transclusion cannot
        // express.
        assert_eq!(doc.span_count, 5, "the EDL composes five spans");
        assert_eq!(doc.spans.len(), 5);

        // SPAN 0 + 2 + 4: OWN content, rendered verbatim (no foreign provenance).
        assert_eq!(doc.spans[0].kind, DocumentSpanKind::Own);
        assert_eq!(doc.spans[0].text, "This document quotes ");
        assert!(doc.spans[0].source.is_none(), "OWN content has no foreign source");
        assert_eq!(doc.spans[2].kind, DocumentSpanKind::Own);
        assert_eq!(doc.spans[2].text, " and a darkened ");
        assert_eq!(doc.spans[4].kind, DocumentSpanKind::Own);
        assert_eq!(doc.spans[4].text, ".");

        // SPAN 1: a VERIFIED PEER QUOTE — the public source's cited BYTE RANGE (4..20 =
        // "PUBLIC paragraph"), with real receipt-pinned provenance. This is the
        // genuine verified cross-cell finalized read (a forged source could not open).
        let quote = &doc.spans[1];
        assert_eq!(quote.kind, DocumentSpanKind::Quote, "span 1 is a verified quote");
        assert_eq!(quote.text, "PUBLIC paragraph", "the cited byte range of the public source");
        assert_eq!(quote.range.as_deref(), Some("4..20"), "the quote shows its cited byte range");
        assert!(
            quote.source.as_deref().map(|s| s.starts_with("dregg://")).unwrap_or(false),
            "the quote cites a dregg:// source"
        );
        assert!(
            quote.content_commitment.as_deref().map(|c| c.len() >= 4).unwrap_or(false),
            "the quote carries a real content commitment (datable provenance)"
        );
        assert!(
            quote.provenance_receipt.as_deref().map(|r| r.len() >= 4).unwrap_or(false),
            "the quote carries a real cited receipt"
        );

        // SPAN 3: a per-viewer DARKENED span — the restricted source's origin is not in
        // the viewer's fetch-allowlist, so the REAL membrane meet withholds it.
        let dark = &doc.spans[3];
        assert_eq!(dark.kind, DocumentSpanKind::Darkened, "span 3 darkens for this viewer");

        // BOTH POLARITIES of `full` exercised here (non-vacuous): the document is NOT
        // full (a span darkened) AND it has a genuine quote that DID render (quote_count
        // ≥ 1) — so darkening is selective, not a blanket failure.
        assert!(!doc.full, "a darkened span ⇒ the document is not fully readable for this viewer");
        assert_eq!(doc.darkened_count, 1, "exactly the restricted span is darkened");
        assert_eq!(doc.quote_count, 1, "the public span DID resolve as a real quote");

        // THE COMPOSED TEXT the viewer sees: OWN content + the public quote, but
        // NOTHING for the darkened span. The honest per-viewer render.
        assert_eq!(
            doc.composed_text,
            "This document quotes PUBLIC paragraph and a darkened .",
            "the composed text carries OWN + the public quote, nothing for the darkened span"
        );
    }

    #[test]
    fn a_darkened_span_withholds_the_bytes_but_keeps_the_citation_anti_forgery() {
        // THE ANTI-FORGERY TOOTH (negative polarity): the viewer NEVER sees the
        // restricted source's value (not the bytes, not a substituted forgery) — but the
        // darkened span STILL carries its provenance (the citation survives).
        let (world, anchors) = demo_world();
        let viewer = anchors[2];
        let browser = WebCellsBrowser::build(&world, viewer, editor_rights(), None);
        let doc = browser.document.expect("a dreggverse document composes");

        let dark = &doc.spans[3];
        assert_eq!(dark.kind, DocumentSpanKind::Darkened);
        // A darkened span yields NO source bytes (the viewer gets none it lacks
        // authority to read).
        assert_eq!(dark.text, "", "a darkened span yields NO source bytes");
        // The restricted source's value NEVER appears anywhere in the composed text —
        // not withheld-then-leaked, not forged.
        assert!(
            !doc.composed_text.contains("RESTRICTED"),
            "the viewer never sees the restricted value it lacks authority to read"
        );
        // …BUT the citation survives: the darkened span keeps its provenance (source +
        // commitment + receipt) — the docuverse skeleton stays visible, only the bytes
        // withheld. This is the both-polarity tooth: present (citation) vs. absent (bytes).
        assert!(dark.source.is_some(), "the darkened span still cites its source");
        assert!(
            dark.content_commitment.as_deref().map(|c| c.len() >= 4).unwrap_or(false),
            "the darkened span keeps its content commitment (provenance survives)"
        );
        assert!(
            dark.provenance_receipt.as_deref().map(|r| r.len() >= 4).unwrap_or(false),
            "the darkened span keeps its cited receipt"
        );
        assert_eq!(dark.range.as_deref(), Some("4..24"), "the darkened span keeps its cited byte range");
    }

    #[test]
    fn a_full_authority_viewer_reaches_every_span_no_darkening() {
        // THE OTHER POLARITY of the darkening: prove the darkening is SELECTIVE (driven
        // by the viewer's fetch-allowlist), not unconditional. We resolve the SAME
        // document for a FULL-authority viewer (wildcard fetch) directly against
        // `deos-web-cells` — every span reaches; nothing darkens. (The cockpit's browser
        // scopes its viewer to the public origin on purpose, to SHOW a darkened span;
        // here we confirm the mechanism, not a constant.)
        let mut web = WebOfCells::new(3);
        let publisher = web.publish(0xE0, b"anchor", "dregg://doc/anchor").cell;
        let public_src = web.publish(0xD0, b"the PUBLIC paragraph anyone may read", "dregg://doc/public");
        let secret_src = web.publish(0xD1, b"the RESTRICTED paragraph", "dregg://doc/restricted");

        let public_origin = doc_span_origin(public_src.cell);
        let secret_origin = doc_span_origin(secret_src.cell);

        let lineage = SurfaceCapability::scoped(
            publisher,
            AuthRequired::Either,
            [public_origin.clone(), secret_origin.clone()],
            [],
        );
        let doc = DreggverseDocument::from_spans(vec![
            Span::own(b"This document quotes ".to_vec()),
            Span::transclude_range(public_src.clone(), SpanRange::new(4, 20)),
            Span::own(b" and ".to_vec()),
            Span::transclude_range(secret_src.clone(), SpanRange::new(4, 14)),
        ]);

        // A FULL-authority viewer: wildcard fetch (root), Either rights — reaches BOTH.
        let full_viewer = Membrane::new(SurfaceCapability::root(publisher, AuthRequired::Either));
        let rendered = doc
            .resolve_for(&web, &full_viewer, &lineage)
            .expect("the full-authority viewer resolves");
        assert!(rendered.is_full(), "the full-authority viewer darkens NOTHING");
        assert_eq!(rendered.darkened_count(), 0);
        // Both quotes are present (the selective-vs-blanket distinction: same document,
        // a wider viewer reaches the span the cockpit's scoped viewer could not).
        assert_eq!(rendered.composed_text().unwrap(), "This document quotes PUBLIC paragraph and RESTRICTED");
    }
}
