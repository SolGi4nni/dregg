//! **Capture → commit → publish a LIVE rendered surface's DOM state as a
//! web-of-cells cell** — the leptosic move made first-class.
//!
//! `docs/deos/WEB-CELLS.md`: "what if we started publishing/committing … bundles of
//! LIVE DOM state, and sharing that as part of the web of cells?" The
//! [`crate::bundle`] layer already gives a [`WebBundle`] (with the
//! [`BundleKind::LiveDomSnapshot`] kind) the whole publish/fetch/rehydrate/transclude
//! story. This module is the missing FRONT END: it takes a *rendered surface's live
//! DOM state* — a [`RenderedSurface`] (the rendered fragment TREE + its named asset
//! references, the `DomSnapshot`-shaped structure a running surface hands over) — and
//!
//! 1. **CAPTURES → COMMITS → PUBLISHES** it: [`RenderedSurface::into_bundle`]
//!    serializes the fragment tree into the bundle's `index.html` (the rendered view)
//!    + a structural `dom-state` asset (the serialized tree — the live quote a peer
//!      transcludes) alongside the surface's referenced assets, and
//!      [`publish_live_surface`] commits that canonical encoding into a REAL `dregg://`
//!      surface cell through the genuine [`publish_bundle`] chain
//!      (content → commitment → receipt → receipt-stream-root → quorum). **The published
//!      cell IS the DOM state at a committed height** — its committed content hash is the
//!      bundle's content hash, checkable by a third party. The publish returns the
//!      bearer [`DreggUri`], the [`Sturdyref`] behind the membrane, AND the tiny
//!      [`DomSnapshot`] frustum (so the surface is immediately rehydratable per-viewer).
//!
//! 2. **TRANSCLUDES A DOM FRAGMENT**: [`PublishedSurface::quote_fragment`] makes a
//!    span/region of the published surface's rendered DOM a transcludable
//!    [`Span`] of a [`DreggverseDocument`] — the same bytes, the source's
//!    receipt-pinned [`Provenance`](starbridge_web_surface::transclusion::Provenance),
//!    per-viewer through the membrane (the darkened
//!    viewer sees the citation, not the bytes). It composes the existing
//!    [`Span::transclude_asset_range`] (a byte range within the published surface's
//!    `index.html` asset — the DOM-level span) and the
//!    [`crate::cascade::transclude_bundle_fragment`] live-quote — it invents no fetch.
//!
//! 3. **RE-PUBLISH ON CHANGE TRACKS LIVE**: [`PublishedSurface::amend`] amends the
//!    source surface (the REAL [`WebOfCells::amend`]) to a NEW captured DOM state at a
//!    NEW committed height. The SNAPSHOT/LIVE dial is the genuine
//!    [`VersionedTransclusion`] ([`PublishedSurface::dom_state_snapshot`] /
//!    [`PublishedSurface::dom_state_live`]): a snapshot pins the OLD DOM-state height
//!    (I-confluent — stable as the surface advances), a live transclusion re-resolves
//!    to the NEW one. Both carry provenance; a forge is refused in either mode.
//!
//! ## What is real vs. the seam
//!
//! - **Real (the capture-serialization + the whole publish/transclude/dial chain):**
//!   the fragment-tree → bytes serialization is deterministic and content-addressed
//!   (so identical DOM state addresses identically); the publish is the REAL
//!   [`publish_bundle`] into a genuine `dregg_cell::Cell` (the cell's committed content
//!   hash IS the captured DOM state's hash); the DOM-fragment transclusion is the REAL
//!   [`TranscludedField`](starbridge_web_surface::transclusion::TranscludedField)-backed
//!   quote with receipt-pinned provenance; the
//!   snapshot/live dial is the REAL [`VersionedTransclusion`]; the per-viewer darkening
//!   is the REAL [`Membrane`] projection. We reinvent no fetch, no attestation, no
//!   snapshot, no membrane, no version machinery.
//! - **The seam (named, not papered): the live-Leptos signal CAPTURE.** This module's
//!   [`RenderedSurface`] is the *structure* a running surface's DOM state takes (a
//!   fragment tree + asset refs) — it models the serialized form FAITHFULLY, but
//!   BINDING a *running* Leptos signal-graph so that a real reactive surface emits a
//!   [`RenderedSurface`] on every commit (the live SSR-serialize → `dom-state` asset →
//!   reactive re-expand) is the in-flight `deos-leptos` crate's job — the named
//!   demonstrable follow-on. What is real here is the capture→commit→publish of a
//!   *given* DOM-state value, the transcludable DOM fragment, and the amend-tracks-live
//!   dial; the `deos-leptos` binding populates the [`RenderedSurface`] from live
//!   signals. The render (bytes → pixels) is the `servo-render` Stage-A seam
//!   ([`crate::cascade`]) exactly as for any bundle.

use starbridge_web_surface::rehydrate::InteractionLog;
use starbridge_web_surface::transclusion::TransclusionError;
use starbridge_web_surface::transclusion_version::VersionedTransclusion;
use starbridge_web_surface::{DreggUri, FetchError, Sturdyref, SurfaceCapability, WebOfCells};

use crate::bundle::{publish_bundle, BundleAsset, BundleError, BundleKind, WebBundle};
use crate::cascade::{transclude_bundle_fragment, BundleFragmentQuote, CascadeError};
use crate::document::{Span, SpanRange};
use crate::rehydrate::{DomSnapshot, SnapshotError};

/// The asset name the captured **rendered view** is serialized into (the bundle
/// entrypoint — the HTML the renderer loads first). Quoting a DOM fragment selects a
/// byte range WITHIN this asset.
pub const RENDERED_VIEW_ASSET: &str = "index.html";

/// The asset name the captured **DOM-state tree** is serialized into (the structural
/// serialization — the live quote of the surface's signal/DOM state a peer transcludes
/// whole). `application/dom-snapshot`, distinct from the rendered HTML.
pub const DOM_STATE_ASSET: &str = "dom-state";

/// One node of a captured rendered DOM fragment **tree** — either an ELEMENT (a tag
/// with attributes + children) or a TEXT node.
///
/// `docs/deos/WEB-CELLS.md`: this is the "rendered fragment tree" half of a live
/// surface's DOM state — the structure a running surface (e.g. a Leptos signal-graph
/// over a DOM) hands over to be captured. It is deliberately a faithful, minimal DOM
/// shape (element/attrs/text/children), serialized DETERMINISTICALLY so identical DOM
/// state has an identical content-address — never a lossy screenshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DomNode {
    /// An element node: a tag `name` (e.g. `div`, `h1`), ordered `attrs`
    /// (`(name, value)`), and ordered `children`.
    Element {
        /// The tag name (lowercased by convention; serialized verbatim).
        name: String,
        /// The element's attributes, in source order. `(attr-name, attr-value)`.
        attrs: Vec<(String, String)>,
        /// The element's children, in document order.
        children: Vec<DomNode>,
    },
    /// A text node carrying its (already-unescaped) text content.
    Text(String),
}

impl DomNode {
    /// An element node `<name …>children</name>`.
    pub fn element(
        name: impl Into<String>,
        attrs: impl IntoIterator<Item = (String, String)>,
        children: impl IntoIterator<Item = DomNode>,
    ) -> Self {
        DomNode::Element {
            name: name.into(),
            attrs: attrs.into_iter().collect(),
            children: children.into_iter().collect(),
        }
    }

    /// A text node.
    pub fn text(content: impl Into<String>) -> Self {
        DomNode::Text(content.into())
    }

    /// A convenience: an element with no attributes wrapping a single text child —
    /// `<name>text</name>`.
    pub fn labelled(name: impl Into<String>, text: impl Into<String>) -> Self {
        DomNode::element(name, [], [DomNode::text(text)])
    }

    /// **Render this node to HTML** — the deterministic serialization that becomes the
    /// bundle's `index.html`. Elements render `<name attr="v">children</name>`
    /// (attributes in source order, HTML-escaped values); text renders escaped. This
    /// is the rendered VIEW (what a renderer rasterizes), and the bytes a DOM-fragment
    /// quote selects a range of.
    pub fn render_html(&self) -> String {
        let mut out = String::new();
        self.render_html_into(&mut out);
        out
    }

    fn render_html_into(&self, out: &mut String) {
        match self {
            DomNode::Element {
                name,
                attrs,
                children,
            } => {
                out.push('<');
                out.push_str(name);
                for (k, v) in attrs {
                    out.push(' ');
                    out.push_str(k);
                    out.push_str("=\"");
                    push_escaped_attr(out, v);
                    out.push('"');
                }
                out.push('>');
                for c in children {
                    c.render_html_into(out);
                }
                out.push_str("</");
                out.push_str(name);
                out.push('>');
            }
            DomNode::Text(t) => push_escaped_text(out, t),
        }
    }

    /// **Serialize this node's structure** into the deterministic `dom-state`
    /// encoding (a parenthesized, length-explicit S-expression-ish form). This is the
    /// STRUCTURAL serialization — the live signal/DOM *state*, distinct from the
    /// rendered HTML — that a peer transcludes whole as the "live quote" of the
    /// surface's state. Deterministic: identical trees serialize identically (so the
    /// bundle is content-addressed by its DOM state).
    pub fn serialize_state(&self) -> String {
        let mut out = String::new();
        self.serialize_state_into(&mut out);
        out
    }

    fn serialize_state_into(&self, out: &mut String) {
        match self {
            DomNode::Element {
                name,
                attrs,
                children,
            } => {
                out.push_str("(el ");
                push_len_token(out, name);
                out.push_str(" (attrs");
                for (k, v) in attrs {
                    out.push(' ');
                    push_len_token(out, k);
                    out.push('=');
                    push_len_token(out, v);
                }
                out.push_str(") (kids");
                for c in children {
                    out.push(' ');
                    c.serialize_state_into(out);
                }
                out.push_str("))");
            }
            DomNode::Text(t) => {
                out.push_str("(tx ");
                push_len_token(out, t);
                out.push(')');
            }
        }
    }

    /// The number of element + text nodes in this subtree (this node included) — the
    /// captured fragment's extent, a readout the capture is the real tree, not a flat
    /// blob.
    pub fn node_count(&self) -> usize {
        match self {
            DomNode::Element { children, .. } => {
                1 + children.iter().map(DomNode::node_count).sum::<usize>()
            }
            DomNode::Text(_) => 1,
        }
    }
}

/// A **captured live rendered surface** — the `DomSnapshot`-shaped structure a running
/// surface's DOM state takes: the rendered fragment TREE (a root [`DomNode`]) + its
/// named ASSET references (the scripts/stylesheets/state-blobs the surface depends on).
///
/// `docs/deos/WEB-CELLS.md`: this is the thing you "publish/commit … bundles of LIVE
/// DOM state." It is captured (serialized) into a [`WebBundle`] by
/// [`RenderedSurface::into_bundle`] and published as a `dregg://` cell by
/// [`publish_live_surface`]. The leptosic angle: a Leptos app's live signal-graph over
/// a DOM IS exactly a [`RenderedSurface`] — its rendered view is the `fragment` tree,
/// its referenced assets the `assets`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RenderedSurface {
    /// The rendered DOM fragment tree (the surface's live rendered view, as a tree —
    /// captured deterministically, never a lossy raster).
    pub fragment: DomNode,
    /// The surface's named asset references (scripts, stylesheets, additional state
    /// blobs) — each becomes a bundle asset alongside the rendered view + the
    /// serialized DOM-state. The per-viewer membrane gates on these names exactly as
    /// for any bundle asset.
    pub assets: Vec<BundleAsset>,
}

impl RenderedSurface {
    /// Capture a rendered surface from its fragment `tree` and named asset
    /// references. The rendered view + the serialized DOM-state are derived from the
    /// tree by [`RenderedSurface::into_bundle`]; `assets` are the surface's *extra*
    /// referenced assets (it must NOT itself name [`RENDERED_VIEW_ASSET`] or
    /// [`DOM_STATE_ASSET`] — those are the captured-from-tree assets).
    pub fn new(fragment: DomNode, assets: impl IntoIterator<Item = BundleAsset>) -> Self {
        RenderedSurface {
            fragment,
            assets: assets.into_iter().collect(),
        }
    }

    /// A convenience: capture a surface that is JUST a rendered fragment tree (no extra
    /// referenced assets) — the common "publish my app's current view + state" case.
    pub fn of(fragment: DomNode) -> Self {
        RenderedSurface::new(fragment, [])
    }

    /// The rendered view bytes — the captured fragment tree serialized to HTML (what a
    /// renderer rasterizes; the asset a DOM-fragment quote selects a byte range of).
    pub fn rendered_view(&self) -> Vec<u8> {
        self.fragment.render_html().into_bytes()
    }

    /// The serialized DOM-state bytes — the captured fragment tree's STRUCTURAL
    /// serialization (the live quote of the surface's signal/DOM state a peer
    /// transcludes whole).
    pub fn dom_state(&self) -> Vec<u8> {
        self.fragment.serialize_state().into_bytes()
    }

    /// **Capture → serialize** the rendered surface into a [`WebBundle`] of kind
    /// [`BundleKind::LiveDomSnapshot`].
    ///
    /// The bundle's assets are, in canonical (name-sorted) order:
    /// - [`RENDERED_VIEW_ASSET`] (`index.html`, `text/html`) — the rendered view (the
    ///   entrypoint);
    /// - [`DOM_STATE_ASSET`] (`dom-state`, `application/dom-snapshot`) — the serialized
    ///   DOM-state tree;
    /// - every referenced asset in [`RenderedSurface::assets`].
    ///
    /// Deterministic + content-addressed: two surfaces with identical DOM state +
    /// identical assets serialize to the SAME bundle (the SAME `dregg://` cell). The
    /// kind is folded into the address, so a captured live surface and a hand-authored
    /// static bundle with byte-identical assets are still DISTINCT cells.
    ///
    /// Refuses ([`BundleError::DuplicateAssetName`]) if a referenced asset collides
    /// with the captured-from-tree [`RENDERED_VIEW_ASSET`] / [`DOM_STATE_ASSET`] names
    /// — the captured assets own those names.
    pub fn into_bundle(&self) -> Result<WebBundle, BundleError> {
        let mut assets = Vec::with_capacity(self.assets.len() + 2);
        assets.push(BundleAsset::new(
            RENDERED_VIEW_ASSET,
            "text/html",
            self.rendered_view(),
        ));
        assets.push(BundleAsset::new(
            DOM_STATE_ASSET,
            "application/dom-snapshot",
            self.dom_state(),
        ));
        for a in &self.assets {
            assets.push(a.clone());
        }
        // The validating constructor enforces unique asset names (a referenced asset
        // colliding with the captured names is a DuplicateAssetName) + the entrypoint.
        WebBundle::new(BundleKind::LiveDomSnapshot, RENDERED_VIEW_ASSET, assets)
    }
}

/// A **published live surface** — the handle the capture→commit→publish returns: the
/// `dregg://` ref the DOM state was committed to, the publishing context, and the
/// captured surface it was published from.
///
/// `docs/deos/WEB-CELLS.md`: **the published cell IS the DOM state at a committed
/// height.** This handle is what you transclude a DOM fragment OF
/// ([`PublishedSurface::quote_fragment`]), dial a snapshot/live read of
/// ([`PublishedSurface::dom_state_snapshot`] / [`PublishedSurface::dom_state_live`]),
/// and amend to a new committed DOM-state height of ([`PublishedSurface::amend`]).
#[derive(Clone, Debug)]
pub struct PublishedSurface {
    /// The `dregg://` ref the captured DOM state was committed to — the bearer cap a
    /// peer fetches / transcludes / rehydrates. UNCHANGED across [`Self::amend`]
    /// (Nelson's unbreakable link: the citation still resolves, to the surface's NEW
    /// committed value).
    pub uri: DreggUri,
    /// The publish seed (the deterministic origin-cell derivation) — kept so
    /// [`Self::amend`] re-commits into the SAME cell.
    pub seed: u8,
    /// The authority lineage the surface is served under (the publisher's cap) — what
    /// the per-viewer membrane meets a viewer's held authority against.
    pub lineage: SurfaceCapability,
    /// The most-recently captured surface (the DOM state currently committed at
    /// [`Self::uri`]). [`Self::amend`] replaces this with the new capture.
    pub surface: RenderedSurface,
}

impl PublishedSurface {
    /// The bundle the currently-committed DOM state serializes to (the value at
    /// [`Self::uri`]). Its [`WebBundle::content_hash`] is the cell's committed content
    /// hash.
    pub fn bundle(&self) -> WebBundle {
        // The surface was published, so its bundle is well-formed (no Empty/duplicate).
        self.surface
            .into_bundle()
            .expect("a published surface's capture is a valid bundle")
    }

    /// The cell the DOM state is committed to (the `dregg://` ref's cell).
    pub fn cell(&self) -> dregg_types::CellId {
        self.uri.cell
    }

    /// **Take the tiny [`DomSnapshot`] frustum** of the currently-committed DOM state
    /// — a [`Sturdyref`] + the culling boundary (NOT the bytes), so the surface is
    /// rehydratable PER-VIEWER through the REAL membrane ([`crate::rehydrate_bundle`]).
    ///
    /// Builds the sturdyref from this surface's `lineage` + the given `witness_log` /
    /// `sources_reachable` (the source context's confinement, from which the
    /// liveness-type is DERIVED). The frustum pins the current capture's manifest
    /// digest, so a rehydration cross-checks it is THIS DOM state.
    pub fn snapshot(
        &self,
        witness_log: InteractionLog,
        sources_reachable: bool,
    ) -> Result<DomSnapshot, SnapshotError> {
        let sturdyref = Sturdyref::new(
            self.uri.clone(),
            self.lineage.clone(),
            witness_log,
            sources_reachable,
        );
        self.snapshot_from(sturdyref)
    }

    /// Take the tiny [`DomSnapshot`] frustum from an EXISTING [`Sturdyref`] (the one
    /// [`publish_live_surface`] returned) — pins the current capture's manifest digest.
    /// Refuses ([`SnapshotError::SturdyrefBoundaryMismatch`]) if the sturdyref's cell ≠
    /// this surface's cell.
    pub fn snapshot_from(&self, sturdyref: Sturdyref) -> Result<DomSnapshot, SnapshotError> {
        DomSnapshot::take(&self.bundle(), sturdyref)
    }

    /// **Quote a DOM FRAGMENT of the published surface as a transcludable [`Span`]** —
    /// a span/region of the rendered DOM, includable into a [`DreggverseDocument`].
    ///
    /// The `range` selects a byte range WITHIN the published surface's rendered view
    /// ([`RENDERED_VIEW_ASSET`]) — a DOM-level span of the live surface. It composes
    /// the existing [`Span::transclude_asset_range`]: at document resolve the span is
    /// the REAL verified cross-cell finalized read of the surface's `index.html`
    /// asset, carrying the source's receipt-pinned provenance, per-viewer through the
    /// membrane (a darkened viewer sees the citation, not the bytes). Use
    /// [`SpanRange::whole`] to quote the entire rendered view.
    pub fn quote_fragment(&self, range: SpanRange) -> Span {
        Span::transclude_asset_range(self.uri.clone(), RENDERED_VIEW_ASSET, range)
    }

    /// Quote the WHOLE rendered DOM of the published surface as a transcludable
    /// [`Span`] (the common "transclude this surface's rendered view" case).
    pub fn quote_rendered(&self) -> Span {
        self.quote_fragment(SpanRange::whole())
    }

    /// **The live quote of the surface's DOM-state** — a [`BundleFragmentQuote`] of the
    /// [`DOM_STATE_ASSET`] fragment, carrying the source's receipt-pinned provenance.
    /// This is the structural live state (the serialized signal/DOM tree) a peer
    /// surface embeds — the genuine [`transclude_bundle_fragment`], never a copy. A
    /// forged / absent / non-bundle source is refused (no opened provenance ⇒ no
    /// fragment).
    pub fn quote_dom_state(&self, web: &WebOfCells) -> Result<BundleFragmentQuote, CascadeError> {
        transclude_bundle_fragment(web, &self.uri, DOM_STATE_ASSET)
    }

    /// **The SNAPSHOT half of the snapshot/live dial** — pin the surface's CURRENT
    /// committed DOM state at its current finalized height (the REAL
    /// [`VersionedTransclusion::snapshot`]). I-confluent: it stays at the pinned DOM
    /// state no matter how far the surface advances (the citation that does not rot).
    /// Refuses if the surface does not resolve to a verified finalized read (a forge
    /// cannot be snapshotted).
    ///
    /// (The pinned quote is over the surface cell's whole committed bundle bytes; the
    /// dial demonstrates "a snapshot pins the OLD DOM-state height" vs the live read's
    /// re-resolution after [`Self::amend`].)
    pub fn dom_state_snapshot(
        &self,
        web: &WebOfCells,
    ) -> Result<VersionedTransclusion, TransclusionError> {
        VersionedTransclusion::snapshot(web, &self.uri)
    }

    /// **The LIVE half of the snapshot/live dial** — a standing intent to re-resolve
    /// the surface's CURRENT committed DOM state on every read (the REAL
    /// [`VersionedTransclusion::live`]). As the surface [`Self::amend`]s, the live
    /// quote follows to the new DOM state at the new height. Caches nothing; the first
    /// [`VersionedTransclusion::read`] is where resolution + verification happen.
    pub fn dom_state_live(&self) -> VersionedTransclusion {
        VersionedTransclusion::live(&self.uri)
    }

    /// **Re-publish on change — amend the surface to a NEW captured DOM state.** The
    /// REAL [`WebOfCells::amend`]: re-commit the new capture's canonical encoding into
    /// the SAME origin cell (content commitment updated, nonce bumped — a distinct
    /// serve-receipt — the federation height advanced). The `dregg://` ref is
    /// UNCHANGED: a snapshot taken before the amend stays pinned to the OLD DOM state,
    /// a live transclusion re-resolves to the NEW one (the snapshot/live dial tracks
    /// live). Returns the advanced federation height (the NEW committed DOM-state
    /// height). Refuses ([`FetchError::OriginNotFound`]) if the surface was never
    /// published, or ([`BundleError`]) if the new capture is not a valid bundle.
    pub fn amend(
        &mut self,
        web: &mut WebOfCells,
        new_surface: RenderedSurface,
    ) -> Result<u64, AmendError> {
        let new_bundle = new_surface.into_bundle().map_err(AmendError::Bundle)?;
        let encoded = new_bundle.encode();
        let height = web.amend(&self.uri, &encoded).map_err(AmendError::Fetch)?;
        self.surface = new_surface;
        Ok(height)
    }
}

/// **Capture → commit → PUBLISH a live rendered surface's DOM state as a
/// content-addressed `dregg://` cell.**
///
/// `docs/deos/WEB-CELLS.md`: the headline capability. Serializes the [`RenderedSurface`]
/// into a [`BundleKind::LiveDomSnapshot`] [`WebBundle`] ([`RenderedSurface::into_bundle`])
/// and commits its canonical encoding into a REAL surface cell through the genuine
/// [`publish_bundle`] chain (content → commitment → receipt → receipt-stream-root →
/// quorum). **The published cell IS the DOM state at a committed height** — its
/// committed content hash is the captured DOM state's content hash, checkable by a
/// third party.
///
/// Returns:
/// - the [`PublishedSurface`] handle (the `dregg://` ref + the publishing context +
///   the captured surface — what you transclude / dial / amend);
/// - the [`Sturdyref`] behind the membrane (the cap-handle [`crate::rehydrate_bundle`]
///   re-expands per-viewer), carrying the publisher's `lineage` + the source context's
///   `witness_log` (here the surface's; a live binding carries the running context's) +
///   `sources_reachable`.
///
/// We add NO bespoke publish: the content commitment, the attested root, and the
/// trusted chrome are all the genuine web-of-cells machinery.
pub fn publish_live_surface(
    web: &mut WebOfCells,
    seed: u8,
    surface: RenderedSurface,
    lineage: SurfaceCapability,
    witness_log: InteractionLog,
    sources_reachable: bool,
) -> Result<(PublishedSurface, Sturdyref), BundleError> {
    let bundle = surface.into_bundle()?;
    let (uri, sturdyref) = publish_bundle(
        web,
        seed,
        &bundle,
        lineage.clone(),
        witness_log,
        sources_reachable,
    );
    let published = PublishedSurface {
        uri,
        seed,
        lineage,
        surface,
    };
    Ok((published, sturdyref))
}

/// What can go wrong re-publishing (amending) a surface to a new DOM state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AmendError {
    /// The new capture did not serialize to a valid bundle (e.g. a referenced asset
    /// collided with the captured-from-tree names) — the REAL [`BundleError`].
    Bundle(BundleError),
    /// The `dregg://` ref was never published (so there is nothing to amend) — the
    /// REAL [`FetchError`] (`OriginNotFound`).
    Fetch(FetchError),
}

// ── HTML / state serialization helpers (deterministic, so the capture is
//    content-addressed by its DOM state). ──

/// Escape a text node's content for HTML body context (`&`, `<`, `>`).
fn push_escaped_text(out: &mut String, t: &str) {
    for ch in t.chars() {
        match ch {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            c => out.push(c),
        }
    }
}

/// Escape an attribute value for HTML double-quoted attribute context (adds `"`).
fn push_escaped_attr(out: &mut String, v: &str) {
    for ch in v.chars() {
        match ch {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            c => out.push(c),
        }
    }
}

/// A length-explicit token `«len:bytes»` for the structural `dom-state` serialization,
/// so the encoding is UNAMBIGUOUS (no token can be confused with a delimiter — a
/// tag/attr/text value carrying spaces or parens cannot collide with the framing).
fn push_len_token(out: &mut String, s: &str) {
    out.push('«');
    out.push_str(&s.len().to_string());
    out.push(':');
    out.push_str(s);
    out.push('»');
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bundle::fetch_bundle;
    use crate::document::{DreggverseDocument, RenderedSpan};
    use crate::rehydrate::rehydrate_bundle;
    use crate::tests_support::cid;
    use starbridge_web_surface::{AuthRequired, Membrane};

    use std::collections::BTreeSet;

    fn origins(list: &[String]) -> BTreeSet<String> {
        list.iter().cloned().collect()
    }

    /// A leptosic "counter app" surface at count `n`: a rendered `<div id=app>` tree
    /// plus a referenced `app.js`. The rendered view embeds the count (so amending the
    /// count re-captures a different DOM state).
    fn counter_surface(n: u32) -> RenderedSurface {
        let fragment = DomNode::element(
            "div",
            [("id".to_string(), "app".to_string())],
            [
                DomNode::labelled("h1", format!("counter: {n}")),
                DomNode::element(
                    "button",
                    [("class".to_string(), "inc".to_string())],
                    [DomNode::text("++")],
                ),
            ],
        );
        RenderedSurface::new(
            fragment,
            [BundleAsset::new(
                "app.js",
                "application/javascript",
                b"onClick(inc)".to_vec(),
            )],
        )
    }

    // ── CAPTURE: the rendered surface serializes deterministically + content-addressed. ──

    #[test]
    fn a_rendered_surface_captures_to_a_live_dom_bundle() {
        let surface = counter_surface(3);
        let bundle = surface.into_bundle().expect("captures to a bundle");

        // It is a LIVE-DOM snapshot bundle (the kind is folded into the address).
        assert_eq!(bundle.kind, BundleKind::LiveDomSnapshot);
        // Its assets: the rendered view, the serialized DOM-state, and the referenced
        // app.js — three assets.
        assert_eq!(bundle.assets.len(), 3);
        assert_eq!(bundle.entrypoint, RENDERED_VIEW_ASSET);

        // The rendered view is the fragment tree serialized to HTML (the count is in it).
        let view = bundle
            .asset(RENDERED_VIEW_ASSET)
            .expect("rendered view asset");
        assert_eq!(view.content_type, "text/html");
        let html = String::from_utf8(view.bytes.clone()).unwrap();
        assert_eq!(
            html,
            "<div id=\"app\"><h1>counter: 3</h1><button class=\"inc\">++</button></div>"
        );

        // The dom-state asset is the structural serialization (distinct from the HTML).
        let state = bundle.asset(DOM_STATE_ASSET).expect("dom-state asset");
        assert_eq!(state.content_type, "application/dom-snapshot");
        assert_ne!(
            state.bytes, view.bytes,
            "the state serialization ≠ the rendered HTML"
        );

        // The referenced asset rode along.
        assert_eq!(bundle.asset("app.js").unwrap().bytes, b"onClick(inc)");
    }

    #[test]
    fn capture_is_deterministic_and_content_addressed() {
        // Identical DOM state → the SAME bundle (the SAME dregg:// cell). A different
        // count → a different content-address.
        let a = counter_surface(3).into_bundle().unwrap();
        let b = counter_surface(3).into_bundle().unwrap();
        assert_eq!(a.content_hash(), b.content_hash());
        let c = counter_surface(4).into_bundle().unwrap();
        assert_ne!(a.content_hash(), c.content_hash());
    }

    #[test]
    fn html_escaping_keeps_the_capture_faithful() {
        // A text node with HTML metacharacters renders escaped (the capture is a
        // faithful DOM serialization, not an injection vector).
        let surface = RenderedSurface::of(DomNode::labelled("p", "a < b & c > d \"q\""));
        let bundle = surface.into_bundle().unwrap();
        let html =
            String::from_utf8(bundle.asset(RENDERED_VIEW_ASSET).unwrap().bytes.clone()).unwrap();
        assert_eq!(html, "<p>a &lt; b &amp; c &gt; d \"q\"</p>");
    }

    #[test]
    fn a_referenced_asset_colliding_with_a_captured_name_is_refused() {
        // A referenced asset cannot claim the captured-from-tree names.
        let surface = RenderedSurface::new(
            DomNode::labelled("h1", "x"),
            [BundleAsset::new(
                DOM_STATE_ASSET,
                "text/plain",
                b"collision".to_vec(),
            )],
        );
        assert_eq!(
            surface.into_bundle(),
            Err(BundleError::DuplicateAssetName {
                name: DOM_STATE_ASSET.to_string()
            })
        );
    }

    // ── CAPTURE → COMMIT → PUBLISH: the published cell IS the DOM state at a
    //    committed height (the REAL publish chain). ──

    #[test]
    fn publish_commits_the_dom_state_and_fetch_round_trips_through_the_attested_path() {
        let surface = counter_surface(3);
        let mut web = WebOfCells::new(3);
        let lineage = SurfaceCapability::root(cid(1), AuthRequired::Either);

        let (published, _sturdyref) = publish_live_surface(
            &mut web,
            1,
            surface.clone(),
            lineage,
            InteractionLog::new(),
            false,
        )
        .expect("publishes");

        // FETCH through the REAL attested path: the fetched bundle IS the captured DOM
        // state (content-addressed), and the committed content hash on the cell IS the
        // captured bundle's content hash.
        let (fetched, chrome) =
            fetch_bundle(&web, &published.uri).expect("fetch + verify + decode");
        assert_eq!(fetched, published.bundle());
        assert_eq!(
            fetched.content_hash(),
            surface.into_bundle().unwrap().content_hash()
        );
        assert!(chrome.finalized);
        // The trusted chrome shows the bundle's content-address (the DOM state's
        // identity), drawn from the ledger.
        assert_eq!(
            chrome.committed_url.as_deref(),
            Some(published.bundle().content_uri().as_str())
        );
    }

    #[test]
    fn a_published_surface_rehydrates_per_viewer_through_the_real_membrane() {
        // The published live surface is immediately rehydratable: a powerful viewer
        // re-expands the full bundle; a weaker viewer (scoped away from app.js) an
        // attenuated projection. (The genuine rehydrate_bundle per-asset membrane meet.)
        let surface = counter_surface(7);
        let mut web0 = WebOfCells::new(3);
        let seed = 5u8;

        // Learn the cell to scope the lineage to all asset origins (publish is
        // deterministic in the seed).
        let probe = SurfaceCapability::root(cid(seed), AuthRequired::Either);
        let (probe_pub, _) = publish_live_surface(
            &mut web0,
            seed,
            surface.clone(),
            probe,
            InteractionLog::new(),
            false,
        )
        .unwrap();
        let cell = probe_pub.cell();
        let all_origins: Vec<String> = probe_pub
            .bundle()
            .manifest()
            .asset_names()
            .iter()
            .map(|n| WebBundle::asset_origin(cell, n))
            .collect();
        let lineage =
            SurfaceCapability::scoped(cell, AuthRequired::Either, origins(&all_origins), []);

        let mut web = WebOfCells::new(3);
        let (published, sturdyref) = publish_live_surface(
            &mut web,
            seed,
            surface,
            lineage,
            InteractionLog::new(),
            false,
        )
        .unwrap();
        assert_eq!(published.cell(), cell);

        let snapshot = published.snapshot_from(sturdyref).expect("snapshot");

        // A powerful viewer re-expands the full captured surface.
        let powerful = Membrane::new(SurfaceCapability::root(cid(20), AuthRequired::Either));
        let full = rehydrate_bundle(&snapshot, &powerful, &web).expect("powerful rehydrates");
        assert!(full.is_full());
        assert_eq!(full.bundle.kind, BundleKind::LiveDomSnapshot);
        assert!(full.bundle.asset("app.js").is_some());

        // A weaker viewer scoped to only the rendered view + dom-state (NOT app.js)
        // gets an attenuated projection — app.js is culled.
        let weaker_allowed = vec![
            WebBundle::asset_origin(cell, RENDERED_VIEW_ASSET),
            WebBundle::asset_origin(cell, DOM_STATE_ASSET),
        ];
        let weaker = Membrane::new(SurfaceCapability::scoped(
            cid(30),
            AuthRequired::Either,
            origins(&weaker_allowed),
            [],
        ));
        let atten = rehydrate_bundle(&snapshot, &weaker, &web).expect("weaker rehydrates");
        assert!(!atten.is_full());
        assert_eq!(atten.culled_assets, vec!["app.js".to_string()]);
        assert!(atten.bundle.asset("app.js").is_none());
    }

    // ── TRANSCLUDE A DOM FRAGMENT: a span/region of the published surface's rendered
    //    DOM renders into a DreggverseDocument with provenance. ──

    #[test]
    fn a_dom_fragment_of_a_published_surface_transcludes_into_a_document_with_provenance() {
        let surface = counter_surface(3);
        let mut web = WebOfCells::new(3);
        let lineage = SurfaceCapability::root(cid(2), AuthRequired::Either);
        let (published, _sr) =
            publish_live_surface(&mut web, 2, surface, lineage, InteractionLog::new(), false)
                .unwrap();

        // The rendered view is
        // `<div id="app"><h1>counter: 3</h1><button class="inc">++</button></div>`.
        // The `<h1>counter: 3</h1>` substring is at a known byte range — quote exactly
        // that DOM fragment as a span of a document.
        let html = String::from_utf8(
            published
                .bundle()
                .asset(RENDERED_VIEW_ASSET)
                .unwrap()
                .bytes
                .clone(),
        )
        .unwrap();
        let h1 = "<h1>counter: 3</h1>";
        let start = html
            .find(h1)
            .expect("the h1 fragment is in the rendered view");
        let range = SpanRange::new(start, start + h1.len());

        let doc = DreggverseDocument::from_spans(vec![
            Span::own(b"LIVE: ".to_vec()),
            published.quote_fragment(range),
            Span::own(b" (from the surface)".to_vec()),
        ]);
        let rendered = doc
            .resolve(&web)
            .expect("the document resolves the DOM-fragment span");

        // The composed text quotes exactly the DOM fragment.
        assert_eq!(
            rendered.composed_text().unwrap(),
            "LIVE: <h1>counter: 3</h1> (from the surface)"
        );
        // The transcluded span carries the surface's receipt-pinned provenance.
        let prov = rendered.spans()[1]
            .provenance()
            .expect("the DOM-fragment span is provenanced");
        assert_eq!(
            prov.source, published.uri,
            "the span cites the published surface"
        );
        assert!(prov.finalized, "a published+attested surface is finalized");
        // The parallel-source link (the EEL) navigates back to the surface + range.
        assert_eq!(
            rendered.spans()[1].source_link(),
            Some((published.uri.clone(), range))
        );
    }

    #[test]
    fn the_dom_state_fragment_is_the_live_quote_with_provenance() {
        // The structural DOM-state fragment transcludes whole as the live quote (the
        // genuine BundleFragmentQuote), carrying the source's provenance + re-verifying.
        let surface = counter_surface(5);
        let mut web = WebOfCells::new(3);
        let lineage = SurfaceCapability::root(cid(3), AuthRequired::Either);
        let (published, _sr) = publish_live_surface(
            &mut web,
            3,
            surface.clone(),
            lineage,
            InteractionLog::new(),
            false,
        )
        .unwrap();

        let quote = published
            .quote_dom_state(&web)
            .expect("the dom-state fragment transcludes");
        // The fragment bytes ARE the surface's serialized DOM-state (not a copy).
        assert_eq!(quote.fragment_bytes, surface.dom_state());
        assert_eq!(quote.asset_name, DOM_STATE_ASSET);
        assert_eq!(quote.cite().source, published.uri);
        assert!(
            quote.verify().is_ok(),
            "the live quote's provenance re-verifies"
        );
    }

    // ── THE DARKENED VIEWER: a viewer lacking authority sees the citation, not the
    //    DOM bytes. ──

    #[test]
    fn a_darkened_viewer_sees_the_citation_not_the_dom_bytes() {
        // The document transcludes the surface's rendered DOM. A full-authority viewer
        // reads it; a viewer whose projection cannot reach the surface's origin sees
        // the span DARKENED — the citation (source + receipt) survives, the DOM bytes
        // are withheld, never forged.
        let surface = counter_surface(9);
        let mut web = WebOfCells::new(3);
        let seed = 4u8;

        // Scope the lineage to the surface's rendered-view origin (so a full viewer
        // reaches it, a scoped-elsewhere viewer darkens it). Learn the cell first.
        let probe = SurfaceCapability::root(cid(seed), AuthRequired::Either);
        let (probe_pub, _) = publish_live_surface(
            &mut web,
            seed,
            surface.clone(),
            probe,
            InteractionLog::new(),
            false,
        )
        .unwrap();
        let cell = probe_pub.cell();
        // The span's origin is the rendered-view asset's origin (quote_rendered quotes
        // RENDERED_VIEW_ASSET).
        let view_origin = WebBundle::asset_origin(cell, RENDERED_VIEW_ASSET);
        let lineage = SurfaceCapability::scoped(
            cell,
            AuthRequired::Either,
            origins(std::slice::from_ref(&view_origin)),
            [],
        );

        let mut web = WebOfCells::new(3);
        let (published, _sr) = publish_live_surface(
            &mut web,
            seed,
            surface,
            lineage.clone(),
            InteractionLog::new(),
            false,
        )
        .unwrap();
        assert_eq!(published.cell(), cell);

        let doc = DreggverseDocument::from_spans(vec![
            Span::own(b"[".to_vec()),
            published.quote_rendered(),
            Span::own(b"]".to_vec()),
        ]);

        // A FULL viewer (wildcard fetch) reaches the surface: the DOM renders for real.
        let full_viewer = Membrane::new(SurfaceCapability::root(cid(20), AuthRequired::Either));
        let full = doc
            .resolve_for(&web, &full_viewer, &lineage)
            .expect("full viewer resolves");
        assert!(full.is_full());
        assert!(full.composed_text().unwrap().contains("counter: 9"));

        // A DARKENED viewer scoped to a DIFFERENT origin (not the surface's view origin):
        // the membrane meet excludes the surface, so the span darkens.
        let elsewhere = WebBundle::asset_origin(cell, "some-other-asset");
        let darkened_viewer = Membrane::new(SurfaceCapability::scoped(
            cid(31),
            AuthRequired::Either,
            origins(&[elsewhere]),
            [],
        ));
        let dark = doc
            .resolve_for(&web, &darkened_viewer, &lineage)
            .expect("darkened viewer resolves (with a darkened span)");
        assert!(!dark.is_full());
        assert_eq!(dark.darkened_count(), 1);
        // The DOM bytes are withheld: the viewer never sees the count.
        assert_eq!(dark.composed_text().unwrap(), "[]");
        assert!(
            !dark
                .composed_bytes()
                .windows(b"counter".len())
                .any(|w| w == b"counter"),
            "a darkened viewer never sees the surface's DOM bytes"
        );
        // …BUT the citation survives (the darkened span still cites the surface).
        let span = &dark.spans()[1];
        assert!(matches!(span, RenderedSpan::Darkened { .. }));
        assert_eq!(span.provenance().unwrap().source, published.uri);
        assert!(span.provenance().unwrap().finalized);
    }

    // ── AMEND-TRACKS-LIVE: re-publishing the surface advances the committed DOM-state
    //    height; a snapshot pins the old, a live transclusion re-resolves to the new. ──

    #[test]
    fn amend_advances_the_dom_state_and_the_snapshot_live_dial_tracks() {
        // Publish the counter at 3. Pin a SNAPSHOT of the DOM state, stand up a LIVE
        // quote. Amend the surface to 4. The snapshot still reads count-3 DOM state
        // (I-confluent); the live quote re-resolves to count-4 (the unbreakable link).
        let mut web = WebOfCells::new(3);
        let lineage = SurfaceCapability::root(cid(6), AuthRequired::Either);
        let (mut published, _sr) = publish_live_surface(
            &mut web,
            6,
            counter_surface(3),
            lineage,
            InteractionLog::new(),
            false,
        )
        .unwrap();

        let v0_state = counter_surface(3).dom_state();
        let v1_state = counter_surface(4).dom_state();
        assert_ne!(v0_state, v1_state);

        // Pin a snapshot of the current (count-3) committed bundle + a live quote.
        let snap = published.dom_state_snapshot(&web).expect("snapshot v0");
        let live = published.dom_state_live();
        assert!(snap.pinning().is_snapshot());
        let pinned_height = snap.pinning().pinned_height().expect("a pinned height");

        // Both read v0 now (the snapshot's pinned bundle decodes to the count-3
        // dom-state asset; the live quote resolves the same current value).
        let snap_r0 = snap.read(&web).expect("snapshot reads v0");
        assert_eq!(decode_dom_state(snap_r0.displayed_bytes()), v0_state);

        // RE-PUBLISH ON CHANGE: amend the surface to the count-4 DOM state.
        let new_height = published
            .amend(&mut web, counter_surface(4))
            .expect("amend advances the surface");
        assert!(
            new_height > pinned_height,
            "the committed DOM-state height advanced"
        );
        // The handle now reflects the new capture, at the SAME dregg:// ref.
        assert_eq!(published.surface, counter_surface(4));

        // THE SNAPSHOT IS STABLE — still the count-3 DOM state, same cited receipt.
        let snap_r1 = snap.read(&web).expect("snapshot reads post-amend");
        assert_eq!(
            decode_dom_state(snap_r1.displayed_bytes()),
            v0_state,
            "the snapshot stays pinned to the OLD DOM-state height (I-confluent)"
        );
        assert_eq!(
            snap_r1.cite().receipt_hash,
            snap_r0.cite().receipt_hash,
            "the snapshot's cited receipt is unchanged"
        );

        // THE LIVE QUOTE RE-RESOLVES — now the count-4 DOM state, advanced receipt.
        let live_r1 = live.read(&web).expect("live re-reads post-amend");
        assert_eq!(
            decode_dom_state(live_r1.displayed_bytes()),
            v1_state,
            "the live transclusion re-resolves to the NEW committed DOM state"
        );
        assert_ne!(
            live_r1.cite().receipt_hash,
            snap_r0.cite().receipt_hash,
            "the live read's cited receipt advanced with the surface"
        );

        // A fresh fetch of the SAME ref now decodes the count-4 capture (the cell IS
        // the current DOM state).
        let (fetched, _c) = fetch_bundle(&web, &published.uri).expect("fetch post-amend");
        assert_eq!(fetched.asset(DOM_STATE_ASSET).unwrap().bytes, v1_state);

        // Both reads still verify (the dial changes the value, never the faithfulness).
        assert!(snap_r1.verify().is_ok());
        assert!(live_r1.verify().is_ok());
        // The dial positions are legible: the snapshot is pinned, the live re-resolves.
        assert!(snap.pinning().is_snapshot() && live.pinning().is_live());
    }

    #[test]
    fn a_dom_fragment_quote_tracks_the_amended_surface_live() {
        // A document that quotes the WHOLE rendered DOM of the surface re-resolves to
        // the surface's CURRENT rendered view on each resolve — amend the surface, the
        // quote follows (the unbreakable link at the DOM level).
        let mut web = WebOfCells::new(3);
        let lineage = SurfaceCapability::root(cid(7), AuthRequired::Either);
        let (mut published, _sr) = publish_live_surface(
            &mut web,
            7,
            counter_surface(3),
            lineage,
            InteractionLog::new(),
            false,
        )
        .unwrap();

        let doc = DreggverseDocument::from_spans(vec![published.quote_rendered()]);

        // v0: the document renders the count-3 view.
        let r0 = doc.resolve(&web).expect("v0 resolves");
        assert!(r0.composed_text().unwrap().contains("counter: 3"));
        let receipt_v0 = r0.spans()[0].provenance().unwrap().receipt_hash;

        // Amend the surface to count-4.
        published
            .amend(&mut web, counter_surface(4))
            .expect("amend");

        // v1: the SAME document, re-resolved, now renders the count-4 view (the quote
        // tracked the surface live), with an advanced cited receipt.
        let r1 = doc.resolve(&web).expect("v1 resolves (same EDL)");
        assert!(r1.composed_text().unwrap().contains("counter: 4"));
        assert!(!r1.composed_text().unwrap().contains("counter: 3"));
        let receipt_v1 = r1.spans()[0].provenance().unwrap().receipt_hash;
        assert_ne!(
            receipt_v1, receipt_v0,
            "the cited receipt advanced with the surface"
        );
    }

    #[test]
    fn amend_of_an_unpublished_surface_is_origin_not_found() {
        // Build a PublishedSurface handle whose ref was never actually committed; amend
        // refuses (OriginNotFound) — you cannot amend a surface that was not published.
        let mut web = WebOfCells::new(3);
        let mut handle = PublishedSurface {
            uri: DreggUri::new(cid(222)),
            seed: 222,
            lineage: SurfaceCapability::root(cid(222), AuthRequired::Either),
            surface: counter_surface(0),
        };
        assert_eq!(
            handle.amend(&mut web, counter_surface(1)),
            Err(AmendError::Fetch(FetchError::OriginNotFound))
        );
    }

    /// Decode the `dom-state` asset bytes out of a versioned read's displayed bundle
    /// bytes (the read displays the surface cell's WHOLE committed bundle; we pull the
    /// dom-state asset to compare DOM states).
    fn decode_dom_state(bundle_bytes: &[u8]) -> Vec<u8> {
        let bundle =
            WebBundle::decode(bundle_bytes).expect("the displayed bytes decode as a bundle");
        bundle
            .asset(DOM_STATE_ASSET)
            .expect("a dom-state asset")
            .bytes
            .clone()
    }
}
