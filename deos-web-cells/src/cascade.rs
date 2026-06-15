//! The **web-level cascade** — how transclusion reaches the actual web: a
//! transcluded `dregg://` bundle fragment rendered in a page is the live quote.
//!
//! `docs/deos/WEB-CELLS.md`: Ted Nelson's transclusion (include-by-reference where
//! the quote keeps its identity + provenance) applied at the DOM level. Another
//! surface includes a *fragment* of a published bundle — a named asset (a `<script>`,
//! a stylesheet, a DOM partial) — and the inclusion is a **verified cross-cell
//! finalized read** carrying the source's receipt-pinned provenance, never a copy
//! that can silently diverge.
//!
//! This module reinvents NOTHING: it is a thin bundle-aware wrapper over the REAL
//! `starbridge_web_surface::transclusion`:
//!
//! - [`transclude_bundle_fragment`] performs the REAL
//!   [`TranscludedField::include`] (the genuine `dregg://` attested finalized read +
//!   the `content→commitment→receipt→receipt-stream-root→quorum` verification)
//!   against the bundle cell, then extracts the named asset's bytes from the
//!   verified, attested bundle. The displayed fragment bytes ARE the source's
//!   committed bytes; a verifier recomputes them; the [`Provenance`] dates them.
//! - The result [`BundleFragmentQuote`] carries the verified [`TranscludedField`]
//!   (so its provenance re-verifies at any time) + the asset name + the fragment
//!   bytes + the genuine receipt-pinned [`Provenance`]. It is the "live quote": the
//!   honest, dated inclusion of a peer bundle's fragment into another surface.
//!
//! ## The web-level cascade — where the pixels come from
//!
//! A [`BundleFragmentQuote`] is the cap-confined, attested, provenanced fragment a
//! page embeds. Turning it into PIXELS is the `servo-render` Stage-A cap-gated
//! render pipeline (`servo-render::fetch_render_present` — the servo Stage-A
//! cap-gated render seam): the fragment's bytes flow through the SAME
//! `WebSurfaceDelegate` cap gate (`load_web_resource`), so a transcluded fragment is
//! subject to the embedding surface's caps exactly as any subresource is — and the
//! render→glass step rasterizes it. This module produces the fragment the renderer
//! consumes; it does not itself rasterize DOM (the libservo seam
//! `starbridge_web_surface::delegate::MockSurface` already names). The cascade is:
//!
//! ```text
//!   dregg:// bundle cell ──TranscludedField::include──▶ verified attested bundle
//!         │  (content-addressed + receipt + quorum-signed root)
//!         ▼
//!   transclude_bundle_fragment ──▶ BundleFragmentQuote { fragment bytes + Provenance }
//!         │  (the live quote — honest, dated, recomputable)
//!         ▼
//!   embedding surface's cap gate (load_web_resource) ──▶ servo-render::fetch_render_present
//!         │  (Stage-A: cap-gate IN FRONT of the render)
//!         ▼
//!   pixels on the glass — the transcluded fragment rendered in a page
//! ```
//!
//! ## What is real vs. the seam
//!
//! - **Real (the transclusion + the provenance):** the include is the REAL
//!   verified cross-cell finalized read; the provenance is the REAL receipt-pinned
//!   citation; a forged/absent/un-finalized quote is REFUSED (no opened provenance
//!   ⇒ no fragment).
//! - **The seam (named, not papered): the RENDER.** The fragment-to-pixels step is
//!   `servo-render::fetch_render_present` (the Stage-A cap-gated pipeline, just
//!   landed). This crate hands that pipeline the attested, provenanced fragment.

use starbridge_web_surface::transclusion::{Provenance, TranscludedField, TransclusionError};
use starbridge_web_surface::{DreggUri, WebOfCells};

use crate::bundle::{BundleError, WebBundle};

/// A **transcluded bundle fragment** — the live quote: a named asset of a published
/// bundle, included BY REFERENCE into another surface, carrying the source's
/// receipt-pinned provenance.
///
/// `docs/deos/WEB-CELLS.md`: this is Nelson's quote at the DOM level. The
/// `fragment_bytes` ARE the source asset's committed bytes (drawn from the verified,
/// attested bundle — not a copy that may diverge); the [`TranscludedField`] is the
/// genuine finalized read it was extracted from (so the whole bundle's provenance
/// re-verifies at any time); the [`Provenance`] is the immutable, dated citation
/// ("quoted from `dregg://<cell>`'s `<asset>` at receipt R; finalized").
#[derive(Clone, Debug)]
pub struct BundleFragmentQuote {
    /// The verified attested bundle this fragment was transcluded FROM (the
    /// finalized-read result — its provenance re-verifies via
    /// [`TranscludedField::verify`]).
    pub field: TranscludedField,
    /// The name of the bundle asset that was quoted (the fragment's identity within
    /// the source bundle — e.g. `app.js`, `theme.css`, `dom-state`).
    pub asset_name: String,
    /// The fragment bytes — the source asset's committed content. These ARE the
    /// source's bytes (drawn from the attested, verified bundle), the live quote a
    /// page embeds.
    pub fragment_bytes: Vec<u8>,
}

/// What can go wrong transcluding a bundle fragment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CascadeError {
    /// The source `dregg://` bundle ref did not resolve to a verified finalized
    /// read, or its provenance did not verify, or it was not quorum-finalized — the
    /// REAL [`TransclusionError`], carried through. No opened provenance ⇒ no
    /// fragment.
    Transclusion(TransclusionError),
    /// The verified, attested content the source committed did not decode as a
    /// bundle (the source cell is not a `deos-web-cells` bundle cell) — the real
    /// [`BundleError`], carried through. The attestation held, but it is not a
    /// bundle.
    Bundle(BundleError),
    /// The bundle resolved + verified, but carries no asset by the requested name —
    /// you cannot transclude a fragment that is not in the source bundle.
    NoSuchAsset {
        /// The asset name that was requested but is not in the source bundle.
        asset_name: String,
    },
}

impl From<TransclusionError> for CascadeError {
    fn from(e: TransclusionError) -> Self {
        CascadeError::Transclusion(e)
    }
}

impl From<BundleError> for CascadeError {
    fn from(e: BundleError) -> Self {
        CascadeError::Bundle(e)
    }
}

/// **Transclude one bundle's fragment INTO another surface** — the web-level
/// cascade, carrying provenance.
///
/// `docs/deos/WEB-CELLS.md`: the Nelson hyperlink at the DOM level. Performs the
/// REAL `dregg://` verified cross-cell finalized read against the bundle cell
/// (`source`), via [`TranscludedField::include`] — which VERIFIES the
/// `content→commitment→receipt→receipt-stream-root→quorum` chain and REFUSES a
/// forged / absent / un-finalized quote — then decodes the verified, attested
/// bundle and extracts the named asset's bytes.
///
/// The returned [`BundleFragmentQuote`]'s `fragment_bytes` ARE the source asset's
/// committed bytes, with the receipt-pinned [`Provenance`] that dates them. The
/// quote never rots: the citation pins an immutable receipt, so even after the
/// source advances, the quote remains the value committed at the cited point
/// (`transclusion_stable_under_source_advance`). What an embedding surface may do
/// with the fragment is then gated by ITS caps (the cascade's render step); the
/// transclusion confers no authority over the source beyond observing the cited
/// value.
pub fn transclude_bundle_fragment(
    web: &WebOfCells,
    source: &DreggUri,
    asset_name: &str,
) -> Result<BundleFragmentQuote, CascadeError> {
    // (1) THE FINALIZED READ — the REAL verified cross-cell observation of the
    //     bundle cell. Verifies the provenance chain + refuses a forged/absent/
    //     un-finalized quote (no opened provenance ⇒ no fragment).
    let field = TranscludedField::include(web, source)?;

    // (2) Decode the VERIFIED, attested bundle bytes. The quoted bytes the
    //     transclusion carries ARE the source's committed bytes (content-addressed);
    //     they decode as the source bundle.
    let bundle = WebBundle::decode(field.quoted_bytes())?;

    // (3) Extract the named fragment. The fragment bytes ARE the source asset's
    //     committed bytes.
    let asset = bundle
        .asset(asset_name)
        .ok_or_else(|| CascadeError::NoSuchAsset {
            asset_name: asset_name.to_string(),
        })?;

    Ok(BundleFragmentQuote {
        field,
        asset_name: asset_name.to_string(),
        fragment_bytes: asset.bytes.clone(),
    })
}

impl BundleFragmentQuote {
    /// **Re-verify the fragment's provenance** — the quoted value EQUALS its source,
    /// recomputably. Runs the genuine
    /// `content→commitment→receipt→receipt-stream-root→quorum` chain over the
    /// transcluded bundle (the REAL [`TranscludedField::verify`]); a fragment whose
    /// underlying bundle was tampered REFUSES. A holder can recompute faithfulness
    /// at any time.
    pub fn verify(&self) -> Result<(), starbridge_web_surface::FetchError> {
        self.field.verify()
    }

    /// The immutable citation this fragment carries (the source bundle ref + the
    /// receipt + the content commitment + finalized) — what tooling renders as
    /// "quoted from `dregg://<cell>`'s `<asset>` at receipt R; finalized". The
    /// honest, dated provenance.
    pub fn cite(&self) -> &Provenance {
        self.field.cite()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bundle::{publish_bundle, BundleAsset, BundleKind};
    use crate::tests_support::cid;
    use starbridge_web_surface::rehydrate::InteractionLog;
    use starbridge_web_surface::AuthRequired;

    /// Publish a three-asset bundle into a fresh web-of-cells and return (web, ref).
    fn published_bundle(seed: u8) -> (WebOfCells, DreggUri) {
        let bundle = WebBundle::new(
            BundleKind::StaticBundle,
            "index.html",
            vec![
                BundleAsset::new("index.html", "text/html", b"<h1>source page</h1>".to_vec()),
                BundleAsset::new("widget.js", "application/javascript", b"renderWidget()".to_vec()),
                BundleAsset::new("theme.css", "text/css", b"h1{color:teal}".to_vec()),
            ],
        )
        .expect("valid bundle");
        let mut web = WebOfCells::new(3);
        let lineage = root_lineage(seed);
        let (uri, _sr) =
            publish_bundle(&mut web, seed, &bundle, lineage, InteractionLog::new(), false);
        (web, uri)
    }

    fn root_lineage(seed: u8) -> starbridge_web_surface::SurfaceCapability {
        starbridge_web_surface::SurfaceCapability::root(cid(seed), AuthRequired::Either)
    }

    // ── A fragment is transcluded with its provenance; the bytes ARE the source's. ──

    #[test]
    fn transclude_a_fragment_carries_the_source_bytes_and_provenance() {
        let (web, uri) = published_bundle(1);

        let quote = transclude_bundle_fragment(&web, &uri, "widget.js")
            .expect("the fragment transcludes");

        // The fragment bytes ARE the source asset's committed bytes (not a copy).
        assert_eq!(quote.fragment_bytes, b"renderWidget()");
        assert_eq!(quote.asset_name, "widget.js");
        // It carries the receipt-pinned provenance: the source bundle ref + finalized.
        assert_eq!(quote.cite().source, uri);
        assert!(quote.cite().finalized, "a published+attested bundle is finalized");
        // And it re-verifies (the whole bundle's content→commitment→receipt→root→
        // quorum chain).
        assert!(quote.verify().is_ok(), "the fragment's provenance must re-verify");
    }

    // ── A different fragment of the same bundle. ──

    #[test]
    fn a_different_fragment_of_the_same_bundle() {
        let (web, uri) = published_bundle(2);
        let css = transclude_bundle_fragment(&web, &uri, "theme.css").expect("css transcludes");
        assert_eq!(css.fragment_bytes, b"h1{color:teal}");
        // Same source, same receipt — two fragments cite the SAME immutable point.
        let js = transclude_bundle_fragment(&web, &uri, "widget.js").expect("js transcludes");
        assert_eq!(css.cite().receipt_hash, js.cite().receipt_hash);
        assert_eq!(css.cite().content_hash, js.cite().content_hash);
    }

    // ── A fragment that is not in the source bundle is refused. ──

    #[test]
    fn a_missing_fragment_is_refused() {
        let (web, uri) = published_bundle(3);
        let r = transclude_bundle_fragment(&web, &uri, "nonexistent.js");
        // BundleFragmentQuote carries a TranscludedField (not Eq), so match the error.
        assert!(
            matches!(&r, Err(CascadeError::NoSuchAsset { asset_name }) if asset_name == "nonexistent.js"),
            "a fragment not in the source bundle is refused, got {r:?}"
        );
    }

    // ── An absent / dead source cannot be transcluded (no finalized read). ──

    #[test]
    fn an_absent_source_cannot_be_transcluded() {
        let web = WebOfCells::new(3);
        let absent = DreggUri::new(cid(200));
        let r = transclude_bundle_fragment(&web, &absent, "widget.js");
        assert!(
            matches!(r, Err(CascadeError::Transclusion(TransclusionError::Fetch(_)))),
            "an absent source yields no finalized read, got {r:?}"
        );
    }

    // ── A FORGED quote cannot be opened: the verification chain catches tampered
    //    transcluded bytes. ──

    #[test]
    fn a_forged_quote_cannot_be_opened() {
        // The property `TranscludedField::include` relies on: the content→commitment→
        // receipt→receipt-stream-root→quorum chain catches a forge. We publish a real
        // bundle, fetch its genuine attested resource, then TAMPER the bytes (the
        // public `AttestedResource.content_bytes` field) — and show `verify()` rejects
        // it. A transclusion built on a resource that does not verify cannot be opened
        // (`include` runs exactly this `verify` and refuses on failure).
        let bundle = WebBundle::static_html(b"<h1>genuine</h1>".to_vec());
        let mut web = WebOfCells::new(3);
        let lineage = root_lineage(4);
        let (uri, _sr) =
            publish_bundle(&mut web, 4, &bundle, lineage, InteractionLog::new(), false);

        // A genuine quote opens + verifies.
        let genuine = transclude_bundle_fragment(&web, &uri, "index.html")
            .expect("the genuine fragment transcludes");
        assert!(genuine.verify().is_ok());

        // Now FORGE: tamper the underlying attested resource's bytes. The content no
        // longer matches the committed content_hash, so the chain rejects — a forged
        // quote cannot be opened.
        let (mut resource, _chrome) = web.fetch(&uri).expect("genuine fetch");
        resource.content_bytes = b"FORGED - different bytes the origin never committed".to_vec();
        assert_eq!(
            resource.verify(),
            Err(starbridge_web_surface::FetchError::ContentHashMismatch),
            "the verification chain catches a forged quote's tampered bytes"
        );
    }

    // ── A non-bundle cell (attested, but not a bundle) is a Bundle decode error. ──

    #[test]
    fn a_non_bundle_source_is_a_decode_error() {
        // Publish raw (non-bundle) content directly through the web-of-cells, then
        // try to transclude a fragment: the attestation HOLDS (it is a real
        // finalized read), but the content is not a bundle → MalformedEncoding.
        let mut web = WebOfCells::new(3);
        let uri = web.publish(5, b"just some html, not a bundle", "dregg://raw");
        let r = transclude_bundle_fragment(&web, &uri, "index.html");
        assert!(
            matches!(&r, Err(CascadeError::Bundle(BundleError::MalformedEncoding))),
            "an attested non-bundle source is a decode error, got {r:?}"
        );
    }
}
