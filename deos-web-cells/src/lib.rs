//! # deos-web-cells — live-DOM / JS-bundle web-of-cells cells
//!
//! A web-of-cells cell can CONTAIN web content. This crate is the
//! **frustum-snapshot applied to the DOM**: you "publish/commit JS bundles, or
//! even bundles of LIVE DOM state, and share that as part of the web-of-cells."
//! A bundle as a `dregg://` cell is:
//!
//! - **content-addressed** — identity = the `blake3` of the canonical bundle
//!   encoding ([`WebBundle::content_hash`]); two bundles are the same cell iff
//!   they encode the same bytes;
//! - **cap-gated** — it is published into a REAL surface cell and fetched through
//!   the REAL attested `dregg://` cross-cell read ([`fetch_bundle`]); an
//!   unattested / tampered / dead bundle yields a [`BundleError`], never bytes;
//! - **transcludable** — another surface includes a *fragment* of it carrying
//!   provenance (Ted Nelson at the DOM level), through the REAL
//!   `starbridge_web_surface::transclusion` ([`cascade`]);
//! - **rehydratable** — a [`DomSnapshot`] is the frustum-snapshot of a published
//!   bundle (a [`Sturdyref`] + a tiny [`BundleBoundary`], NOT the bytes), and
//!   [`rehydrate_bundle`] re-expands it PER-VIEWER through the REAL [`Membrane`];
//! - **liveness-typed** — Live / ReplayedDeterministic / ReconstructedApproximate
//!   is the rehydration-stack's [`Rehydration`], DERIVED from the source context's
//!   witness-log, surfaced at rehydration.
//!
//! The **leptosic angle**: a Leptos app's live signal-graph state IS a "live DOM
//! bundle" — publishing it as a [`BundleKind::LiveDomSnapshot`] cell shares your
//! app's live state as a transcludable, rehydratable, cap-confined artifact. The
//! SSR→hydrate shape of a Leptos app *is* the rehydration shape: serialize the
//! signal graph into a snapshot asset, publish, and re-expand per-viewer.
//!
//! ## This crate builds NOTHING the protocol already has
//!
//! It is a thin, web-bundle layer over the STABLE public API of
//! [`starbridge_web_surface`]. Everything load-bearing is the genuine machinery:
//!
//! - the `dregg://` publish/fetch is [`starbridge_web_surface::WebOfCells`] —
//!   we add NO bespoke fetch, NO parallel attestation;
//! - the snapshot/membrane is [`starbridge_web_surface::rehydrate`] —
//!   [`Sturdyref`], [`Membrane`], [`rehydrate`], the [`Rehydration`]
//!   liveness-type. We reinvent NO membrane, NO snapshot; the per-viewer
//!   attenuation is the SAME `is_attenuation` lattice;
//! - the cap is [`SurfaceCapability`] (a firmament `Capability{ Surface(cell),
//!   rights }`); per-asset visibility rides the REAL fetch-allowlist meet
//!   ([`SurfaceCapability::may_fetch`]), never a parallel filter;
//! - transclusion is [`starbridge_web_surface::transclusion::TranscludedField`] —
//!   the verified cross-cell finalized read NAMED as Nelson's quote, with the
//!   REAL [`Provenance`].
//!
//! ## What is real vs. the seam
//!
//! - **Real (addressing + attestation + the cap discipline + transclusion):** the
//!   content hash is the genuine `blake3` the web-of-cells commits; the publish
//!   writes it into a REAL `dregg_cell::Cell`; the fetch is the REAL attested
//!   cross-cell read + `verify()`; the per-viewer projection is the REAL
//!   [`Membrane`]; the transclusion is the REAL `TranscludedField` carrying the
//!   REAL receipt-pinned [`Provenance`].
//! - **The seam (named, not papered): the RENDER, and the LIVE Leptos binding.**
//!   Turning the verified bundle bytes into pixels is the `servo-render` Stage-A
//!   cap-gated pipeline (`servo-render::fetch_render_present`) — the
//!   transcluded-fragment-in-a-page is where transclusion reaches the actual web
//!   ([`cascade`] points at it). Binding a *running* Leptos signal-graph to a
//!   `LiveDomSnapshot` (capturing live signals → a snapshot asset → reactive
//!   re-expansion) needs the in-flight `deos-leptos` crate and is the named
//!   demonstrable follow-on; this crate ships the bundle + snapshot + rehydrate +
//!   transclude core against the STABLE API, with a `LiveDomSnapshot` bundle as
//!   the concrete carrier the live binding will populate.

pub mod bundle;
pub mod cascade;
pub mod rehydrate;

// ── The crate's surface: the bundle data model + publish/fetch, the DOM
//    frustum-snapshot + per-viewer rehydration, and the web-level transclusion
//    cascade. Everything below `bundle`/`rehydrate`/`cascade` is named from the
//    STABLE starbridge-web-surface API (re-exported here so a consumer of THIS
//    crate names the genuine model, not a parallel one). ──

pub use bundle::{
    fetch_bundle, publish_bundle, BundleAsset, BundleError, BundleKind, BundleManifest, WebBundle,
};
pub use cascade::{transclude_bundle_fragment, BundleFragmentQuote, CascadeError};
pub use rehydrate::{
    rehydrate_bundle, BundleBoundary, DomSnapshot, RehydratedBundle, SnapshotError,
};

// Re-export the REAL stable web-of-cells + rehydration + membrane API this crate
// is a thin layer over — so a consumer names the genuine types directly. We never
// reinvent any of these. (The `rehydrate` *function* is intentionally NOT re-exported
// at the crate root — it would collide with this crate's `rehydrate` module; it is
// reachable as `starbridge_web_surface::rehydrate`, and a consumer of THIS crate uses
// the bundle-aware [`rehydrate_bundle`].)
pub use starbridge_web_surface::{
    is_attenuation, AttestedResource, AuthRequired, Capability, DreggUri, FetchError, Membrane,
    OriginChrome, Projection, Rehydration, RehydrateError, Sturdyref, SurfaceCapability, WebOfCells,
};
pub use starbridge_web_surface::rehydrate::{Interaction, InteractionLog};
pub use starbridge_web_surface::transclusion::{Provenance, TranscludedField, TransclusionError};

// The REAL content-addressed cell identity (re-exported by starbridge-web-surface,
// named here so a bundle's boundary cell is the genuine type).
pub use dregg_types::CellId;

/// Shared test scaffolding — a deterministic [`CellId`] helper used by the inline
/// module tests and the integration tests. (Not part of the crate's runtime
/// surface; it derives a content-addressed cell id from a seed byte the way the
/// web-of-cells' own tests do.)
#[doc(hidden)]
pub mod tests_support {
    use dregg_types::CellId;

    /// A deterministic content-addressed [`CellId`] from a seed byte — the same
    /// derivation the `starbridge-web-surface` tests use (`CellId::derive_raw`
    /// over a one-hot key + a zero domain), so cells minted here line up with the
    /// genuine content-addressed identity space.
    pub fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }
}
