//! `servo-render` — the HOST SWGL render path that IS deos's compositor render
//! pass (**Stage A** of `docs/desktop-os-research/SERVO-ON-SEL4.md`).
//!
//! # The one paragraph
//!
//! The compositor-PD (`sel4/dregg-firmament/src/compositor_pd.rs`) carries a
//! `present(region, contentDigest)` whose `contentDigest` is, today, a *promise*
//! of pixels — its honestly-labeled **F3** fidelity gap. This crate makes the
//! pixels REAL: a [`SwglRenderingContext`](swgl_context::SwglRenderingContext)
//! backed by WebRender's **SWGL** (`swgl 0.68.0` — a self-contained, CPU-only,
//! framebuffer-out software GL that `impl Gl for swgl::Context`, so it IS a
//! `gleam::gl::Gl`) renders a page into a caller-owned RGBA8 `Vec<u8>`, and
//! [`compositor_seam::present_frame`] hashes those bytes to the `content_digest`
//! the compositor's unchanged T1/T2/T3 gate admits. **No GPU, no EGL, no platform
//! surface** — "unaccelerated but real."
//!
//! # The HONEST build split (this crate's whole design)
//!
//! - **`swgl-standalone` (DEFAULT)** — depends on NOTHING but `swgl` + `gleam` (+
//!   the real `dregg-firmament` for the compositor seam). This is the de-risking
//!   core: it proves SWGL's C++17 rasterizer (clang, `gl.cc`) COMPILES on this
//!   host and produces REAL RGBA8 pixels, *independent of the libservo elephant*.
//!   The tests here exercise that.
//! - **`libservo` (OPT-IN)** — adds the real `servo` + `servo-paint-api` and wires
//!   the SWGL context into a real `WebView` (see [`webview`]). This pulls `script`
//!   → `mozjs` (the multi-GB SpiderMonkey C++ build) — the known-hard, known-walked
//!   long pole, kept behind a feature so the core builds without grinding it.
//!
//! # What closes and what doesn't (NOT laundered)
//!
//! When the SWGL frame's digest drives `present()`, **F3 (real pixels from a
//! confined renderer)** closes on the host. **F1** (binding the *scanned-out*
//! framebuffer to the digest) and **F2** (IOMMU/DMA-confining a display PD) are
//! NOT touched and NOT claimed — they are the named hardware-trust frontier
//! (`SERVO-ON-SEL4.md §3.3`). "The pixels are real" does not launder "the scan-out
//! is attested."
//!
//! # Module map
//!
//! - [`swgl_context`] — the [`SwglRenderingContext`](swgl_context::SwglRenderingContext)
//!   shim + the load-bearing "SWGL produces real RGBA8" test.
//! - [`compositor_seam`] — [`present_frame`](compositor_seam::present_frame): the
//!   render→hash→present→gate→blit step against the GENUINE compositor-PD.
//! - [`cap_gated_pipeline`] — [`fetch_render_present`](cap_gated_pipeline::fetch_render_present):
//!   the cap gate (the REAL `starbridge_web_surface::CapGatedDelegate`) IN FRONT of
//!   the SWGL render → compositor present, so a frame reaches the glass only through
//!   a held [`SurfaceCapability`](starbridge_web_surface::SurfaceCapability). Joins
//!   Stage-A steps 4 (the cap gate) and 5 (the render→glass).
//! - [`webview`] (feature `libservo`) — the real-`RenderingContext`-trait adapter
//!   over SWGL that a real `WebView` paints into.

pub mod swgl_context;

#[cfg(feature = "swgl-standalone")]
pub mod compositor_seam;

/// The cap-gated render pipeline — Stage A's two halves (the `starbridge-web-surface`
/// cap gate + this crate's SWGL render → compositor present), joined.
#[cfg(feature = "swgl-standalone")]
pub mod cap_gated_pipeline;

/// The starbridge-v2 integration entry — an attested `dregg://` page's bytes
/// rendered to a real, cap-gated SWGL [`swgl_context::RgbaFrame`] the cockpit
/// web-of-cells tab paints (the FIRST real rendered `dregg://` content, today,
/// without the `libservo`/mozjs elephant). See [`content_tile::render_dregg_page`].
#[cfg(feature = "swgl-standalone")]
pub mod content_tile;

#[cfg(feature = "libservo")]
pub mod webview;

/// **THE NET-CAP CONNECTOR** — the page's outbound socket bound to the dregg `captp`
/// [`Netlayer::dial`](dregg_captp::netlayer::Netlayer::dial) transport. Always
/// present (it needs neither SWGL nor libservo): a fetch the held
/// [`SurfaceCapability`](starbridge_web_surface::SurfaceCapability) does not authorize
/// is refused AT the connector before any dial (the socket never opens); an authorized
/// origin connects through the audited netlayer. See [`netcap_connector`].
pub mod netcap_connector;

pub use netcap_connector::{block_on as netcap_block_on, ConnectOutcome, NetcapConnector};

#[cfg(feature = "swgl-standalone")]
pub use swgl_context::{
    with_gl, ReadRect, RenderingContext, RgbaFrame, SwglRenderingContext, GL_LOCK,
};

#[cfg(feature = "swgl-standalone")]
pub use compositor_seam::{present_frame, FramePresentation};

#[cfg(feature = "swgl-standalone")]
pub use cap_gated_pipeline::{fetch_render_present, PipelineOutcome};

#[cfg(feature = "swgl-standalone")]
pub use content_tile::{render_dregg_page, TileOutcome};
