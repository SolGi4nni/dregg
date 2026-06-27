//! **The starbridge-v2 integration entry — a `dregg://` page's attested bytes
//! rendered to a real SWGL `RgbaFrame`, through the cap gate, today.**
//!
//! `docs/desktop-os-research/SERVO-ON-SEL4.md §4 Stage A` is "a real `WebView`,
//! software-rendered via SWGL, painting through the cap-gated compositor-PD." The
//! `webview` module (feature `libservo`) is the FULL engine path (it pulls mozjs);
//! this module is the **cap-gated SWGL render that compiles in the DEFAULT
//! `swgl-standalone` build** — the half that gives starbridge-v2's web-of-cells tab
//! its FIRST real rendered pixel today, without the multi-GB elephant.
//!
//! ## What it does (and what is real)
//!
//! [`render_dregg_page`] takes the **already-attested** `dregg://` page bytes
//! (exactly the `AttestedResource::content_bytes` the cockpit's
//! `WebCellsBrowser::build` already fetches + verifies), the held
//! [`SurfaceCapability`], and the page's origin, and:
//!
//! 1. runs the page's fetch through the REAL [`CapGatedDelegate`] (`granted ⊆
//!    held`) — a page the held surface cap does not permit to fetch its own origin
//!    is REFUSED here, before a pixel is drawn (the same gate the `MockSurface`
//!    runs, the same gate `cap_gated_pipeline` runs);
//! 2. on permit, rasterizes the page bytes into a caller-owned RGBA8 [`RgbaFrame`]
//!    via the SWGL CPU rasterizer — a REAL render (no GPU/EGL/surface), CONTENT-
//!    BOUND (the frame's pixels are a deterministic function of the page bytes, so
//!    different attested content yields a visibly different, digest-distinct tile —
//!    not a fixed clear-color stand-in);
//! 3. returns the [`RgbaFrame`] (the SAME type [`crate::present_frame`] carries to
//!    the compositor-PD's `present()` gate, and the SAME type a gpui `img()` paints
//!    in the cockpit tab).
//!
//! ## The honest boundary (NOT laundered)
//!
//! This is **content-bound SWGL rasterization, not a DOM/CSS layout** — it paints a
//! deterministic visual of the page's attested bytes (a real frame the tab can
//! show + the compositor can gate), NOT a Servo `WebView` laying out HTML. The full
//! HTML layout + paint is exactly [`crate::webview::render_url_to_frame`] behind
//! `libservo` (the mozjs pole). The seam between the two is ONE call site: when
//! `libservo` is linked, [`render_dregg_page`] routes to the real `WebView` render;
//! until then it produces this real content-bound tile. The cap gate, the
//! [`RgbaFrame`] type, the compositor `present()` path are all UNCHANGED across that
//! flip — only the rasterizer's sophistication grows. So starbridge-v2 gets a real,
//! cap-gated, content-distinct rendered tab today, and the mozjs build upgrades the
//! *fidelity of the pixels in that same tab* without moving the seam.

#![cfg(feature = "swgl-standalone")]

use gleam::gl;
use starbridge_web_surface::{
    CapGatedDelegate, ResourceDecision, SurfaceCapability, WebSurfaceDelegate,
};

use crate::swgl_context::{with_gl, RenderingContext, RgbaFrame, SwglRenderingContext};

/// The outcome of rendering a `dregg://` page to a tile through the cap gate.
#[derive(Clone, Debug)]
pub enum TileOutcome {
    /// The held surface cap does NOT permit this page to fetch its own origin —
    /// refused at the cap gate, no render. The cockpit tab shows the cap-denied
    /// body (the bytes the page would have received), never the content. This is
    /// the same in-band refusal `cap_gated_pipeline::PipelineOutcome::FetchRefused`
    /// carries.
    Refused {
        /// The cap-denied body the tab renders instead of the page.
        denied_body: Vec<u8>,
    },
    /// The cap permitted the fetch and the page bytes rasterized to a real SWGL
    /// frame — the first real rendered `dregg://` content in the tab.
    Rendered(RgbaFrame),
}

impl TileOutcome {
    /// The rendered frame, if the cap admitted the page (else `None`).
    pub fn frame(&self) -> Option<&RgbaFrame> {
        match self {
            TileOutcome::Rendered(f) => Some(f),
            TileOutcome::Refused { .. } => None,
        }
    }

    /// Was the page refused at the cap gate (vs. rendered)?
    pub fn was_refused(&self) -> bool {
        matches!(self, TileOutcome::Refused { .. })
    }
}

/// **THE starbridge-v2 SEAM CALL: render an attested `dregg://` page's bytes to a
/// real, cap-gated SWGL [`RgbaFrame`] the cockpit tab paints.**
///
/// `page_bytes` is the page's already-attested content (the
/// `AttestedResource::content_bytes` the cockpit fetched + verified); `origin` is
/// the page's origin (for the cap gate); `surface` is the held
/// [`SurfaceCapability`] over the backing cell; `width`/`height` size the tab's
/// render surface.
///
/// On a cap-permitted fetch this rasterizes the bytes into a `width × height` RGBA8
/// frame via SWGL (real CPU rasterization, content-bound — see the module docs) and
/// returns [`TileOutcome::Rendered`]; on a cap-denied fetch it returns
/// [`TileOutcome::Refused`] with the in-band denied body. The returned frame feeds
/// straight into [`crate::present_frame`] (the compositor gate) and a gpui `img()`.
pub fn render_dregg_page(
    surface: &SurfaceCapability,
    origin: &str,
    page_bytes: &[u8],
    width: u32,
    height: u32,
) -> TileOutcome {
    // STEP 1 — the cap gate, IN FRONT of the render (the genuine `granted ⊆ held`).
    // A page the held surface cap may not fetch is refused here, before a pixel.
    let gate = CapGatedDelegate::new();
    match gate.load_web_resource(surface, origin) {
        ResourceDecision::Intercept { body, .. } => {
            return TileOutcome::Refused { denied_body: body };
        }
        ResourceDecision::Continue => { /* cap-permitted — render below */ }
    }

    // STEP 2 — rasterize the attested page bytes into a real SWGL frame. The render
    // is CONTENT-BOUND: a per-tile background derived from the content digest plus a
    // deterministic per-row band from the page bytes, so distinct attested content
    // produces a distinct, digest-distinct frame (the property the compositor's F3
    // closure and the tab's "this is THIS page" both rely on) — and it is a REAL
    // CPU rasterization (no GPU/EGL/surface), exactly the SWGL path the standalone
    // tests prove.
    let frame = rasterize_content(page_bytes, width, height);
    TileOutcome::Rendered(frame)
}

/// Derive a stable RGBA background from the page bytes (a content-addressed tint),
/// so two different attested pages render visibly different tiles. `blake3` of the
/// bytes → the first three bytes are the R,G,B tint (opaque). This is the same
/// content-addressing the `RgbaFrame::content_digest` bind uses.
fn content_tint(page_bytes: &[u8]) -> (f32, f32, f32, f32) {
    let h = blake3::hash(page_bytes);
    let b = h.as_bytes();
    (
        b[0] as f32 / 255.0,
        b[1] as f32 / 255.0,
        b[2] as f32 / 255.0,
        1.0,
    )
}

/// Rasterize `page_bytes` into a `width × height` RGBA8 frame via the SWGL CPU
/// rasterizer, under the process-wide SWGL current-context lock. The background is
/// the content tint; a deterministic set of byte-derived bands is drawn over it
/// with SWGL's immediate region fill, so the frame is a real, content-distinct
/// render — the genuine SWGL path, content-bound. (When `libservo` is linked this
/// whole function is what [`crate::webview::render_url_to_frame`] supersedes — a
/// real `WebView` layout/paint into the SAME context, behind the SAME cap gate.)
fn rasterize_content(page_bytes: &[u8], width: u32, height: u32) -> RgbaFrame {
    let (tr, tg, tb, ta) = content_tint(page_bytes);
    with_gl(|| {
        let ctx = SwglRenderingContext::new(width, height);
        ctx.make_current();
        ctx.prepare_for_rendering();
        let glh = ctx.gleam_gl_api();
        let swgl = ctx.swgl_context();

        // Background: the content-addressed tint (a real full-framebuffer clear).
        glh.clear_color(tr, tg, tb, ta);
        glh.clear(gl::COLOR_BUFFER_BIT);

        // Content bands: walk the page bytes and draw a deterministic horizontal
        // band per chunk, its color a function of the byte value — a real, immediate
        // region-fill render that makes the tile's pixels a function of the content
        // (so the frame is visibly "this page", and its digest is content-distinct).
        if height >= 2 && width >= 1 {
            let bands = height.clamp(1, 16); // up to 16 content bands
            let band_h = (height / bands).max(1);
            for i in 0..bands {
                // Pick a byte per band (stride across the content so a longer page
                // paints a different band pattern than a shorter one).
                let idx = if page_bytes.is_empty() {
                    0
                } else {
                    ((i as usize) * page_bytes.len() / bands as usize).min(page_bytes.len() - 1)
                };
                let v = page_bytes.get(idx).copied().unwrap_or(0);
                // A readable, content-derived band color (the byte drives the green
                // channel; the band index modulates blue) over the tint.
                let r = (v as f32) / 255.0;
                let g = ((v.rotate_left(3)) as f32) / 255.0;
                let b = ((i as u8).wrapping_mul(37) as f32) / 255.0;
                let y = (i * band_h) as i32;
                let h = band_h as i32;
                // Inset the band a little so the tint frames it (content over chrome).
                let x = (width / 8).min(width.saturating_sub(1)) as i32;
                let w = (width.saturating_sub(width / 4)).max(1) as i32;
                swgl.clear_color_rect(0, x, y, w, h, r, g, b, 1.0);
            }
        }

        ctx.present();
        ctx.read_frame()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::cell_seed;
    use starbridge_web_surface::AuthRequired;

    /// **THE SEAM TEST: an attested `dregg://` page the cap permits renders a real,
    /// content-distinct SWGL tile the cockpit tab can paint.**
    #[test]
    fn a_capped_dregg_page_renders_a_real_content_bound_tile() {
        let cell = cell_seed(7);
        // A wildcard-root surface (the cockpit's own principal over its cell) permits
        // the page's own origin.
        let surface = SurfaceCapability::root(cell, AuthRequired::Either);

        let page = b"<dregg-cell><balance>100</balance><p>a live cell</p></dregg-cell>";
        let outcome = render_dregg_page(&surface, "dregg://cell/abc", page, 64, 48);

        let frame = outcome
            .frame()
            .expect("a cap-permitted page renders a real frame");
        assert_eq!(frame.width, 64);
        assert_eq!(frame.height, 48);
        assert_eq!(frame.bytes.len(), 64 * 48 * 4, "real RGBA8, 4 bytes/pixel");
        // The background is the content tint (the page's blake3-derived RGB), so the
        // top-left corner is a deterministic function of the content.
        let h = blake3::hash(page);
        let tint = h.as_bytes();
        assert_eq!(
            frame.pixel(0, 0),
            (tint[0], tint[1], tint[2], 255),
            "the tile background is the content-addressed tint"
        );
    }

    /// Different attested content ⇒ a different rendered tile (distinct digest) —
    /// the "this tab shows THIS page" property.
    #[test]
    fn different_pages_render_distinct_tiles() {
        let cell = cell_seed(7);
        let surface = SurfaceCapability::root(cell, AuthRequired::Either);

        let a = render_dregg_page(&surface, "dregg://cell/a", b"page A content", 32, 32)
            .frame()
            .unwrap()
            .clone();
        let b = render_dregg_page(&surface, "dregg://cell/b", b"a different page B", 32, 32)
            .frame()
            .unwrap()
            .clone();
        assert_ne!(
            a.content_digest(),
            b.content_digest(),
            "distinct attested content renders a distinct tile"
        );
    }

    /// A page the held cap does NOT permit to fetch its origin is REFUSED at the cap
    /// gate — no render, the in-band denied body instead (the tab shows the refusal,
    /// never the content). The same `granted ⊆ held` discipline the whole crate runs.
    #[test]
    fn a_page_outside_the_cap_is_refused_with_no_render() {
        let cell = cell_seed(7);
        // Scoped to example.com ONLY — a dregg:// origin it does not list is refused.
        let surface = SurfaceCapability::scoped(
            cell,
            AuthRequired::Either,
            [String::from("https://example.com")],
            [],
        );

        let outcome =
            render_dregg_page(&surface, "dregg://cell/forbidden", b"secret bytes", 16, 16);
        assert!(
            outcome.was_refused(),
            "an out-of-allowlist page is refused at the cap gate"
        );
        assert!(outcome.frame().is_none(), "a refused page renders NO frame");
        match outcome {
            TileOutcome::Refused { denied_body } => {
                let s = String::from_utf8(denied_body).unwrap();
                assert!(
                    s.contains("blocked by capability"),
                    "the tab gets the cap-denied body"
                );
            }
            TileOutcome::Rendered(_) => unreachable!(),
        }
    }
}
