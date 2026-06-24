//! The real-`WebView` path (`SERVO-ON-SEL4.md §4 Stage A`, steps 3-4) — OPT-IN
//! behind the `libservo` feature, because it pulls `servo` → `script` → `mozjs`
//! (the multi-GB SpiderMonkey C++ build), the known-hard, known-walked long pole.
//!
//! ## What this module does (the wiring is WRITTEN against the genuine API)
//!
//! 1. [`ServoSwglContext`] implements servo's GENUINE
//!    `paint_api::rendering_context::RenderingContext` trait (not the standalone
//!    mirror) over a [`SwglRenderingContext`], so a real `WebView` accepts our SWGL
//!    context as its render target — the §1.5 "write a small new `RenderingContext`
//!    impl" that replaces the surfman → Mesa path.
//! 2. [`CapGate`] is the real `WebViewDelegate` — Servo calls *out* to it at every
//!    authority point and it forwards `load_web_resource` / `request_navigation` to
//!    the genuine `CapGatedDelegate` (`granted ⊆ held`), so the held
//!    [`SurfaceCapability`] mediates the engine exactly as it mediates the
//!    `MockSurface`.
//! 3. [`render_url_to_frame`] builds a real `Servo` (`ServoBuilder`) + `WebView`
//!    (`WebViewBuilder` pointed at the SWGL context, the `CapGate` as delegate),
//!    loads a URL, spins `spin_event_loop` until the page is loaded+painted, calls
//!    `WebView::paint`, and reads the frame back via `RenderingContext::read_to_image`
//!    as an [`RgbaFrame`] — the SAME type `present_frame` carries to the compositor.
//!
//! This is API-correct against the published trait + the `winit_minimal` upstream
//! embed example, and it RUNS end-to-end: a real Servo `WebView` lays out + paints a
//! `data:` page into the SWGL framebuffer, captured to a PNG and carried through the
//! genuine compositor-PD gate (the test
//! [`tests::first_real_render_data_page_through_the_compositor_gate`]). Two things made
//! the real engine paint into our SWGL context: [`ServoSwglContext::connection`] hands
//! servo-paint a real surfman software `Connection` (its WebGL bookkeeping `.expect()`s
//! one — see that method), and the vendored `servo-paint` fork
//! (`servo-render/vendor/servo-paint/`, `[patch.crates-io]`) sets
//! `WebRenderOptions { clear_caches_with_quads: false }` so WebRender's cache clear does
//! not issue a depth-`GL_ALWAYS` quad SWGL's `DepthFunc` asserts on.
//!
//! ## The one real trait-shape divergence (HONEST)
//!
//! Servo's real trait (verified against `servo-paint-api`'s `rendering_context.rs`;
//! the version the codebase pins as `0.1.0-rc2` resolves to the published `0.1.0`)
//! requires BOTH:
//!   - `gleam_gl_api(&self) -> Rc<dyn gleam::gl::Gl>`  ← SWGL provides this (it
//!     `impl Gl for swgl::Context`); this is the WebRender render path + the
//!     `read_to_image` (`read_pixels`) pixel path.
//!   - `glow_gl_api(&self) -> Arc<glow::Context>`  ← SWGL does **NOT** implement
//!     `glow`. This is used by the OFFSCREEN-context blit path
//!     (`OffscreenRenderingContext::blit_framebuffer`), NOT by the page→buffer
//!     render or the pixel readback. For a DRAW-compositor SWGL context that owns
//!     the whole default framebuffer we do not take the offscreen blit path. It is
//!     nonetheless CLOSED honestly via option (a): a real
//!     `glow::Context::from_loader_function` over SWGL's statically-linked bare GL
//!     symbols (`swgl_proc_loader` strips glow's `gl` prefix and `dlsym`s the bare
//!     symbol from the process image, e.g. `glClear` → SWGL's `Clear`). No panicking
//!     stub remains.
//!
//! ## Build status
//!
//! This module compiles ONLY under `--features libservo`, which pulls the full
//! servo dependency tree (941 crates incl. mozjs/SpiderMonkey, the multi-GB C++
//! build). That whole tree **resolves and builds offline from the crates.io
//! mirror** — the wall is wall-clock on the `mozjs`/`script` compile, not a missing
//! dependency. The `swgl-standalone` default proves the render path (real RGBA8 out
//! of SWGL) WITHOUT this elephant, and is green today.

#![cfg(feature = "libservo")]

use std::rc::Rc;
use std::sync::Arc;

// NB: the crate is `servo-paint-api` but its `[lib] name` is `paint_api` (verified
// via `cargo metadata`), so it is imported as `paint_api`, not `servo_paint_api`.
use dpi::PhysicalSize;
use image::RgbaImage;
use paint_api::rendering_context::RenderingContext as ServoRenderingContext;
use webrender_api::units::DeviceIntRect;

use crate::swgl_context::SwglRenderingContext;

/// A real-`RenderingContext`-trait adapter over [`SwglRenderingContext`]. THIS is
/// the type a real `WebViewBuilder` accepts (`builder(rendering_context: Rc<dyn
/// RenderingContext>)`), making the SWGL software rasterizer the WebView's render
/// target — no GPU, no EGL, no surfman.
pub struct ServoSwglContext {
    inner: SwglRenderingContext,
}

impl ServoSwglContext {
    /// Wrap a SWGL context for use as a real servo `RenderingContext`.
    pub fn new(width: u32, height: u32) -> Self {
        ServoSwglContext {
            inner: SwglRenderingContext::new(width, height),
        }
    }

    /// The inner SWGL context (for direct frame readback into the compositor seam).
    pub fn inner(&self) -> &SwglRenderingContext {
        &self.inner
    }
}

impl ServoRenderingContext for ServoSwglContext {
    fn prepare_for_rendering(&self) {
        use crate::swgl_context::RenderingContext as _;
        self.inner.prepare_for_rendering();
    }

    fn read_to_image(&self, source_rectangle: DeviceIntRect) -> Option<RgbaImage> {
        use crate::swgl_context::{ReadRect, RenderingContext as _};
        let rect = ReadRect {
            x: source_rectangle.min.x,
            y: source_rectangle.min.y,
            width: source_rectangle.width(),
            height: source_rectangle.height(),
        };
        let frame = self.inner.read_to_image(rect)?;
        RgbaImage::from_raw(frame.width, frame.height, frame.bytes)
    }

    fn size(&self) -> PhysicalSize<u32> {
        use crate::swgl_context::RenderingContext as _;
        let (w, h) = self.inner.size();
        PhysicalSize::new(w, h)
    }

    fn resize(&self, size: PhysicalSize<u32>) {
        use crate::swgl_context::RenderingContext as _;
        self.inner.resize(size.width, size.height);
    }

    fn present(&self) {
        use crate::swgl_context::RenderingContext as _;
        self.inner.present();
    }

    fn make_current(&self) -> Result<(), paint_api::rendering_context::Error> {
        use crate::swgl_context::RenderingContext as _;
        self.inner.make_current();
        Ok(())
    }

    fn gleam_gl_api(&self) -> Rc<dyn gleam::gl::Gl> {
        use crate::swgl_context::RenderingContext as _;
        self.inner.gleam_gl_api()
    }

    /// **THE SURFMAN-CEILING BREAK.** servo-paint's `register_rendering_context`
    /// (`paint.rs:236-238`) UNCONDITIONALLY does
    /// `rendering_context.connection().expect("Failed to get connection")` then
    /// `connection.create_adapter()`, storing the pair in a per-painter
    /// `PainterSurfmanDetails { connection, adapter }` map keyed by `PainterId`. That
    /// map is the WebGL-canvas plumbing (`SwapChains<WebGLContextId, surfman::Device>`):
    /// it is touched ONLY when a page allocates a WebGL canvas surface. The
    /// trait-default `connection() -> None` therefore panics at registration BEFORE
    /// any page paints, even for a page that draws no WebGL.
    ///
    /// We hand back a REAL surfman software `Connection`. `Connection::new()` opens the
    /// default display connection (CGL on macOS / EGL+gbm or X11 on Linux) — a
    /// *connection handle*, NOT a window or a GPU surface; no framebuffer is allocated
    /// here. servo-paint's `create_adapter()` then succeeds against it. SWGL still does
    /// ALL the page rasterization through `gleam_gl_api()` (the `swgl::Context` IS the
    /// `gleam::gl::Gl` WebRender's `Renderer` draws into our `Vec<u8>`); the surfman
    /// connection's device is only ever instantiated for a WebGL canvas, which our
    /// pages do not contain. This is the genuine
    /// `RenderingContext::connection()` of servo's own `SoftwareRenderingContext`
    /// (`Connection::new()` — `rendering_context.rs:312`), minus the surface bind we
    /// do not need because SWGL owns the default framebuffer.
    ///
    /// Returns `None` only if the host has no display connection at all (a truly
    /// headless box with no CGL/EGL) — in which case the page cannot paint and the
    /// `.expect()` would (correctly) report the absent display, not a SWGL gap.
    fn connection(&self) -> Option<surfman::Connection> {
        surfman::Connection::new().ok()
    }

    fn glow_gl_api(&self) -> Arc<glow::Context> {
        // Follow-up (a), CLOSED: a real `glow::Context` over SWGL's GL entry points.
        //
        // SWGL exports its GL functions as BARE C symbols statically linked into
        // the final binary (`swgl/src/gl.cc`'s `extern "C" { void Clear(..); void
        // ActiveTexture(..); const char* GetString(..); .. }` — the SAME symbols
        // `swgl_fns.rs`'s `extern "C"` block binds, e.g. `ActiveTexture`,
        // `BindTexture`, `ReadPixels`, `GetString`). It exposes NO surfman-style
        // `get_proc_address`, so we build the glow loader ourselves: glow asks for
        // the GL-prefixed name (`glActiveTexture`); we strip the `gl` prefix and
        // resolve the bare symbol from the current process image
        // (`dlsym(RTLD_DEFAULT, ..)`) — exactly the symbols SWGL linked in.
        //
        // The context must be current for `from_loader_function`'s immediate
        // `GetString(GL_VERSION)` probe (and any subsequent draw) to read SWGL's
        // global `ctx`; SWGL's current context is a process-global (`gl.cc:898`),
        // so we make ours current first.
        use crate::swgl_context::RenderingContext as _;
        self.inner.make_current();
        let ctx = unsafe { glow::Context::from_loader_function(swgl_proc_loader) };
        Arc::new(ctx)
    }
}

/// Resolve a GL function `glow` requests against SWGL's statically-linked bare C
/// symbols. glow asks for the canonical GL name (e.g. `glClear`, `glReadPixels`,
/// `glGetString`); SWGL exports them WITHOUT the `gl` prefix (`Clear`,
/// `ReadPixels`, `GetString` — `swgl/src/gl.cc`'s `extern "C"` blocks), so we strip
/// a leading `gl` and `dlsym` the bare symbol from the running image
/// (`RTLD_DEFAULT`), into which SWGL is linked under the `libservo` feature.
/// Returns null for a name SWGL does not export (glow tolerates a null entry —
/// that function is simply unavailable, the same as an unsupported extension).
fn swgl_proc_loader(name: &str) -> *const std::os::raw::c_void {
    // `RTLD_DEFAULT` (0 on macOS, the special handle on glibc) — search the whole
    // process image, where SWGL's bare GL symbols live once `libservo` links it.
    #[cfg(target_os = "macos")]
    const RTLD_DEFAULT: *mut std::os::raw::c_void =
        std::ptr::null_mut::<std::os::raw::c_void>().wrapping_offset(-2);
    #[cfg(not(target_os = "macos"))]
    const RTLD_DEFAULT: *mut std::os::raw::c_void = std::ptr::null_mut();

    extern "C" {
        fn dlsym(
            handle: *mut std::os::raw::c_void,
            symbol: *const std::os::raw::c_char,
        ) -> *mut std::os::raw::c_void;
    }

    // SWGL's symbols are the GL name minus the `gl` prefix (`glClear` → `Clear`).
    let bare = name.strip_prefix("gl").unwrap_or(name);
    let Ok(c_name) = std::ffi::CString::new(bare) else {
        return std::ptr::null();
    };
    unsafe { dlsym(RTLD_DEFAULT, c_name.as_ptr()) as *const std::os::raw::c_void }
}

// ─────────────────────────────────────────────────────────────────────────────
// The real `WebView` embed — Stage-A steps 3-4 wired against the GENUINE servo
// API (`servo 0.1.x`, the `winit_minimal` example is the upstream template). This
// is the actual `ServoBuilder → WebViewBuilder → load → spin-until-painted →
// read_to_image` flow, NOT a stand-in. It is gated `#[cfg(feature = "libservo")]`,
// so it compiles only once the engine (mozjs/SpiderMonkey, the long pole) links;
// the code itself is complete and API-correct against the published trait.
// ─────────────────────────────────────────────────────────────────────────────

use std::cell::Cell;

use servo::{
    EventLoopWaker, InputEvent, Key, KeyState, KeyboardEvent, LoadStatus, MouseButton,
    MouseButtonAction, MouseButtonEvent, Scroll, ServoBuilder, WebResourceLoad, WebResourceResponse,
    WebView, WebViewBuilder, WebViewDelegate, WebViewPoint, WebViewVector, WheelDelta, WheelEvent,
    WheelMode,
};
use url::Url;
use webrender_api::units::{DevicePoint, DeviceVector2D};

use starbridge_web_surface::{
    CapGatedDelegate, NavigationDecision, ResourceDecision, SurfaceCapability, WebSurfaceDelegate,
};

use dregg_captp::netlayer::{InProcessFabric, InProcessNetlayer};

use crate::netcap_connector::{block_on, ConnectOutcome, NetcapConnector};
use crate::netcap_http::{CapGatedHttpHandler, SharedHttpHandler};
use crate::swgl_context::RgbaFrame;

use servo::protocol_handler::ProtocolRegistry;

/// **The real `WebViewDelegate` that IS the cap gate** (the `// LIBSERVO SEAM` made
/// good). Servo calls *out* to this at every authority point; each callback
/// discharges the held [`SurfaceCapability`] through the GENUINE
/// [`CapGatedDelegate`] (the same `granted ⊆ held` `is_attenuation` gate the
/// firmament runs), so a fetch/navigation the cap does not permit is refused *at
/// the callback*, before the engine acts — exactly the discipline
/// `starbridge-web-surface` already proves on the `MockSurface`. The only thing
/// new here over the mock is that the callbacks are the *real* libservo ones.
///
/// It also wakes the embedder loop on a new frame ([`Self::frame_ready`]), the
/// signal the headless [`render_url_to_frame`] spins on.
struct CapGate {
    /// The held authority for this `WebView` (the c-list entry the delegate
    /// discharges) — carried by the surface, never by the untrusted page.
    surface: SurfaceCapability,
    /// The genuine cap-enforcing gate the callbacks forward to.
    gate: CapGatedDelegate,
    /// **THE NET-CAP CONNECTOR** — the audited transport leg. Every fetch the gate
    /// admits is routed through this connector's [`NetcapConnector::connect`], so an
    /// origin's *reachability* is the netlayer's to grant (gated by the held cap), not
    /// an ambient OS socket's. A cap-denied origin is refused at the connector before
    /// any `dial`; a cap-admitted origin's connection IS a real audited
    /// [`dregg_captp::netlayer::NetSession`]. (This delegate binds the *connect
    /// decision*; the http(s) BYTE socket is now owned by the cap-gated
    /// [`crate::netcap_http::CapGatedHttpHandler`] the vendored `servo-net` fork lets
    /// us register — the forbidden-scheme ceiling is broken, see that module.)
    connector: NetcapConnector<InProcessNetlayer>,
    /// The net-cap outcomes this gate produced, newest last — the audit/status trail
    /// the headless render surfaces ([`render_url_to_frame`] returns the last one).
    net_outcomes: std::cell::RefCell<Vec<ConnectOutcome>>,
    /// Set when servo reports a new frame is painted — the headless render loop
    /// reads this to know a frame is ready to read back.
    frame_ready: Cell<bool>,
    /// Set when the load reaches [`LoadStatus::Complete`] — the headless loop's
    /// terminating condition (paint the *finished* page, not a partial one).
    load_complete: Cell<bool>,
}

impl CapGate {
    /// **THE NET-CAP SOCKET DECISION** for `origin`, recorded into the audit trail.
    /// Routes the connect decision through the audited netlayer connector: a cap-denied
    /// origin returns [`ConnectOutcome::RefusedByCap`] (no dial happened); a cap-admitted
    /// origin opens a real netlayer session. Pulled out of [`load_web_resource`] so it is
    /// testable without constructing a servo `WebResourceLoad`.
    fn decide_net_cap(&self, origin: &str) -> ConnectOutcome {
        let outcome = block_on(self.connector.connect(&self.surface, origin));
        self.net_outcomes.borrow_mut().push(outcome.clone());
        outcome
    }
}

impl WebViewDelegate for CapGate {
    /// libservo `load_web_resource` — the fetch/subresource chokepoint. Forward to
    /// the cap gate: on [`ResourceDecision::Intercept`] (cap-denied) we intercept
    /// the load with the cap-denied body (the page sees the refusal bytes, never
    /// the resource); on [`ResourceDecision::Continue`] we let it proceed.
    fn load_web_resource(&self, _webview: WebView, load: WebResourceLoad) {
        let origin = load.request().url.origin().ascii_serialization();
        // THE NET-CAP SOCKET BIND: route the connect decision through the audited
        // netlayer. A cap-denied origin is refused AT the connector (no dial, no
        // socket); a cap-admitted origin opens a real netlayer session for the origin.
        // The outcome is recorded for the status line + decides whether we let servo's
        // bytes-leg proceed (Dialed) or intercept it with the refusal body (Refused).
        let outcome = self.decide_net_cap(&origin);
        match outcome {
            ConnectOutcome::RefusedByCap { .. } => {
                // The held cap does not authorize this origin — the netlayer was never
                // dialed. Hand the page the cap-denied body; servo's socket never opens.
                let body = format!("dregg: blocked by net-cap — {origin} not authorized by the held SurfaceCapability (Netlayer::dial never called)").into_bytes();
                let url = load.request().url.clone();
                let mut intercepted = load.intercept(WebResourceResponse::new(url));
                intercepted.send_body_data(body);
                intercepted.finish();
                return;
            }
            ConnectOutcome::RefusedByTransport { reason, .. } => {
                // The cap authorized it, but the audited netlayer could not reach the
                // peer. The page gets the transport refusal — NOT a silent ambient
                // fallback to a different socket.
                let body = format!("dregg: net-cap transport could not reach {origin} ({reason})")
                    .into_bytes();
                let url = load.request().url.clone();
                let mut intercepted = load.intercept(WebResourceResponse::new(url));
                intercepted.send_body_data(body);
                intercepted.finish();
                return;
            }
            ConnectOutcome::Dialed { .. } => { /* audited session opened — fall through to the gate */
            }
        }
        match self.gate.load_web_resource(&self.surface, &origin) {
            ResourceDecision::Continue => { /* not intercepted — proceeds to net */ }
            ResourceDecision::Intercept { body, .. } => {
                // Hand the page the cap-denied body instead of the resource. The
                // builder shape (`WebResourceResponse::new(url)`) + `intercept` →
                // `send_body_data` → `finish` is servo's own canonical interception
                // pattern (verified against its `webview_delegate.rs` test).
                let url = load.request().url.clone();
                let mut intercepted = load.intercept(WebResourceResponse::new(url));
                intercepted.send_body_data(body);
                intercepted.finish();
            }
        }
    }

    /// libservo `request_navigation` — accepted by default, so the cap gate must
    /// affirmatively decide. Forward to the gate's navigate allowlist:
    /// [`NavigationDecision::Allow`] → `allow()`, else `deny()`.
    fn request_navigation(&self, _webview: WebView, navigation_request: servo::NavigationRequest) {
        // `NavigationRequest::url` is a public FIELD in the published `servo 0.1.1`
        // (not the `url()` accessor the pre-1.0 docs implied).
        let origin = navigation_request.url.origin().ascii_serialization();
        match self.gate.allow_navigation(&self.surface, &origin) {
            NavigationDecision::Allow => navigation_request.allow(),
            NavigationDecision::Deny { .. } => navigation_request.deny(),
        }
    }

    /// libservo `notify_new_frame_ready` — servo painted a new frame into the
    /// rendering context's back buffer. Flag it so the headless loop reads back.
    fn notify_new_frame_ready(&self, _webview: WebView) {
        self.frame_ready.set(true);
    }

    /// libservo `notify_load_status_changed` — flag [`LoadStatus::Complete`] so the
    /// headless loop knows the page is fully loaded (ready for a final paint).
    fn notify_load_status_changed(&self, _webview: WebView, status: LoadStatus) {
        // `matches!` (not `==`) so this is robust whether or not `LoadStatus` derives
        // `PartialEq` — it is a plain variant discriminant check either way.
        if matches!(status, LoadStatus::Complete) {
            self.load_complete.set(true);
        }
    }
}

/// A no-op [`EventLoopWaker`] — the headless render driver pumps
/// [`Servo::spin_event_loop`] itself in a bounded loop (no external event loop to
/// wake). A real windowed embedder wakes its winit proxy here (cf. `winit_minimal`).
#[derive(Clone)]
struct HeadlessWaker;
impl EventLoopWaker for HeadlessWaker {
    fn clone_box(&self) -> Box<dyn EventLoopWaker> {
        Box::new(self.clone())
    }
    fn wake(&self) {}
}

/// **THE STAGE-A STEP-3+4 PAYOFF: render a real web page to an `RgbaFrame` through
/// the SWGL context, behind the cap gate.**
///
/// Build a real `Servo` engine, point a real `WebView` at our [`ServoSwglContext`]
/// (the SWGL software rasterizer — no GPU, no EGL, no surfman), install the
/// [`CapGate`] `WebViewDelegate` (so the held `surface` cap mediates every fetch /
/// navigation), load `url`, spin the event loop until the page is loaded and
/// painted, then read the rendered RGBA8 back via the genuine
/// `RenderingContext::read_to_image`. The returned [`RgbaFrame`] is the SAME type
/// [`crate::present_frame`] carries to the compositor-PD's `present()` gate — so the
/// real page's pixels flow straight into the unchanged T1/T2/T3 gate, closing F3
/// with genuine page content (not the clear-to-color stand-in).
///
/// `max_spins` bounds the headless pump (servo is multi-threaded; the page load +
/// layout + paint complete asynchronously across its actor threads). Returns `None`
/// if no frame was produced within the bound (e.g. the page never painted).
///
/// This is the function the `swgl-standalone` `fetch_render_present` pipeline's
/// `render_color` stand-in is replaced BY when `libservo` is on: same cap gate in
/// front, same compositor gate behind, real pixels in between.
pub fn render_url_to_frame(
    url: &str,
    surface: SurfaceCapability,
    width: u32,
    height: u32,
    max_spins: usize,
) -> Option<RgbaFrame> {
    render_url_to_frame_netcap(url, surface, width, height, max_spins).0
}

/// Build the net-cap [`CapGate`] for `surface`: a connector over a fresh in-process
/// netlayer fabric in which `surface`'s authorized origins' peers have JOINED (so a
/// cap-admitted fetch dials a reachable peer through the audited netlayer; an
/// unauthorized origin is refused at the connector before any dial). The fabric is
/// owned by the gate for the render's lifetime — a per-render audited transport leg.
///
/// `seed_origins` are the origins to pre-join as reachable peers (typically the
/// surface's `fetch_allow` allowlist + the navigated origin); a wildcard surface
/// joins the navigated origin so its top-level fetch is reachable.
fn build_cap_gate(surface: SurfaceCapability, seed_origins: &[String]) -> Rc<CapGate> {
    use crate::netcap_connector::origin_to_peer;
    let fabric = InProcessFabric::new();
    // Our own node (the page's dialer identity) — a fixed id in the keyspace.
    let me = fabric.join([0x5e; 32]);
    // Join the reachable peers: the origins the cap authorizes (so a cap-admitted
    // dial reaches a real peer). An origin the cap does NOT authorize is refused at
    // the connector regardless of whether its peer joined.
    for o in seed_origins {
        let _ = fabric.join(origin_to_peer(o));
    }
    Rc::new(CapGate {
        surface,
        gate: CapGatedDelegate::new(),
        connector: NetcapConnector::new(me),
        net_outcomes: std::cell::RefCell::new(Vec::new()),
        frame_ready: Cell::new(false),
        load_complete: Cell::new(false),
    })
}

/// Render a page AND report the net-cap outcome — the [`render_url_to_frame`] variant
/// that surfaces whether the navigation's fetches dialed through the audited netlayer,
/// were refused by the cap at the socket, or were unreachable on the transport. The
/// returned [`ConnectOutcome`] is the LAST one the gate produced (the most recent
/// fetch's fate); `None` if the engine never issued a network load (e.g. a `data:`
/// page, which needs no socket).
pub fn render_url_to_frame_netcap(
    url: &str,
    surface: SurfaceCapability,
    width: u32,
    height: u32,
    max_spins: usize,
) -> (Option<RgbaFrame>, Option<ConnectOutcome>) {
    // The real engine. Headless: we drive `spin_event_loop` ourselves. Servo's
    // process-global options/prefs (`servo_config::opts`) are a `OnceCell` set ONCE
    // per process by `ServoBuilder::build`, so at most one `Servo` exists per process;
    // [`render_url_on_servo`] renders additional pages on this same engine.
    let servo = ServoBuilder::default()
        .event_loop_waker(Box::new(HeadlessWaker))
        .build();
    render_url_on_servo(&servo, url, surface, width, height, max_spins)
}

/// **THE HTTP(S) PAYOFF: rasterize a REAL `http://` page through the cap-gated byte
/// socket.**
///
/// This is the function the forbidden-scheme fork makes possible. It:
///
/// 1. builds a [`CapGatedHttpHandler`] for `surface` (the cap discharged at the byte
///    socket) and registers it in a [`ProtocolRegistry`] for `http` AND `https` —
///    now permitted, because the vendored `servo-net` fork removed http/https from
///    `FORBIDDEN_SCHEMES` and makes `scheme_fetch` consult an embedder handler first;
/// 2. builds a real `Servo` with that registry (`ServoBuilder::protocol_registry`),
///    so the engine routes http(s) loads through OUR handler instead of its hyper;
/// 3. renders `url` through [`render_url_on_servo`] into the SWGL framebuffer — the
///    handler runs the cap gate at the socket, fetches the bytes over a real
///    cap-gated TCP socket, hands them to servo, servo lays them out, SWGL rasters.
///
/// Returns the rendered [`RgbaFrame`], the handler (for audit readback — which
/// origins were dialed/refused, what bytes were fetched), and the navigation's last
/// net-cap [`ConnectOutcome`].
/// A real `Servo` engine whose `http`/`https` loads are routed through ONE
/// cap-gated [`CapGatedHttpHandler`] (registered in the engine's `ProtocolRegistry`,
/// permitted by the `servo-net` fork). Because `servo_config::opts` is a
/// process-wide `OnceCell`, at most one engine exists per process; this holds that
/// engine + its one handler so SEVERAL pages (different surfaces) render on it via
/// [`Self::render`], each [`CapGatedHttpHandler::reconfigure`]-ing the held cap.
pub struct CapGatedHttpEngine {
    servo: servo::Servo,
    handler: std::sync::Arc<CapGatedHttpHandler>,
}

impl CapGatedHttpEngine {
    /// Build the one-per-process engine with the cap-gated http handler registered
    /// for http AND https (both permitted by the fork). The handler starts pointed at
    /// `initial_surface`/`initial_seeds`; [`Self::render`] re-points it per page.
    pub fn new(initial_surface: SurfaceCapability, initial_seeds: &[String]) -> Self {
        let handler = std::sync::Arc::new(CapGatedHttpHandler::new(initial_surface, initial_seeds));
        let shared = SharedHttpHandler(handler.clone());

        // Register it for BOTH http and https (the fork permits both). servo's
        // `scheme_fetch` consults this handler first for those schemes.
        let mut registry = ProtocolRegistry::default();
        registry.register("http", shared.clone()).expect(
            "the servo-net fork permits registering an http handler (FORBIDDEN_SCHEMES loosened)",
        );
        registry.register("https", shared).expect(
            "the servo-net fork permits registering an https handler (FORBIDDEN_SCHEMES loosened)",
        );

        let servo = ServoBuilder::default()
            .event_loop_waker(Box::new(HeadlessWaker))
            .protocol_registry(registry)
            .build();
        CapGatedHttpEngine { servo, handler }
    }

    /// The shared cap-gated http handler (for audit readback: outcomes, last fetch).
    pub fn handler(&self) -> &std::sync::Arc<CapGatedHttpHandler> {
        &self.handler
    }

    /// Re-point the handler at `surface`/`seed_origins`, then render `url` on this
    /// engine. The handler runs the cap gate at the byte socket; a cap-admitted
    /// origin's bytes are fetched over a real cap-gated TCP socket, laid out by servo,
    /// rasterized by SWGL. Returns the frame + the delegate's last net-cap outcome
    /// (the handler's own outcomes are read via [`Self::handler`]).
    pub fn render(
        &self,
        url: &str,
        surface: SurfaceCapability,
        seed_origins: &[String],
        width: u32,
        height: u32,
        max_spins: usize,
    ) -> (Option<RgbaFrame>, Option<ConnectOutcome>) {
        self.handler.reconfigure(surface.clone(), seed_origins);
        render_url_on_servo(&self.servo, url, surface, width, height, max_spins)
    }
}

/// **THE HTTP(S) PAYOFF (single-shot).** Build a fresh [`CapGatedHttpEngine`] and
/// render ONE http(s) page through the cap gate. Convenient when the process renders
/// exactly one page; to render several (different surfaces), build ONE
/// [`CapGatedHttpEngine`] and call [`CapGatedHttpEngine::render`] per page (servo's
/// opts is a process `OnceCell`, so only one engine may exist per process).
pub fn render_http_url_to_frame(
    url: &str,
    surface: SurfaceCapability,
    seed_origins: &[String],
    width: u32,
    height: u32,
    max_spins: usize,
) -> (
    Option<RgbaFrame>,
    std::sync::Arc<CapGatedHttpHandler>,
    Option<ConnectOutcome>,
) {
    let engine = CapGatedHttpEngine::new(surface.clone(), seed_origins);
    let (frame, outcome) = engine.render(url, surface, seed_origins, width, height, max_spins);
    (frame, engine.handler.clone(), outcome)
}

/// Render `url` to a frame on an ALREADY-BUILT [`Servo`] engine — the per-page leg of
/// [`render_url_to_frame_netcap`], factored out so several pages can be rendered on
/// ONE engine (Servo's `servo_config::opts` is a process-global `OnceCell`, so the
/// engine is built at most once per process; a test that wants both a box page and a
/// text page drives them through the same `servo`).
pub fn render_url_on_servo(
    servo: &servo::Servo,
    url: &str,
    surface: SurfaceCapability,
    width: u32,
    height: u32,
    max_spins: usize,
) -> (Option<RgbaFrame>, Option<ConnectOutcome>) {
    use crate::swgl_context::RenderingContext as _;

    let Ok(parsed) = Url::parse(url) else {
        return (None, None);
    };

    // The SWGL rendering context — our software rasterizer as a real servo
    // `RenderingContext` (`Rc<dyn RenderingContext>` is what `WebViewBuilder` takes).
    let rendering_context = Rc::new(ServoSwglContext::new(width, height));
    let _ = ServoRenderingContext::make_current(&*rendering_context);

    // The delegate IS the cap gate — every fetch/navigation discharges `surface` AND
    // routes the connect decision through the audited netlayer connector. Seed the
    // navigated origin (+ the surface's fetch allowlist) as reachable peers so a
    // cap-admitted top-level fetch dials a real peer.
    let mut seed: Vec<String> = vec![parsed.origin().ascii_serialization()];
    if let Some(allow) = surface_fetch_allow(&surface) {
        seed.extend(allow);
    }
    let delegate = build_cap_gate(surface, &seed);

    let webview = WebViewBuilder::new(servo, rendering_context.clone())
        .url(parsed)
        .delegate(delegate.clone())
        .build();

    // Pump servo's actor threads until the page is loaded AND a frame is ready,
    // bounded so a non-painting page cannot hang the caller. Servo is multi-threaded
    // (constellation / script / layout / paint run on their OWN threads); a tight
    // `spin_event_loop` busy-loop completes in microseconds and out-runs the page
    // load+layout+paint that is happening asynchronously on those threads. The
    // upstream `winit_minimal` example is naturally paced by waiting on OS events
    // between spins. Here, headless, we pace it ourselves with a short yield so the
    // worker threads make progress between embedder spins.
    let mut spins = 0;
    while spins < max_spins {
        servo.spin_event_loop();
        if delegate.load_complete.get() && delegate.frame_ready.get() {
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(1));
        spins += 1;
    }

    // Give the freshly-loaded page a few extra paced spins so its WebRender scene
    // (display list → built frame) is fully ready before the final embedder paint.
    for _ in 0..16 {
        servo.spin_event_loop();
        std::thread::sleep(std::time::Duration::from_millis(1));
    }

    // Ask the WebView to paint the (now-loaded) page into the SWGL back buffer,
    // then read the RGBA8 out via the genuine trait — the same `read_pixels` path
    // the standalone build proves. `read_to_image` reads the back buffer even
    // before `present`, so the rendered page is available here.
    webview.paint();
    let (w, h) = rendering_context.inner().size();
    let rect = crate::swgl_context::ReadRect::whole(w, h);
    let frame = rendering_context.inner().read_to_image(rect);
    let last_outcome = delegate.net_outcomes.borrow().last().cloned();
    (frame, last_outcome)
}

// ─────────────────────────────────────────────────────────────────────────────
// THE INTERACTIVE SPIKE — input → re-render → fresh tile. This is the move from a
// STATIC snapshot to a LIVE embedded WebView: the SAME `ServoSwglContext` +
// `CapGate` the headless render uses, but driven with an INPUT EVENT between two
// paints so the second frame reflects the input (e.g. a scrolled page). The
// embedder-side loop is exactly the upstream `winit_minimal` pattern
// (`notify_input_event`/`notify_scroll_event` → `spin_event_loop`* → `paint`),
// only headless and bounded.
// ─────────────────────────────────────────────────────────────────────────────

/// An input event to deliver to a live [`WebView`] between two paints — the spike's
/// "feed input in" half. These map 1:1 onto servo's [`InputEvent`] / `Scroll`
/// vocabulary (`MouseButton`, `MouseMove`, `Wheel`, and the higher-level scroll),
/// so an embedder (the cockpit web-shell, a winit window, the seL4 input PD) lowers
/// its native events to these and the same `apply_input` drives the engine.
#[derive(Clone, Copy, Debug)]
pub enum WebInput {
    /// A wheel/trackpad scroll by `(dx, dy)` CSS pixels at viewport `(x, y)`.
    /// Positive `dy` reveals content below (servo's `WheelDelta` convention is the
    /// opposite sign, handled inside [`apply_input`]).
    Scroll { x: f32, y: f32, dx: f32, dy: f32 },
    /// A left-button press-and-release ("click") at viewport `(x, y)`.
    Click { x: f32, y: f32 },
    /// A pointer move to viewport `(x, y)` (drives `:hover`, cursor).
    MouseMove { x: f32, y: f32 },
    /// A typed character key (a `keydown`+`keyup` for the character) — drives text
    /// input / key handlers. `char`-typed (not a `String`) so [`WebInput`] stays
    /// `Copy`; an embedder lowers each typed grapheme to one of these.
    KeyChar { ch: char },
}

/// Deliver one [`WebInput`] to a live `webview`. Mouse/wheel events go through
/// `notify_input_event` (which routes point-bearing events to the paint thread for
/// hit-testing first); the high-level page scroll uses `notify_scroll_event`. The
/// caller then spins + repaints to obtain the post-input frame
/// (see [`render_url_then_input_on_servo`]).
pub fn apply_input(webview: &WebView, input: WebInput) {
    match input {
        WebInput::Scroll { x, y, dx, dy } => {
            let point = WebViewPoint::Device(DevicePoint::new(x, y));
            // A wheel event (what a trackpad/mouse wheel produces) AND a high-level
            // scroll, mirroring how an embedder delivers a scroll gesture. Servo's
            // `WheelDelta.y` positive reveals content ABOVE, so negate `dy` to make
            // "scroll down `dy`px" reveal content below (the intuitive sense).
            webview.notify_input_event(InputEvent::Wheel(WheelEvent::new(
                WheelDelta {
                    x: dx as f64,
                    y: -(dy as f64),
                    z: 0.0,
                    mode: WheelMode::DeltaPixel,
                },
                point,
            )));
            // The high-level scroll the paint thread applies to the scroll tree:
            // a Device-space delta vector (positive `y` reveals content below).
            webview.notify_scroll_event(
                Scroll::Delta(WebViewVector::Device(DeviceVector2D::new(dx, dy))),
                point,
            );
        }
        WebInput::Click { x, y } => {
            let point = WebViewPoint::Device(DevicePoint::new(x, y));
            webview.notify_input_event(InputEvent::MouseButton(MouseButtonEvent::new(
                MouseButtonAction::Down,
                MouseButton::Left,
                point,
            )));
            webview.notify_input_event(InputEvent::MouseButton(MouseButtonEvent::new(
                MouseButtonAction::Up,
                MouseButton::Left,
                point,
            )));
        }
        WebInput::MouseMove { x, y } => {
            let point = WebViewPoint::Device(DevicePoint::new(x, y));
            webview.notify_input_event(InputEvent::MouseMove(servo::MouseMoveEvent::new(point)));
        }
        WebInput::KeyChar { ch } => {
            // A character key as a keydown then keyup. `Key::Character` carries the
            // typed string; servo's `from_state_and_key` fills code/location/modifiers
            // with defaults (the embedder-minimal lowering — the same `winit_minimal`
            // does for a plain character before it has a physical key code).
            let key = Key::Character(ch.to_string());
            webview.notify_input_event(InputEvent::Keyboard(KeyboardEvent::from_state_and_key(
                KeyState::Down,
                key.clone(),
            )));
            webview.notify_input_event(InputEvent::Keyboard(KeyboardEvent::from_state_and_key(
                KeyState::Up,
                key,
            )));
        }
    }
}

/// **THE INTERACTIVITY SPIKE: prove input → re-render → a DIFFERENT tile.**
///
/// Load `url` on `servo` into a fresh [`ServoSwglContext`] behind the [`CapGate`],
/// paint the loaded page (frame A), deliver `input` to the live `WebView`, pump the
/// actor threads so the input takes effect (a scroll re-lays the scroll tree, a click
/// runs script/handlers), repaint (frame B), and return BOTH frames. When `input`
/// changes what is on screen (e.g. scrolling a page taller than the viewport), the two
/// frames' `content_digest`s DIFFER — the proof that the embedded WebView is LIVE, not
/// a static snapshot.
///
/// This is the headless analogue of the upstream `winit_minimal` window loop: the only
/// difference is that a winit embedder is paced by OS redraw events, whereas here we
/// pump `spin_event_loop` ourselves between the input and the repaint.
pub fn render_url_then_input_on_servo(
    servo: &servo::Servo,
    url: &str,
    surface: SurfaceCapability,
    width: u32,
    height: u32,
    input: WebInput,
    max_spins: usize,
) -> Option<(RgbaFrame, RgbaFrame)> {
    use crate::swgl_context::RenderingContext as _;

    let parsed = Url::parse(url).ok()?;

    let rendering_context = Rc::new(ServoSwglContext::new(width, height));
    let _ = ServoRenderingContext::make_current(&*rendering_context);

    let mut seed: Vec<String> = vec![parsed.origin().ascii_serialization()];
    if let Some(allow) = surface_fetch_allow(&surface) {
        seed.extend(allow);
    }
    let delegate = build_cap_gate(surface, &seed);

    let webview = WebViewBuilder::new(servo, rendering_context.clone())
        .url(parsed)
        .delegate(delegate.clone())
        .build();

    // Pump until loaded + first frame ready, bounded (the same load loop as
    // `render_url_on_servo`).
    let mut spins = 0;
    while spins < max_spins {
        servo.spin_event_loop();
        if delegate.load_complete.get() && delegate.frame_ready.get() {
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(1));
        spins += 1;
    }
    for _ in 0..16 {
        servo.spin_event_loop();
        std::thread::sleep(std::time::Duration::from_millis(1));
    }

    // FRAME A — the loaded page before any input.
    webview.paint();
    let (w, h) = rendering_context.inner().size();
    let frame_a = rendering_context
        .inner()
        .read_to_image(crate::swgl_context::ReadRect::whole(w, h))?;

    // ── DELIVER THE INPUT ──, then pump so the engine processes it (hit-test on the
    // paint thread, scroll-tree update / script on the constellation/script threads)
    // and produces a new built frame.
    delegate.frame_ready.set(false);
    apply_input(&webview, input);
    for _ in 0..256 {
        servo.spin_event_loop();
        std::thread::sleep(std::time::Duration::from_millis(1));
    }

    // FRAME B — after the input. A scroll past the fold makes this differ from A.
    webview.paint();
    let frame_b = rendering_context
        .inner()
        .read_to_image(crate::swgl_context::ReadRect::whole(w, h))?;

    Some((frame_a, frame_b))
}

// ─────────────────────────────────────────────────────────────────────────────
// THE PERSISTENT LIVE WEBVIEW — the cockpit-pane holder (SERVO-INTERACTIVE §3/§5.1).
//
// `render_url_*` above each build a fresh `WebView` per call (the spike shape). To
// intersperse a LIVE web pane into the gpui cockpit, the pane needs ONE long-lived
// `WebView` on ONE engine: load a URL, keep it alive, feed it input between paints,
// and read back the current tile on demand. [`LiveWebView`] is exactly that — the
// SAME `ServoSwglContext` + `CapGate` + `apply_input` loop the spike proves, only
// HELD across calls instead of constructed per call.
//
// !Send by construction (`servo::Servo`/`WebView` are `Rc`-based); the cockpit is a
// gpui view that lives on the main thread and drives this under the process-wide
// `with_gl` SWGL lock, so the single-thread + single-engine discipline holds.
// ─────────────────────────────────────────────────────────────────────────────

thread_local! {
    /// At most ONE [`LiveWebView`] (hence one `Servo` engine) may exist per process —
    /// `servo_config::opts` is a process-wide `OnceCell` set once by `ServoBuilder::build`.
    /// This flag refuses a second concurrent engine so a buggy caller fails loudly
    /// instead of tripping servo's `OnceCell` re-set panic. Cleared on [`LiveWebView`] drop.
    static LIVE_WEBVIEW_ALIVE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// A persistent, live `servo::WebView` on its own `servo::Servo` engine, rendering
/// into a held [`ServoSwglContext`] behind the cap gate — the embeddable web pane.
///
/// Build it once ([`LiveWebView::open`]); thereafter [`LiveWebView::apply_input`]
/// feeds one input event (scroll / click / move / key) and repaints, and
/// [`LiveWebView::frame`] reads the current RGBA8 tile. This is the "hold ONE
/// engine + a per-pane WebView, bridge events → `apply_input`, repaint on change"
/// of `SERVO-INTERACTIVE.md §5.1`, made concrete.
///
/// `!Send`: `servo::Servo`/`WebView` are `Rc`-based and servo's options are a
/// process `OnceCell`, so this lives on ONE thread (the gpui main thread) and all
/// of its methods MUST be called under [`crate::with_gl`] (the process-wide SWGL
/// current-context lock) — every public method documents this.
pub struct LiveWebView {
    /// The one-per-process engine. Held for the pane's lifetime (re-navigating
    /// rebuilds the `WebView` on THIS engine, never a second `Servo`).
    servo: servo::Servo,
    /// The held render target the live `WebView` paints into — selected at runtime by
    /// [`crate::make_rendering_context`]: the HARDWARE-GL [`crate::ServoGpuContext`]
    /// (surfman, GPU-accelerated paint + `glReadPixels` readback) on a desktop with a
    /// GPU, else the software SWGL [`ServoSwglContext`] fallback (no-GPU / seL4 PD /
    /// headless). The same `Rc<dyn RenderingContext>` `WebViewBuilder` takes either
    /// way, so the embed code below is backend-agnostic; the tile readback goes through
    /// the trait's `read_to_image`, which both backends implement (`SERVO-INTERACTIVE.md §4`).
    rendering_context: Rc<dyn ServoRenderingContext>,
    /// Whether [`Self::rendering_context`] is the GPU backend (`true`) or the SWGL
    /// fallback (`false`) — the runtime selection result, surfaced for status/logging.
    gpu_backed: bool,
    /// The live `WebView` — `None` until [`LiveWebView::open`]/[`LiveWebView::load`]
    /// builds one. Rebuilt on navigation.
    webview: Option<WebView>,
    /// The cap gate delegate for the current `WebView` (carries `frame_ready` /
    /// `load_complete` + the net-cap audit). Rebuilt alongside `webview`.
    delegate: Option<Rc<CapGate>>,
    /// The current tile (the last frame read back). Repainted by [`Self::repaint`].
    frame: Option<RgbaFrame>,
    /// The viewport size (device pixels) the context + `WebView` are sized to.
    size: (u32, u32),
    /// The URL currently loaded (for status / reload).
    url: Option<String>,
}

impl Drop for LiveWebView {
    fn drop(&mut self) {
        LIVE_WEBVIEW_ALIVE.with(|a| a.set(false));
    }
}

impl LiveWebView {
    /// Build the persistent engine + render context for a `width`×`height` pane,
    /// selecting the HARDWARE-GL backend when a GPU is available (else the SWGL
    /// fallback) via [`crate::make_rendering_context`]. Does NOT load a page yet (call
    /// [`Self::load`]). Returns `Err` if a [`LiveWebView`] already exists on this
    /// process (only one `Servo` engine is permitted — its options are a process-wide
    /// `OnceCell`).
    ///
    /// MUST be called under [`crate::with_gl`].
    pub fn new(width: u32, height: u32) -> Result<Self, &'static str> {
        if LIVE_WEBVIEW_ALIVE.with(|a| a.replace(true)) {
            return Err("a LiveWebView (Servo engine) already exists on this process");
        }
        let servo = ServoBuilder::default()
            .event_loop_waker(Box::new(HeadlessWaker))
            .build();
        // GPU-accelerated paint where a hardware GL device opens, SWGL otherwise — the
        // §4.3 runtime selection, built INLINE so `gpu_backed` reflects the ACTUAL
        // backend produced (not a separate `gpu_available()` probe that could disagree
        // if the GPU device opens but its offscreen surface fails). Both yield the same
        // `Rc<dyn RenderingContext>` the embed code drives.
        let (rendering_context, gpu_backed): (Rc<dyn ServoRenderingContext>, bool) =
            match crate::gpu_context::ServoGpuContext::new(width, height) {
                Ok(gpu) => (Rc::new(gpu), true),
                Err(_) => (Rc::new(ServoSwglContext::new(width, height)), false),
            };
        let _ = ServoRenderingContext::make_current(&*rendering_context);
        Ok(LiveWebView {
            servo,
            rendering_context,
            gpu_backed,
            webview: None,
            delegate: None,
            frame: None,
            size: (width, height),
            url: None,
        })
    }

    /// Build the pane AND load `url` through the cap gate, pumping until the page is
    /// loaded + painted, leaving a live `WebView` ready for input. The convenience
    /// constructor for "open a live web pane at this URL". MUST be called under
    /// [`crate::with_gl`].
    pub fn open(
        url: &str,
        surface: SurfaceCapability,
        width: u32,
        height: u32,
        max_spins: usize,
    ) -> Result<Self, &'static str> {
        let mut live = Self::new(width, height)?;
        live.load(url, surface, max_spins);
        Ok(live)
    }

    /// Navigate the live pane to `url` (building a fresh `WebView` on the held engine,
    /// pointed at the held render context — GPU or SWGL — behind a fresh [`CapGate`] for
    /// `surface`), pump until loaded + painted, and read back the first tile. Re-navigating drops
    /// the previous `WebView` and builds a new one on the SAME engine (servo's options
    /// are a process `OnceCell`, so the engine is never rebuilt). MUST be called under
    /// [`crate::with_gl`]. Returns `true` if a frame was produced.
    pub fn load(&mut self, url: &str, surface: SurfaceCapability, max_spins: usize) -> bool {
        let Ok(parsed) = Url::parse(url) else {
            return false;
        };

        let mut seed: Vec<String> = vec![parsed.origin().ascii_serialization()];
        if let Some(allow) = surface_fetch_allow(&surface) {
            seed.extend(allow);
        }
        let delegate = build_cap_gate(surface, &seed);

        let _ = ServoRenderingContext::make_current(&*self.rendering_context);
        let webview = WebViewBuilder::new(&self.servo, self.rendering_context.clone())
            .url(parsed)
            .delegate(delegate.clone())
            .build();

        // Pump until loaded AND a frame is ready (bounded), then a few paced extra
        // spins so the WebRender scene is fully built — the SAME load loop the
        // headless `render_url_on_servo` uses.
        let mut spins = 0;
        while spins < max_spins {
            self.servo.spin_event_loop();
            if delegate.load_complete.get() && delegate.frame_ready.get() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(1));
            spins += 1;
        }
        for _ in 0..16 {
            self.servo.spin_event_loop();
            std::thread::sleep(std::time::Duration::from_millis(1));
        }

        self.webview = Some(webview);
        self.delegate = Some(delegate);
        self.url = Some(url.to_string());
        self.repaint();
        self.frame.is_some()
    }

    /// Read the current page into the held tile (`WebView::paint` → the backend's back
    /// buffer → `read_to_image`). Backend-agnostic: the readback goes through the servo
    /// `RenderingContext` trait, so it is SWGL's `read_pixels` on the software path and
    /// `glReadPixels` (route-a) on the GPU path — both yield the same [`RgbaFrame`].
    /// Called after a load or an input. MUST be called under [`crate::with_gl`].
    fn repaint(&mut self) {
        let Some(webview) = self.webview.as_ref() else {
            return;
        };
        let _ = ServoRenderingContext::make_current(&*self.rendering_context);
        webview.paint();
        self.frame = self.read_trait_frame();
    }

    /// Read the whole framebuffer back as an [`RgbaFrame`] through the servo
    /// `RenderingContext` trait (`read_to_image`), so it works for EITHER backend (the
    /// SWGL `ServoSwglContext` and the hardware `ServoGpuContext` both implement it).
    /// Mirrors the standalone `read_frame` but over the trait object.
    fn read_trait_frame(&self) -> Option<RgbaFrame> {
        let size = self.rendering_context.size();
        let rect = DeviceIntRect::from_origin_and_size(
            euclid::Point2D::origin(),
            euclid::Size2D::new(size.width as i32, size.height as i32),
        );
        let img = self.rendering_context.read_to_image(rect)?;
        let (w, h) = (img.width(), img.height());
        Some(RgbaFrame {
            width: w,
            height: h,
            bytes: img.into_raw(),
        })
    }

    /// **THE LIVE LOOP — feed ONE input event to the live `WebView`, pump the engine,
    /// and repaint.** A scroll/click/move/key on the cockpit web-pane lowers to a
    /// [`WebInput`] and lands here: the input is delivered through the SAME
    /// [`apply_input`] the interactivity spike proves, the actor threads are pumped so
    /// the input takes effect (scroll-tree update / hit-test / script), and the page is
    /// repainted. Returns `true` if the resulting tile DIFFERS from the previous one
    /// (the content digest changed) — the "repaint on change" signal the cockpit uses
    /// to `cx.notify()`. MUST be called under [`crate::with_gl`].
    ///
    /// `pump` bounds how many `spin_event_loop` iterations to drive between the input
    /// and the repaint (a scroll needs only a handful; a click that runs script may
    /// want more). The spike uses 256; a live pane uses fewer for responsiveness.
    pub fn apply_input(&mut self, input: WebInput, pump: usize) -> bool {
        let Some(webview) = self.webview.as_ref() else {
            return false;
        };
        let before = self.frame.as_ref().map(|f| f.content_digest());

        if let Some(d) = self.delegate.as_ref() {
            d.frame_ready.set(false);
        }
        apply_input(webview, input);
        for _ in 0..pump {
            self.servo.spin_event_loop();
            // A short yield lets servo's worker threads make progress between spins
            // (the same pacing the headless loops use). Cheap; bounded by `pump`.
            std::thread::sleep(std::time::Duration::from_millis(1));
            // Early-out once the engine reports a fresh frame is ready to read back.
            if self
                .delegate
                .as_ref()
                .map(|d| d.frame_ready.get())
                .unwrap_or(false)
            {
                break;
            }
        }
        self.repaint();

        let after = self.frame.as_ref().map(|f| f.content_digest());
        before != after
    }

    /// The current tile (the last frame read back), or `None` before the first load.
    pub fn frame(&self) -> Option<&RgbaFrame> {
        self.frame.as_ref()
    }

    /// The URL currently loaded, if any.
    pub fn url(&self) -> Option<&str> {
        self.url.as_deref()
    }

    /// The viewport size (device pixels) the pane renders at.
    pub fn size(&self) -> (u32, u32) {
        self.size
    }

    /// Whether a live `WebView` is currently built (a page has been loaded).
    pub fn is_loaded(&self) -> bool {
        self.webview.is_some()
    }

    /// Whether this pane renders on the HARDWARE-GL backend (`true`, GPU-accelerated)
    /// or the SWGL software fallback (`false`) — the runtime selection result.
    pub fn gpu_backed(&self) -> bool {
        self.gpu_backed
    }

    /// A short label for the active backend (`"GPU (hardware-GL)"` or `"SWGL (software)"`)
    /// — for the cockpit status line.
    pub fn backend_label(&self) -> &'static str {
        if self.gpu_backed {
            "GPU (hardware-GL)"
        } else {
            "SWGL (software)"
        }
    }
}

/// The surface's fetch allowlist as a `Vec<String>` (for seeding reachable peers) —
/// `None` when the surface is the wildcard root (no finite allowlist to seed beyond
/// the navigated origin).
fn surface_fetch_allow(surface: &SurfaceCapability) -> Option<Vec<String>> {
    surface
        .fetch_allow
        .as_ref()
        .map(|s| s.iter().cloned().collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::emulated_kernel::EmulatedKernel;
    use dregg_firmament::{cell_seed, label_of, CompositorPd, Scene, Surface};
    use starbridge_web_surface::AuthRequired;

    use crate::compositor_seam::{present_frame, FramePresentation};

    /// Encode an RGBA8 buffer (`w*h*4` bytes, row-major) to PNG bytes (8-bit,
    /// color-type 6 = RGBA), using only STORED (uncompressed) deflate blocks so it
    /// needs no compressor — the SAME self-contained encoder `tests/swgl_render_to_png.rs`
    /// uses (CRC-32 over each chunk, Adler-32 over the zlib payload), inlined here so the
    /// real-page render writes its proof PNG with ZERO added dependency.
    fn png_encode_rgba8(w: u32, h: u32, rgba: &[u8]) -> Vec<u8> {
        fn crc32(bytes: &[u8]) -> u32 {
            let mut crc: u32 = 0xFFFF_FFFF;
            for &b in bytes {
                crc ^= b as u32;
                for _ in 0..8 {
                    let mask = (crc & 1).wrapping_neg();
                    crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
                }
            }
            !crc
        }
        fn adler32(bytes: &[u8]) -> u32 {
            const MOD: u32 = 65521;
            let (mut a, mut b) = (1u32, 0u32);
            for &x in bytes {
                a = (a + x as u32) % MOD;
                b = (b + a) % MOD;
            }
            (b << 16) | a
        }
        fn chunk(out: &mut Vec<u8>, kind: &[u8; 4], data: &[u8]) {
            out.extend_from_slice(&(data.len() as u32).to_be_bytes());
            let mut typed = Vec::with_capacity(4 + data.len());
            typed.extend_from_slice(kind);
            typed.extend_from_slice(data);
            out.extend_from_slice(&typed);
            out.extend_from_slice(&crc32(&typed).to_be_bytes());
        }
        // Filtered scanlines: a filter-type byte 0 (None) per row, then the RGBA bytes.
        // SWGL/WebRender render with the GL bottom-left origin, so framebuffer row 0 is
        // the BOTTOM of the image; servo's own `read_framebuffer_to_image`
        // (`rendering_context.rs`) flips vertically for exactly this reason. We do the
        // same here so the captured PNG is upright (row 0 = top): emit source row
        // `h-1-y` for output row `y`.
        let row_bytes = (w * 4) as usize;
        let mut raw = Vec::with_capacity((h * (1 + w * 4)) as usize);
        for y in 0..h {
            raw.push(0);
            let src = ((h - 1 - y) * w * 4) as usize;
            raw.extend_from_slice(&rgba[src..src + row_bytes]);
        }
        // zlib with STORED blocks.
        let mut z = vec![0x78u8, 0x01];
        let mut off = 0usize;
        while off < raw.len() {
            let take = (raw.len() - off).min(0xFFFF);
            let bfinal = if off + take >= raw.len() { 1u8 } else { 0u8 };
            z.push(bfinal);
            z.extend_from_slice(&(take as u16).to_le_bytes());
            z.extend_from_slice(&(!(take as u16)).to_le_bytes());
            z.extend_from_slice(&raw[off..off + take]);
            off += take;
        }
        z.extend_from_slice(&adler32(&raw).to_be_bytes());

        let mut png = vec![0x89, b'P', b'N', b'G', 0x0D, 0x0A, 0x1A, 0x0A];
        let mut ihdr = Vec::new();
        ihdr.extend_from_slice(&w.to_be_bytes());
        ihdr.extend_from_slice(&h.to_be_bytes());
        ihdr.extend_from_slice(&[8, 6, 0, 0, 0]); // depth 8, RGBA, deflate, adaptive filter, no interlace
        chunk(&mut png, b"IHDR", &ihdr);
        chunk(&mut png, b"IDAT", &z);
        chunk(&mut png, b"IEND", &[]);
        png
    }

    /// **THE FIRST REAL RENDER (Stage-A step 3, never previously executed): a real
    /// Servo `WebView` rasterizes a page into a SWGL `RgbaFrame`, which then lands on
    /// the compositor-PD's glass through the genuine T1/T2/T3 gate.**
    ///
    /// This is the page→glass flow with the *page content rendered by the real
    /// engine* (not the clear-to-color stand-in): `render_url_to_frame` builds a real
    /// `Servo` (`ServoBuilder`), points a real `WebView` (`WebViewBuilder`) at our
    /// [`ServoSwglContext`] (the SWGL software rasterizer — no GPU/EGL/surfman),
    /// installs the [`CapGate`] delegate (so the held [`SurfaceCapability`] mediates
    /// every fetch/navigation), loads an in-memory `data:` HTML page, spins the actor
    /// threads until load+paint, and reads the RGBA8 back via the genuine
    /// `RenderingContext::read_to_image`. We then carry that REAL frame through
    /// [`present_frame`] — the SAME unchanged compositor gate the standalone build
    /// drives — closing F3 with genuine page pixels.
    ///
    /// A wildcard [`SurfaceCapability::root`] cap backs the surface so the inline
    /// `data:` page (whose origin serializes to `"null"`) is permitted; the cap model
    /// is exercised identically to the `cap_gated_pipeline` tests, only with the real
    /// engine in between. The frame is bounded by `max_spins` so a non-painting page
    /// cannot hang the test.
    ///
    /// ✅ **SURFMAN CEILING BROKEN (2026-06-23).** Previously `#[ignore]`d: servo-paint
    /// `0.1.0`'s `register_rendering_context` (`paint.rs:236-238`) unconditionally does
    /// `rendering_context.connection().expect("Failed to get connection")` then
    /// `connection.create_adapter()`, storing the pair in a per-painter
    /// `PainterSurfmanDetails` map (the WebGL-canvas `SwapChains<_, surfman::Device>`
    /// plumbing). A SWGL-only context returning the trait-default `connection() -> None`
    /// panicked there BEFORE any page painted. The break:
    /// [`ServoSwglContext::connection`] now returns a REAL surfman software
    /// `Connection` (`Connection::new()` — the default display connection, NO window /
    /// GPU surface), so registration succeeds; SWGL still does ALL the page
    /// rasterization through `gleam_gl_api()`, and the surfman device is only ever
    /// instantiated for a WebGL canvas (none here). This test now RUNS: the real engine
    /// lays the page out and paints it into the SWGL framebuffer, and the test asserts
    /// the frame carries genuine multi-color laid-out content (not a uniform clear) and
    /// writes it to a PNG.
    #[test]
    fn first_real_render_data_page_through_the_compositor_gate() {
        // An in-memory HTML page — no network, no filesystem; the engine lays it out
        // and paints it into our SWGL framebuffer. Two distinct laid-out regions so the
        // captured frame PROVES real layout happened (a clear-to-color stand-in could
        // never produce two colors at known positions): a blue page background with a
        // centered yellow block in normal flow. `%23` is the URL-escaped `#` of a hex
        // color inside the `data:` URL.
        const PAGE: &str = "data:text/html,\
            <html><body style='margin:0;background:%230000ff'>\
            <div style='margin:40px auto;width:160px;height:120px;background:%23ffff00'>\
            </div></body></html>";
        const W: u32 = 240;
        const H: u32 = 200;

        let presenter = cell_seed(11);
        // The wildcard root surface authority — the `data:` page's null origin is
        // permitted; the cap that authorizes the surface is the cap that presents.
        let surface = SurfaceCapability::root(presenter, AuthRequired::Either);

        // THE STAGE-A STEP-3 PAYOFF, now executed: drive the real Servo engine to
        // rasterize the page. Serialized on the process-wide SWGL current-context lock
        // (SWGL's `ctx` is a global) for the whole engine-drive → readback sequence.
        // We build ONE engine and render BOTH this box page and the text page on it
        // (`render_glyph_page`), because Servo's `servo_config::opts` is a process-wide
        // `OnceCell` set once per process — at most one `Servo` may exist per process.
        let frame = crate::swgl_context::with_gl(|| {
            let servo = servo::ServoBuilder::default()
                .event_loop_waker(Box::new(super::HeadlessWaker))
                .build();
            let box_frame = super::render_url_on_servo(&servo, PAGE, surface, W, H, 4096)
                .0
                .expect("the real Servo WebView produced a frame for the data: page");
            // SECOND page on the SAME engine: a text page, proving glyph layout.
            render_glyph_page(&servo);
            box_frame
        });

        // It is a REAL RGBA8 frame of the requested size.
        assert_eq!(frame.width, W);
        assert_eq!(frame.height, H);
        assert_eq!(
            frame.bytes.len(),
            (W * H * 4) as usize,
            "real RGBA8, 4 bytes/pixel"
        );

        // ── PROVE it is genuine laid-out PAGE content, not an empty/uniform buffer ──
        // The page has two CSS-positioned regions; a real layout+paint produces BOTH
        // the blue background and the yellow block. Count distinct colors and confirm
        // the frame is non-trivial. (A bare clear or an unpainted buffer is one color.)
        let mut distinct = std::collections::BTreeSet::new();
        for i in 0..(frame.width * frame.height) as usize {
            let p = &frame.bytes[i * 4..i * 4 + 4];
            distinct.insert([p[0], p[1], p[2], p[3]]);
            if distinct.len() > 8 {
                break;
            }
        }
        assert!(
            distinct.len() >= 2,
            "the rendered page is non-trivial (≥2 distinct colors = real layout, not a uniform clear); got {} distinct color(s)",
            distinct.len()
        );

        // ── write the captured PNG artifact (the load-bearing proof-of-render) ──
        let out_path = std::env::var("WEB_RENDER_PNG_OUT").unwrap_or_else(|_| {
            let mut p = std::env::temp_dir();
            p.push("servo_real_page_render.png");
            p.to_string_lossy().into_owned()
        });
        let png = png_encode_rgba8(frame.width, frame.height, &frame.bytes);
        std::fs::write(&out_path, &png).expect("write the rendered-page PNG");
        let png_len = std::fs::metadata(&out_path).map(|m| m.len()).unwrap_or(0);
        assert!(
            png_len > 100,
            "the captured PNG is substantial, got {png_len} bytes"
        );
        println!(
            "WEB_RENDER_PNG_WRITTEN path={out_path} bytes={png_len} dims={W}x{H} \
             distinct_colors={} page='data: blue bg + yellow block (real servo layout)'",
            distinct.len()
        );

        // Carry the real page's pixels through the GENUINE compositor gate.
        let scene = Scene {
            surfaces: vec![Surface {
                owner: presenter,
                regions: vec![3],
                content_digest: 0,
                source_state_root: 7,
                z_layer: 0,
                focus_flag: true,
            }],
        };
        let mut compositor = CompositorPd::boot(EmulatedKernel::new(), scene);

        let commit = present_frame(
            &mut compositor,
            &frame,
            &FramePresentation {
                presenter,
                target_regions: vec![3],
                source_state_root: 7,
                claims_focus: true,
            },
        )
        .expect("the real page's frame is admitted by the gate");

        // The commit carries the REAL page pixels' digest + the genuine owner-binding.
        assert_eq!(
            commit.digest,
            frame.content_digest(),
            "the real page's digest is committed"
        );
        assert_eq!(
            commit.label,
            label_of(&presenter, 7),
            "T2: the genuine owner-binding"
        );
        // The glass shows the rendered page's digest byte in the authorized tile.
        assert_eq!(
            compositor.framebuffer_snapshot()[3],
            (frame.content_digest() & 0xFF) as u8,
            "the real Servo-rendered page composited to the glass through the gate"
        );
    }

    /// **A REAL PAGE WITH TEXT — proving the engine lays out + rasterizes GLYPHS, not
    /// just CSS boxes.** Renders a `data:` page with a white background and black
    /// heading text on the GIVEN engine (`servo` — the same one the box page used,
    /// since at most one `Servo` exists per process). A real font shaping + glyph
    /// raster produces black antialiased text pixels over white — so the captured frame
    /// contains MANY distinct colors (the antialiasing gradient between black glyph and
    /// white background), which a box-only or clear-to-color render never produces. This
    /// is the "text from the HTML" half of the deliverable's bar. The PNG is written
    /// next to the box render's. Called (not `#[test]`) from the engine-owning test so
    /// it shares the single process-global Servo.
    fn render_glyph_page(servo: &servo::Servo) {
        // Large dark heading on white — the glyph edges antialias, yielding gray
        // intermediates between #000 and #fff that ONLY a real glyph raster produces.
        const PAGE: &str = "data:text/html,\
            <html><body style='margin:0;background:%23ffffff'>\
            <h1 style='margin:20px;font-size:48px;color:%23000000'>dregg</h1>\
            </body></html>";
        const W: u32 = 320;
        const H: u32 = 120;

        let presenter = cell_seed(11);
        let surface = SurfaceCapability::root(presenter, AuthRequired::Either);

        let frame = super::render_url_on_servo(servo, PAGE, surface, W, H, 4096)
            .0
            .expect("the real Servo WebView produced a frame for the text page");

        assert_eq!(frame.width, W);
        assert_eq!(frame.height, H);

        // Count distinct colors AND look for both near-white (background) and dark
        // (glyph ink) plus an antialiasing intermediate (a gray that is neither).
        let mut distinct = std::collections::BTreeSet::new();
        let mut has_white = false;
        let mut has_dark = false;
        let mut has_intermediate = false;
        for i in 0..(frame.width * frame.height) as usize {
            let p = &frame.bytes[i * 4..i * 4 + 4];
            distinct.insert([p[0], p[1], p[2], p[3]]);
            let lum = p[0] as u32 + p[1] as u32 + p[2] as u32;
            if lum >= 3 * 250 {
                has_white = true;
            } else if lum <= 3 * 40 {
                has_dark = true;
            } else {
                has_intermediate = true;
            }
        }
        assert!(has_white, "the page background (white) is present");
        assert!(
            has_dark,
            "glyph ink (near-black) is present — real text was rasterized"
        );
        assert!(
            has_intermediate,
            "antialiased glyph edges (gray intermediates) are present — a box/clear render \
             has no intermediates; only a real font glyph raster does"
        );
        assert!(
            distinct.len() >= 8,
            "real antialiased text yields many distinct colors; got {}",
            distinct.len()
        );

        let out_path = std::env::var("WEB_RENDER_TEXT_PNG_OUT").unwrap_or_else(|_| {
            let mut p = std::env::temp_dir();
            p.push("servo_real_text_render.png");
            p.to_string_lossy().into_owned()
        });
        let png = png_encode_rgba8(frame.width, frame.height, &frame.bytes);
        std::fs::write(&out_path, &png).expect("write the rendered text-page PNG");
        let png_len = std::fs::metadata(&out_path).map(|m| m.len()).unwrap_or(0);
        println!(
            "WEB_RENDER_TEXT_PNG_WRITTEN path={out_path} bytes={png_len} dims={W}x{H} \
             distinct_colors={} page='data: white bg + black <h1>dregg</h1> (real glyph layout)'",
            distinct.len()
        );
    }

    /// **THE INTERACTIVITY SPIKE, EXECUTED: a scroll input to the live `WebView`
    /// produces a DIFFERENT tile.** This is the move from a static snapshot to a live
    /// embedded webview — the deliverable's "two differing tiles" bar.
    ///
    /// We render a page TALLER than the viewport with two distinct color bands stacked
    /// so that only the FIRST band is visible at scroll offset 0 and the SECOND becomes
    /// visible after scrolling down. [`render_url_then_input_on_servo`] paints frame A
    /// (top of page), delivers a downward [`WebInput::Scroll`], pumps the engine,
    /// repaints frame B (scrolled), and returns both. A real, LIVE WebView makes B's
    /// pixels differ from A's; a static snapshot could not. We assert the two frames'
    /// content digests differ.
    #[test]
    fn a_scroll_input_re_renders_the_webview_to_a_different_tile() {
        // A page much taller than the 200px viewport: a 600px red block followed by a
        // 600px lime block. At offset 0 the viewport shows red; after scrolling down
        // ~400px the lime block enters the viewport, so the painted pixels change.
        const PAGE: &str = "data:text/html,\
            <html><body style='margin:0'>\
            <div style='height:600px;background:%23ff0000'></div>\
            <div style='height:600px;background:%2300ff00'></div>\
            </body></html>";
        const W: u32 = 240;
        const H: u32 = 200;

        let presenter = cell_seed(11);
        let surface = SurfaceCapability::root(presenter, AuthRequired::Either);

        let (a, b) = crate::swgl_context::with_gl(|| {
            let servo = servo::ServoBuilder::default()
                .event_loop_waker(Box::new(super::HeadlessWaker))
                .build();
            super::render_url_then_input_on_servo(
                &servo,
                PAGE,
                surface,
                W,
                H,
                // Scroll down 450px at the viewport center — past the first block, so the
                // lime block enters view.
                super::WebInput::Scroll {
                    x: 120.0,
                    y: 100.0,
                    dx: 0.0,
                    dy: 450.0,
                },
                4096,
            )
            .expect("the live WebView produced both a pre- and post-scroll frame")
        });

        assert_eq!(a.width, W);
        assert_eq!(b.width, W);
        assert_eq!(a.bytes.len(), (W * H * 4) as usize);
        // The load-bearing assertion: the scroll changed what is on screen, so the two
        // frames' content digests DIFFER — the WebView re-rendered in response to input.
        assert_ne!(
            a.content_digest(),
            b.content_digest(),
            "scrolling the live WebView produced a DIFFERENT tile (input → re-render → new frame); \
             a static snapshot would yield the same digest"
        );

        // Stronger: frame A is dominated by red (the top block), frame B by lime — a
        // direct witness that the SECOND block scrolled into view, not just noise.
        fn dominant_is(frame: &RgbaFrame, r: u8, g: u8, b: u8) -> usize {
            let mut n = 0usize;
            for i in 0..(frame.width * frame.height) as usize {
                let p = &frame.bytes[i * 4..i * 4 + 4];
                // tolerate antialiasing / sub-pixel by a loose threshold
                if (p[0] as i32 - r as i32).abs() < 48
                    && (p[1] as i32 - g as i32).abs() < 48
                    && (p[2] as i32 - b as i32).abs() < 48
                {
                    n += 1;
                }
            }
            n
        }
        let a_red = dominant_is(&a, 255, 0, 0);
        let b_lime = dominant_is(&b, 0, 255, 0);
        println!(
            "INTERACTIVE_SPIKE pre_scroll_red_px={a_red} post_scroll_lime_px={b_lime} \
             digest_a={:#x} digest_b={:#x}",
            a.content_digest(),
            b.content_digest()
        );
        assert!(a_red > 0, "the top (red) block is visible before scrolling");
        assert!(
            b_lime > 0,
            "the second (lime) block scrolled into view after the scroll input — a LIVE re-render"
        );
    }

    /// **THE NET-CAP SOCKET BIND, PROVEN IN THE REAL `CapGate`.** The `CapGate` is the
    /// genuine libservo `WebViewDelegate` (built by [`build_cap_gate`], the SAME path
    /// `render_url_to_frame_netcap` uses). This drives its [`CapGate::decide_net_cap`] —
    /// the exact decision servo's `load_web_resource` callback runs — directly, so it
    /// is provable WITHOUT the surfman-blocked painter:
    ///
    ///   * an origin the held cap does NOT authorize → `RefusedByCap`, and the audited
    ///     netlayer was NEVER dialed (the dialed-audit is empty) — the gate bit at the
    ///     socket, before any `Netlayer::dial`;
    ///   * an origin the cap DOES authorize → `Dialed` through the real netlayer, the
    ///     connection recorded in the audit.
    ///
    /// This is the deliverable's "prove the gate bites" through the REAL delegate the
    /// real WebView installs, not a mock.
    #[test]
    fn cap_gate_net_cap_refuses_unauthorized_origin_at_the_socket() {
        let presenter = cell_seed(11);
        // A surface scoped to example.com (NOT evil.com).
        let surface = SurfaceCapability::scoped(
            presenter,
            AuthRequired::Either,
            [String::from("https://example.com")],
            [],
        );
        // The same gate the real WebView gets, with example.com's peer joined reachable.
        let gate = build_cap_gate(surface, &["https://example.com".to_string()]);

        // The cap-denied origin: refused at the socket, NO dial.
        let denied = gate.decide_net_cap("https://evil.com");
        assert!(
            denied.refused_by_cap(),
            "evil.com is refused by the held cap: {denied:?}"
        );
        assert!(
            gate.connector.dialed_origins().is_empty(),
            "Netlayer::dial was NEVER called for the cap-denied origin — the socket never opened"
        );

        // The cap-authorized origin: dials through the audited netlayer.
        let allowed = gate.decide_net_cap("https://example.com");
        assert!(
            allowed.dialed(),
            "example.com dials through the netlayer: {allowed:?}"
        );
        let dialed = gate.connector.dialed_origins();
        assert_eq!(
            dialed.len(),
            1,
            "exactly the authorized origin opened an audited session"
        );
        assert_eq!(dialed[0].0, "https://example.com");

        // The audit trail recorded BOTH decisions (refused, then dialed), newest last.
        let outcomes = gate.net_outcomes.borrow();
        assert_eq!(outcomes.len(), 2);
        assert!(outcomes[0].refused_by_cap());
        assert!(outcomes[1].dialed());
    }

    /// **THE LIVE WEBVIEW ON THE GPU BACKEND — a real page lays out + paints through the
    /// HARDWARE-GL context, and a scroll input re-renders it.** This proves the GPU work
    /// is wired all the way into the persistent [`LiveWebView`] (not just the standalone
    /// `ServoGpuContext` spike): `LiveWebView::new` selects the hardware backend via
    /// [`crate::gpu_context::make_rendering_context`]'s logic when a GPU is present, a
    /// real `data:` page renders into it (read back through the trait's `glReadPixels`
    /// route-a path), and the live-input loop ([`LiveWebView::apply_input`]) produces a
    /// DIFFERENT tile after a scroll — the full live loop, on the GPU.
    ///
    /// On this macOS host a hardware surfman device opens, so `gpu_backed()` is `true`
    /// and the page paints on the GPU. On a no-GPU box (CI/headless) `gpu_backed()` is
    /// `false` and the SAME assertions hold over the SWGL fallback — the backend is
    /// transparent to the live loop. Either way we assert `gpu_backed()` AGREES with
    /// `gpu_available()` (the selection is honest) and that the page renders + re-renders.
    #[test]
    fn live_webview_renders_and_re_renders_on_the_selected_backend() {
        use crate::gpu_context::gpu_available;

        // A page taller than the viewport: a 600px red band over a 600px lime band, so a
        // downward scroll flips the visible band (the same content the SWGL spike uses).
        const PAGE: &str = "data:text/html,\
            <html><body style='margin:0'>\
            <div style='height:600px;background:%23ff0000'></div>\
            <div style='height:600px;background:%2300ff00'></div>\
            </body></html>";
        const W: u32 = 240;
        const H: u32 = 200;

        let presenter = cell_seed(11);
        let surface = SurfaceCapability::root(presenter, AuthRequired::Either);

        crate::swgl_context::with_gl(|| {
            let expect_gpu = gpu_available();

            let mut live = super::LiveWebView::new(W, H)
                .expect("a single LiveWebView builds (no other engine on this process)");

            // THE SELECTION IS HONEST: the backend the holder reports matches the probe.
            assert_eq!(
                live.gpu_backed(),
                expect_gpu,
                "LiveWebView selected the GPU backend iff a hardware device is available \
                 (gpu_backed={} expect_gpu={})",
                live.gpu_backed(),
                expect_gpu,
            );

            // A real page lays out + paints through the SELECTED backend (GPU here).
            let painted = live.load(PAGE, surface, 4096);
            assert!(
                painted,
                "the live WebView painted a frame for the data: page on the {} backend",
                live.backend_label()
            );
            let frame_a = live
                .frame()
                .expect("a tile was read back after load")
                .clone();
            assert_eq!(frame_a.width, W);
            assert_eq!(frame_a.height, H);
            assert_eq!(frame_a.bytes.len(), (W * H * 4) as usize, "RGBA8");

            // The live loop on this backend: a downward scroll re-renders to a DIFFERENT
            // tile (the lime band enters view) — input → re-render → fresh tile, on the
            // GPU when present.
            let digest_a = frame_a.content_digest();
            let changed = live.apply_input(
                super::WebInput::Scroll {
                    x: 120.0,
                    y: 100.0,
                    dx: 0.0,
                    dy: 450.0,
                },
                512,
            );
            let frame_b = live.frame().expect("a tile after the scroll").clone();
            let digest_b = frame_b.content_digest();

            assert!(
                changed,
                "apply_input reported the tile changed after the scroll"
            );
            assert_ne!(
                digest_a, digest_b,
                "scrolling the live WebView produced a DIFFERENT tile on the {} backend \
                 (input → re-render → new frame)",
                live.backend_label()
            );

            println!(
                "LIVE_WEBVIEW_BACKEND gpu_backed={} backend='{}' \
                 digest_a={:#x} digest_b={:#x} — a real page rendered + re-rendered live",
                live.gpu_backed(),
                live.backend_label(),
                digest_a,
                digest_b,
            );
        });
    }
}
