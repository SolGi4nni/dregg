//! The SWGL `RenderingContext` shim — the heart of Stage A.
//!
//! `docs/desktop-os-research/SERVO-ON-SEL4.md §1.5`: servo does NOT ship SWGL; its
//! "software" renderer (`SoftwareRenderingContext`) rides surfman → Mesa/llvmpipe
//! via EGL — a *real* GL implementation, not a self-contained CPU rasterizer. So
//! selecting SWGL is not flipping a flag; it is **writing a small new
//! `RenderingContext` impl** that holds a `swgl::Context`, allocates the RGBA8
//! `Vec<u8>`, calls `init_default_framebuffer`, returns the swgl `Context` as the
//! gleam `Gl`, and reads pixels back via `read_pixels`. This module is that impl.
//!
//! ## What is real here (the de-risking core)
//!
//! Under the default `swgl-standalone` feature this depends on NOTHING but `swgl`
//! + `gleam`. It therefore proves the load-bearing, genuinely-uncertain thing:
//!   **that WebRender's SWGL — a CPU-only C++17 software rasterizer — compiles
//!   (clang, `gl.cc`) on this host and produces REAL RGBA8 pixels into a buffer we
//!   own**, with zero GPU / EGL / windowing dependency. That is the whole "no card"
//!   claim of Stage A, and it is verified by [`tests`] WITHOUT the multi-GB mozjs
//!   build the full `WebView` path needs.
//!
//! ## The trait it implements
//!
//! [`RenderingContext`] here is a faithful LOCAL MIRROR of servo's real
//! `paint_api::rendering_context::RenderingContext` (`servo-paint-api 0.1.0-rc2`),
//! method-for-method on the surface that matters for software rendering:
//! `make_current`, `prepare_for_rendering`, `read_to_image`, `size`/`resize`,
//! `present`, `gleam_gl_api`. The mirror exists so the wiring is genuine before
//! the engine links; the `libservo` feature swaps it for the REAL trait (see
//! `src/webview.rs`). The one real divergence the real trait forces — it ALSO
//! requires `glow_gl_api() -> Arc<glow::Context>`, which SWGL does not implement —
//! is documented there (it is on the compositor's blit path, NOT the
//! `read_to_image` pixel path, which is pure gleam).

#![cfg(feature = "swgl-standalone")]

use std::cell::Cell;
use std::rc::Rc;

use gleam::gl::{self, Gl};

/// The OpenGL-ES constant for an 8-bit RGBA framebuffer read. SWGL's default
/// framebuffer is hard `GL_RGBA8`; reading it back is `read_pixels(.., GL_RGBA,
/// GL_UNSIGNED_BYTE)` — 4 bytes per pixel, exactly the compositor's tile format.
const RGBA: gl::GLenum = gl::RGBA;
const UNSIGNED_BYTE: gl::GLenum = gl::UNSIGNED_BYTE;

/// **The process-wide SWGL current-context lock — a REAL constraint, not a test
/// crutch.**
///
/// SWGL keeps the current context in a single PROCESS-GLOBAL pointer (`static
/// Context* ctx` at `gl.cc:898`; `MakeCurrent(c)` mutates it globally with NO
/// thread-local isolation — `gl.cc:3074`). So SWGL is designed to be driven from
/// ONE thread at a time (WebRender's render thread); two `SwglRenderingContext`s
/// driven concurrently from different threads stomp each other's `ctx` and
/// framebuffer binding. This is also a load-bearing input to `SERVO-ON-SEL4.md
/// §2.1` (the seL4 thread personality): the *render* itself wants a single owning
/// thread even though servo's actor threads are structural.
///
/// [`with_gl`] serializes a whole `create → make_current → draw → read` sequence
/// behind this lock so the global `ctx` is stable for its duration — exactly the
/// discipline a real single-threaded compositor render pass provides structurally.
/// Exposed `pub` because the integration-test binary (a separate process, but its
/// own tests run in parallel threads) needs the SAME serialization.
pub static GL_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Run `f` while holding the process-wide SWGL [`GL_LOCK`], so the global current
/// context is stable for the whole render→read sequence. Poison-tolerant (a panic
/// in one SWGL test must not wedge the rest): on a poisoned lock we take the guard
/// anyway, since the protected data is `()` (the lock orders access; it guards no
/// invariant-bearing state).
pub fn with_gl<R>(f: impl FnOnce() -> R) -> R {
    let _guard = GL_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    f()
}

/// A minimal `DeviceIntRect`-shaped read region (x, y, w, h) — the local mirror of
/// `webrender_api::units::DeviceIntRect` the real `read_to_image` takes. Kept tiny
/// and dependency-free in the standalone build; the `libservo` path uses the real
/// type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReadRect {
    pub x: i32,
    pub y: i32,
    pub width: i32,
    pub height: i32,
}

impl ReadRect {
    /// The whole framebuffer (origin, full size).
    pub fn whole(width: u32, height: u32) -> Self {
        ReadRect {
            x: 0,
            y: 0,
            width: width as i32,
            height: height as i32,
        }
    }
}

/// A rendered RGBA8 frame the caller OWNS — the `Vec<u8>` SWGL rasterized into,
/// `width * height * 4` bytes, row-major, 4 bytes/pixel (R,G,B,A). This is the
/// concrete "page rendered into a caller-owned buffer" Stage A promises; the
/// compositor hashes it to the `content_digest` and `present()`s the region.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RgbaFrame {
    pub width: u32,
    pub height: u32,
    /// `width * height * 4` bytes, RGBA8 row-major. Owned by the caller.
    pub bytes: Vec<u8>,
}

impl RgbaFrame {
    /// The pixel at `(x, y)` as `(r, g, b, a)`. Panics out of bounds (test helper).
    pub fn pixel(&self, x: u32, y: u32) -> (u8, u8, u8, u8) {
        let i = ((y * self.width + x) * 4) as usize;
        (
            self.bytes[i],
            self.bytes[i + 1],
            self.bytes[i + 2],
            self.bytes[i + 3],
        )
    }

    /// `blake3(bytes)` truncated to a `u64` — the bind from these REAL pixels to
    /// the compositor-PD's `content_digest` (which is a `u64`, the low-bytes tile
    /// witness in `compositor_pd.rs`). The compositor's T1/T2/T3 gate then admits
    /// the region; this digest is the F3-closing promise made GOOD.
    pub fn content_digest(&self) -> u64 {
        let h = blake3::hash(&self.bytes);
        u64::from_le_bytes(h.as_bytes()[..8].try_into().expect("blake3 is 32 bytes"))
    }

    /// A **cheap, non-cryptographic change signal** over the frame bytes — for the
    /// per-input "did the framebuffer change since last frame?" gate, where the FULL
    /// `blake3` of [`Self::content_digest`] is overkill (its collision-resistance is
    /// only load-bearing for the compositor's T2 content-address binding, NOT for a
    /// frame-vs-frame inequality test). This is FNV-1a over the bytes: one multiply +
    /// xor per byte, no cryptographic permutation. A changed frame almost-certainly
    /// changes this signal; an identical frame always yields the same one — exactly
    /// the property a change-detect needs, an order of magnitude cheaper than blake3.
    pub fn change_signal(&self) -> u64 {
        let mut h: u64 = 1469598103934665603; // FNV-1a offset
        for b in &self.bytes {
            h ^= *b as u64;
            h = h.wrapping_mul(1099511628211);
        }
        h
    }
}

/// A faithful LOCAL MIRROR of servo's `paint_api::rendering_context::RenderingContext`
/// (verified against `servo-paint-api 0.1.0-rc2`). Identical method *shapes* on the
/// software-render surface; the `libservo` feature replaces this with the genuine
/// trait so a `WebView` accepts our context. See the module docs for the one real
/// divergence (`glow_gl_api`).
pub trait RenderingContext {
    /// Make this context the current GL context for the thread (real trait:
    /// `make_current(&self) -> Result<(), surfman::Error>`; mirror: infallible —
    /// SWGL's `make_current` cannot fail).
    fn make_current(&self);
    /// Bind the default framebuffer so Servo/WebRender paints into it (real trait:
    /// `prepare_for_rendering`). For SWGL the default framebuffer (FBO 0) is the
    /// buffer we handed `init_default_framebuffer`; this binds it.
    fn prepare_for_rendering(&self);
    /// Read the back buffer into an owned RGBA8 frame (real trait: `read_to_image`
    /// → `Option<image::RgbaImage>`; mirror: `Option<RgbaFrame>`). `None` if no
    /// render has happened.
    fn read_to_image(&self, rect: ReadRect) -> Option<RgbaFrame>;
    /// The current framebuffer size in physical pixels.
    fn size(&self) -> (u32, u32);
    /// Resize the framebuffer (reallocates the backing `Vec<u8>`).
    fn resize(&self, width: u32, height: u32);
    /// Present the frame (real trait: swaps buffers in a double-buffered context).
    /// SWGL-into-our-`Vec` is single-buffered, so this is a flush/no-op — the
    /// pixels are already in our buffer the instant WebRender draws them.
    fn present(&self);
    /// The `gleam::gl::Gl` WebRender's `Renderer` is constructed from. For SWGL
    /// this IS the `swgl::Context` (it `impl Gl`). THIS is the seam that points
    /// WebRender at the software rasterizer — handing it a swgl context instead of
    /// a windowed GL context, with no shim.
    fn gleam_gl_api(&self) -> Rc<dyn Gl>;
}

/// **THE SWGL RENDERING CONTEXT.** A `swgl::Context` whose default framebuffer is
/// a caller-owned RGBA8 `Vec<u8>`. This is the no-GPU, no-EGL, no-windowing render
/// target of Stage A.
///
/// Construction is windowing-free (`SERVO-ON-SEL4.md §1.1`): `Context::create()`
/// → `make_current()` → `init_default_framebuffer(0,0,W,H,W*4, buf)`. There is no
/// display, no surface, no GL config. The page renders into `self.buffer`; you
/// read it out with [`Self::read_frame`] (or the trait's [`RenderingContext::read_to_image`]).
pub struct SwglRenderingContext {
    /// The SWGL context — a complete `gleam::gl::Gl` (CPU rasterizer). `Copy`, a
    /// thin handle over the C++ context pointer.
    swgl: swgl::Context,
    /// The same context behind an `Rc<dyn Gl>`, handed to WebRender's `Renderer`.
    /// (Allocated once; `gleam_gl_api` clones the `Rc`.)
    gl: Rc<dyn Gl>,
    /// Current width in pixels.
    width: Cell<u32>,
    /// Current height in pixels.
    height: Cell<u32>,
    /// **The caller-owned RGBA8 default framebuffer** — `w*h*4` bytes SWGL renders
    /// FBO 0 into. Boxed so its address is stable across moves of `self` (SWGL
    /// holds the raw pointer we gave `init_default_framebuffer`). A `RefCell` is
    /// not needed for the pointer's stability; we re-`init` on resize.
    buffer: Box<std::cell::RefCell<Vec<u8>>>,
}

impl SwglRenderingContext {
    /// Create a SWGL rendering context with a `width × height` RGBA8 default
    /// framebuffer, all owned by the returned value. No GPU, no display, no
    /// surface — `Context::create()` + `init_default_framebuffer` into our own
    /// `Vec<u8>`.
    pub fn new(width: u32, height: u32) -> Self {
        let swgl = swgl::Context::create();
        let gl: Rc<dyn Gl> = Rc::new(swgl);
        let buffer = Box::new(std::cell::RefCell::new(vec![
            0u8;
            (width * height * 4) as usize
        ]));

        let ctx = SwglRenderingContext {
            swgl,
            gl,
            width: Cell::new(width),
            height: Cell::new(height),
            buffer,
        };
        ctx.bind_default_framebuffer();
        ctx
    }

    /// Point SWGL's FBO 0 at our backing buffer at the current size. Idempotent;
    /// called on construction and after [`Self::resize`]. The caller supplies the
    /// pointer + stride (`width*4`); swgl renders directly into our memory
    /// (`SERVO-ON-SEL4.md §1.2`).
    fn bind_default_framebuffer(&self) {
        self.swgl.make_current();
        let w = self.width.get() as i32;
        let h = self.height.get() as i32;
        let mut buf = self.buffer.borrow_mut();
        let ptr = buf.as_mut_ptr() as *mut std::ffi::c_void;
        self.swgl.init_default_framebuffer(0, 0, w, h, w * 4, ptr);
    }

    /// Read the whole default framebuffer back as an owned [`RgbaFrame`] — the
    /// direct (non-trait) accessor the standalone test + the compositor wiring
    /// use. Uses the gleam `Gl::read_pixels` path (`GL_RGBA`, `GL_UNSIGNED_BYTE`),
    /// the SAME path servo's real `read_to_image` uses.
    pub fn read_frame(&self) -> RgbaFrame {
        self.read_to_image(ReadRect::whole(self.width.get(), self.height.get()))
            .expect("a freshly-rendered SWGL framebuffer always reads back")
    }

    /// The underlying `swgl::Context` (so a caller can drive raw GL — e.g. the
    /// trivial-frame test's `clear_color` + `clear`, standing in for a WebRender
    /// `Renderer::render` until the `libservo` feature wires the real one).
    pub fn swgl_context(&self) -> swgl::Context {
        self.swgl
    }
}

impl RenderingContext for SwglRenderingContext {
    fn make_current(&self) {
        self.swgl.make_current();
    }

    fn prepare_for_rendering(&self) {
        // SWGL's default framebuffer is FBO 0 (our buffer); bind it.
        self.gl.bind_framebuffer(gl::FRAMEBUFFER, 0);
    }

    fn read_to_image(&self, rect: ReadRect) -> Option<RgbaFrame> {
        if rect.width <= 0 || rect.height <= 0 {
            return None;
        }
        self.swgl.make_current();
        // gleam `Gl::read_pixels` — allocates a `Vec<u8>` of w*h*4 and fills it from
        // the framebuffer. This is the EXACT call servo's
        // `Framebuffer::read_framebuffer_to_image` makes, and the readback is
        // LOAD-BEARING beyond a copy: SWGL's `glClear` is a *delayed* clear
        // (materialized lazily AT readback, not on `finish`) and SWGL's internal
        // default framebuffer is BGRA — `read_pixels(GL_RGBA, ..)` both RESOLVES the
        // delayed clear AND swizzles BGRA→RGBA. Borrowing `self.buffer` raw would skip
        // both (un-materialized zeros + channel-swapped), so this readback is the
        // correct path, NOT a redundant copy.
        let pixels =
            self.gl
                .read_pixels(rect.x, rect.y, rect.width, rect.height, RGBA, UNSIGNED_BYTE);
        Some(RgbaFrame {
            width: rect.width as u32,
            height: rect.height as u32,
            bytes: pixels,
        })
    }

    fn size(&self) -> (u32, u32) {
        (self.width.get(), self.height.get())
    }

    fn resize(&self, width: u32, height: u32) {
        if (width, height) == (self.width.get(), self.height.get()) {
            return;
        }
        self.width.set(width);
        self.height.set(height);
        self.buffer
            .borrow_mut()
            .resize((width * height * 4) as usize, 0);
        self.bind_default_framebuffer();
    }

    fn present(&self) {
        // Single-buffered into our own `Vec<u8>`: the pixels are already there the
        // instant WebRender draws. A real double-buffered context swaps here.
        self.gl.finish();
    }

    fn gleam_gl_api(&self) -> Rc<dyn Gl> {
        self.gl.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **THE LOAD-BEARING TEST: SWGL produces REAL RGBA8 pixels with no GPU.**
    ///
    /// This is the Stage-A de-risking proof. It constructs a `SwglRenderingContext`
    /// (CPU-only, no display), drives raw GL to clear the default framebuffer to a
    /// known color (standing in for a WebRender `Renderer::render` until the
    /// `libservo` feature wires the real one), reads the pixels back via the gleam
    /// `read_pixels` path, and asserts EVERY pixel equals the cleared color. If
    /// this passes, SWGL's C++ rasterizer compiled and rasterized into a buffer we
    /// own — "unaccelerated but real" is true on this host.
    #[test]
    fn swgl_clears_to_known_color_real_rgba8_pixels() {
        const W: u32 = 64;
        const H: u32 = 48;
        // The color we'll clear to (RGBA, 0..=255): a distinctive non-trivial one.
        const R: u8 = 0x12;
        const G: u8 = 0x34;
        const B: u8 = 0x56;
        const A: u8 = 0x78;

        // Serialize on the process-wide SWGL current-context lock for the whole
        // create→draw→read sequence (SWGL's `ctx` is a global, gl.cc:898).
        let frame = with_gl(|| {
            let ctx = SwglRenderingContext::new(W, H);
            ctx.make_current();
            ctx.prepare_for_rendering();

            // Drive the SWGL GL: set the clear color (normalized 0..1) and clear the
            // color buffer. This is real CPU rasterization into our buffer.
            let gl = ctx.gleam_gl_api();
            gl.clear_color(
                R as f32 / 255.0,
                G as f32 / 255.0,
                B as f32 / 255.0,
                A as f32 / 255.0,
            );
            gl.clear(gl::COLOR_BUFFER_BIT);
            ctx.present();

            // Read the pixels back — REAL RGBA8 out of the CPU rasterizer.
            ctx.read_frame()
        });

        assert_eq!(frame.width, W);
        assert_eq!(frame.height, H);
        assert_eq!(
            frame.bytes.len(),
            (W * H * 4) as usize,
            "RGBA8 = 4 bytes/pixel"
        );

        // Every pixel must be the cleared color.
        for y in 0..H {
            for x in 0..W {
                assert_eq!(
                    frame.pixel(x, y),
                    (R, G, B, A),
                    "pixel ({x},{y}) must be the SWGL-cleared color"
                );
            }
        }
    }

    /// A second, harder frame: fill the background one color, then fill a sub-rect
    /// a DIFFERENT color — proving SWGL does region-selective rasterization (the
    /// basis of compositor tiles), not just a uniform fill.
    ///
    /// The sub-rect uses SWGL's native immediate region-fill,
    /// [`swgl::Context::clear_color_rect`] (→ `ClearColorRect` → `ClearTexSubImage`,
    /// `gl.cc:2770`), NOT `glClear` under `GL_SCISSOR_TEST`. This is deliberate and
    /// load-bearing: SWGL's `Clear` is a *delayed* clear (`enable_delayed_clear`,
    /// `gl.cc:461`; materialized lazily on `prepare_texture` at readback), and a
    /// scissored `glClear` issued while a prior full delayed-clear is still pending
    /// takes the `force_clear(skip=scissor)` path (`gl.cc:2533`) which marks the
    /// box rows cleared while SKIPPING the box columns — leaving the box interior
    /// unwritten (reads back transparent-black). `clear_color_rect` sidesteps the
    /// delayed-clear bookkeeping with an immediate sub-image write — and it is
    /// exactly the primitive a tile compositor uses for a region fill. (The
    /// full-framebuffer delayed `glClear` path is proven correct by
    /// [`swgl_clears_to_known_color_real_rgba8_pixels`] above.)
    #[test]
    fn swgl_subrect_is_a_distinct_color() {
        const W: u32 = 32;
        const H: u32 = 32;
        let frame = with_gl(|| {
            let ctx = SwglRenderingContext::new(W, H);
            ctx.make_current();
            ctx.prepare_for_rendering();
            let gl = ctx.gleam_gl_api();
            let swgl = ctx.swgl_context();

            // Background: opaque red (full-framebuffer delayed clear, resolved on read).
            gl.clear_color(1.0, 0.0, 0.0, 1.0);
            gl.clear(gl::COLOR_BUFFER_BIT);

            // An 8x8 box at (4,4): opaque green, via SWGL's immediate region fill on
            // the default framebuffer (FBO 0). This forces the background red to
            // materialize outside the box and writes green inside — region-selective.
            swgl.clear_color_rect(0, 4, 4, 8, 8, 0.0, 1.0, 0.0, 1.0);
            ctx.present();
            ctx.read_frame()
        });

        // Inside the box (e.g. (5,5)) is green; outside (e.g. (0,0), (20,20)) is red.
        assert_eq!(frame.pixel(5, 5), (0, 255, 0, 255), "the sub-rect is green");
        assert_eq!(
            frame.pixel(0, 0),
            (255, 0, 0, 255),
            "corner is background red"
        );
        assert_eq!(
            frame.pixel(20, 20),
            (255, 0, 0, 255),
            "outside the box is red"
        );
    }

    /// The pixels→digest bind is deterministic and content-sensitive: two
    /// different frames hash to different `content_digest`s, the same frame to the
    /// same — the property the compositor's F3 closure relies on.
    #[test]
    fn content_digest_binds_the_real_pixels() {
        let a = RgbaFrame {
            width: 1,
            height: 1,
            bytes: vec![1, 2, 3, 4],
        };
        let b = RgbaFrame {
            width: 1,
            height: 1,
            bytes: vec![1, 2, 3, 5],
        };
        assert_eq!(
            a.content_digest(),
            a.content_digest(),
            "digest is a function"
        );
        assert_ne!(
            a.content_digest(),
            b.content_digest(),
            "different pixels ⇒ different digest"
        );
    }
}
