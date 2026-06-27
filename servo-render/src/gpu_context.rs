//! The HARDWARE-GL `RenderingContext` (route a of the dual backend) — OPT-IN behind
//! the `libservo` feature, alongside [`crate::webview::ServoSwglContext`] (the
//! software SWGL fallback). See `docs/desktop-os-research/SERVO-INTERACTIVE.md §4`.
//!
//! ## What this is (route a — the tractable first GPU step)
//!
//! [`ServoGpuContext`] is a real servo `paint_api::rendering_context::RenderingContext`
//! whose GL is a **surfman hardware-GL context** rendering into an offscreen surface,
//! with a `glReadPixels` readback at the present boundary that yields the same
//! [`RgbaFrame`] the SWGL path produces. It is, structurally, servo's own
//! `SoftwareRenderingContext` (`servo-paint-api`'s `rendering_context.rs`) with ONE
//! difference: it asks the surfman `Connection` for [`create_hardware_adapter`]
//! (the GPU) instead of `create_software_adapter` (Mesa/llvmpipe). Everything
//! downstream is identical — WebRender draws through the `gleam::Gl` the context
//! yields, and the rendered tile flows to the same compositor `present(region,
//! content_digest)` gate. The verification story does not change; only the renderer's
//! `gleam::Gl` differs (`SERVO-INTERACTIVE.md §4.1`).
//!
//! [`create_hardware_adapter`]: surfman::Connection::create_hardware_adapter
//!
//! ## Route (a) vs route (b)
//!
//! This is route (a): accelerated layout/paint on the GPU, then ONE `glReadPixels`
//! copy at the present boundary to produce the tile for the compositor gate. Route
//! (b) — zero-readback, WebRender rendering directly into a gpui-composited GPU
//! texture — is the fluid end-state whose hard part lives in the gpui fork (a
//! GPU-texture-source element + device sharing), NOT here; servo will render into
//! whatever `gleam::Gl` it is given. See `SERVO-INTERACTIVE.md §4.2`.
//!
//! ## Runtime selection (`gpu_available()` / [`make_rendering_context`])
//!
//! [`gpu_available`] probes whether a hardware GL device can be opened on this host
//! (a `Connection::new()` + `create_hardware_adapter()` + `create_device()` that
//! succeeds). [`make_rendering_context`] returns the hardware [`ServoGpuContext`] when
//! it can, else falls back to the software SWGL [`ServoSwglContext`]. The SWGL path is
//! therefore never removed — it is the load-bearing guarantee for the no-GPU
//! environments SERVO-ON-SEL4 targets (an seL4 PD with no GPU driver VM, a headless
//! server), and the GPU path is an acceleration layered above the same seam.

#![cfg(feature = "libservo")]

use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::sync::Arc;

use dpi::PhysicalSize;
use euclid::Size2D;
use gleam::gl::{self, Gl};
use image::RgbaImage;
use paint_api::rendering_context::{
    Error as PaintError, RenderingContext as ServoRenderingContext,
};
use surfman::chains::{PreserveBuffer, SwapChain};
use surfman::{
    Adapter, Connection, Context, ContextAttributeFlags, ContextAttributes, Device, GLApi,
    SurfaceAccess, SurfaceType,
};
use webrender_api::units::DeviceIntRect;

use crate::swgl_context::RgbaFrame;

/// The inner surfman hardware-GL plumbing — a faithful local re-creation of
/// servo-paint-api's private `SurfmanRenderingContext`, against a HARDWARE adapter
/// (the only structural difference from servo's `SoftwareRenderingContext`).
struct SurfmanHardware {
    gleam_gl: Rc<dyn Gl>,
    device: RefCell<Device>,
    context: RefCell<Context>,
}

impl SurfmanHardware {
    /// Open a hardware-GL surfman context for `adapter` on `connection`. Mirrors
    /// servo-paint-api's `SurfmanRenderingContext::new` (the `gleam_gl` load path is
    /// byte-for-byte the same; we omit the `glow` build until the compositor blit
    /// path needs it — see [`ServoGpuContext::glow_gl_api`]).
    fn new(connection: &Connection, adapter: &Adapter) -> Result<Self, PaintError> {
        let device = connection.create_device(adapter)?;

        let flags = ContextAttributeFlags::ALPHA
            | ContextAttributeFlags::DEPTH
            | ContextAttributeFlags::STENCIL;
        let gl_api = connection.gl_api();
        let version = match &gl_api {
            GLApi::GLES => surfman::GLVersion { major: 3, minor: 0 },
            GLApi::GL => surfman::GLVersion { major: 3, minor: 2 },
        };
        let context_descriptor =
            device.create_context_descriptor(&ContextAttributes { flags, version })?;
        let context = device.create_context(&context_descriptor, None)?;

        // The SAME gleam-load path servo's `SurfmanRenderingContext::new` uses: load
        // the GL function pointers from the surfman device's `get_proc_address`.
        let gleam_gl = match gl_api {
            GLApi::GL => unsafe {
                gl::GlFns::load_with(|name| device.get_proc_address(&context, name))
            },
            GLApi::GLES => unsafe {
                gl::GlesFns::load_with(|name| device.get_proc_address(&context, name))
            },
        };

        Ok(SurfmanHardware {
            gleam_gl,
            device: RefCell::new(device),
            context: RefCell::new(context),
        })
    }

    /// Create an offscreen `Generic` surface (no window/widget — a pixel-sized GPU
    /// surface), bind it to the context, and make the context current. This is the
    /// windowless analogue of servo's `SoftwareRenderingContext::new` surface setup
    /// (which uses the same `SurfaceType::Generic`).
    fn create_generic_surface(&self, size: PhysicalSize<u32>) -> Result<(), PaintError> {
        let surfman_size = Size2D::new(size.width as i32, size.height as i32);
        let surface = {
            let device = self.device.borrow();
            let context = self.context.borrow();
            device.create_surface(
                &context,
                SurfaceAccess::GPUOnly,
                SurfaceType::Generic { size: surfman_size },
            )?
        };
        {
            let device = self.device.borrow();
            let mut context = self.context.borrow_mut();
            device
                .bind_surface_to_context(&mut context, surface)
                .map_err(|(err, mut surface)| {
                    let _ = device.destroy_surface(&mut context, &mut surface);
                    err
                })?;
        }
        self.make_current()
    }

    fn create_attached_swap_chain(&self) -> Result<SwapChain<Device>, PaintError> {
        let device = self.device.borrow_mut();
        let mut context = self.context.borrow_mut();
        SwapChain::create_attached(&device, &mut context, SurfaceAccess::GPUOnly)
    }

    fn make_current(&self) -> Result<(), PaintError> {
        let device = self.device.borrow();
        let context = self.context.borrow();
        device.make_context_current(&context)
    }

    /// The bound surface's framebuffer object (the FBO WebRender renders into and we
    /// read back). `0` if none is bound — the default framebuffer.
    fn framebuffer_id(&self) -> gl::GLuint {
        let device = self.device.borrow();
        let context = self.context.borrow();
        device
            .context_surface_info(&context)
            .unwrap_or(None)
            .and_then(|info| info.framebuffer_object)
            .map_or(0, |fb| fb.0.get())
    }
}

impl Drop for SurfmanHardware {
    fn drop(&mut self) {
        let device = self.device.borrow();
        let mut context = self.context.borrow_mut();
        let _ = device.destroy_context(&mut context);
    }
}

/// **THE HARDWARE-GL RENDERING CONTEXT (route a).** A surfman hardware-GL context
/// rendering into an offscreen `Generic` surface; servo's WebRender draws through its
/// [`gleam::Gl`], and [`read_to_image`](ServoRenderingContext::read_to_image) does a
/// `glReadPixels` (the route-a readback) to produce the [`RgbaFrame`] tile the
/// compositor gate hashes.
///
/// Constructed via [`Self::new`] (errors if no hardware device is available — the
/// caller falls back to SWGL via [`make_rendering_context`]).
pub struct ServoGpuContext {
    size: Cell<PhysicalSize<u32>>,
    inner: SurfmanHardware,
    swap_chain: SwapChain<Device>,
}

impl ServoGpuContext {
    /// Open a hardware-GL context of `width × height`. Mirrors servo's
    /// `SoftwareRenderingContext::new`, but selects the HARDWARE adapter
    /// (`create_hardware_adapter` — the GPU) rather than the software one. Returns the
    /// surfman `Error` if no hardware device/surface can be created (no GPU, no display
    /// connection) — the signal [`make_rendering_context`] uses to fall back to SWGL.
    pub fn new(width: u32, height: u32) -> Result<Self, PaintError> {
        let size = PhysicalSize::new(width, height);
        let connection = Connection::new()?;
        // THE ONE DIFFERENCE FROM `SoftwareRenderingContext`: the hardware adapter.
        let adapter = connection.create_hardware_adapter()?;
        let inner = SurfmanHardware::new(&connection, &adapter)?;
        inner.create_generic_surface(size)?;
        let swap_chain = inner.create_attached_swap_chain()?;
        Ok(ServoGpuContext {
            size: Cell::new(size),
            inner,
            swap_chain,
        })
    }

    /// Read the whole framebuffer back as an owned [`RgbaFrame`] — the direct
    /// (non-trait) accessor mirroring [`crate::webview::ServoSwglContext::inner`]'s
    /// `read_frame`, so the GPU path feeds the compositor seam the same type.
    pub fn read_frame(&self) -> Option<RgbaFrame> {
        let size = self.size.get();
        let rect = DeviceIntRect::from_origin_and_size(
            euclid::Point2D::origin(),
            Size2D::new(size.width as i32, size.height as i32),
        );
        let img = ServoRenderingContext::read_to_image(self, rect)?;
        let (w, h) = (img.width(), img.height());
        Some(RgbaFrame {
            width: w,
            height: h,
            bytes: img.into_raw(),
        })
    }
}

impl ServoRenderingContext for ServoGpuContext {
    fn prepare_for_rendering(&self) {
        let fb = self.inner.framebuffer_id();
        self.inner.gleam_gl.bind_framebuffer(gl::FRAMEBUFFER, fb);
    }

    fn read_to_image(&self, source_rectangle: DeviceIntRect) -> Option<RgbaImage> {
        let gl = &self.inner.gleam_gl;
        let fb = self.inner.framebuffer_id();
        gl.bind_framebuffer(gl::FRAMEBUFFER, fb);
        // Work around the OSMesa/driver VAO-state bug servo's own readback guards
        // against (`read_framebuffer_to_image`): unbind any vertex array first.
        gl.bind_vertex_array(0);

        let mut pixels = gl.read_pixels(
            source_rectangle.min.x,
            source_rectangle.min.y,
            source_rectangle.width(),
            source_rectangle.height(),
            gl::RGBA,
            gl::UNSIGNED_BYTE,
        );
        if pixels.is_empty() {
            return None;
        }

        // GL's framebuffer origin is bottom-left; flip vertically so the tile is
        // upright (row 0 = top) — the SAME flip servo's `read_framebuffer_to_image`
        // does, kept here so the GPU tile matches the SWGL/PNG convention.
        //
        // IN-PLACE: swap symmetric row pairs through one small per-row scratch buffer
        // (`stride` bytes), instead of cloning the WHOLE `w*h*4` framebuffer. The two
        // halves never alias, so `split_at_mut` hands out disjoint mutable slices the
        // borrow checker accepts; the middle row (odd height) is already in place.
        let rect = source_rectangle.to_usize();
        let stride = rect.width() * 4;
        if stride > 0 && rect.height() > 1 {
            let rows = rect.height();
            let mut scratch = vec![0u8; stride];
            for y in 0..rows / 2 {
                let top = y * stride;
                let bot = (rows - y - 1) * stride;
                // top..top+stride and bot..bot+stride are disjoint (y < rows-y-1).
                let (head, tail) = pixels.split_at_mut(bot);
                let top_row = &mut head[top..top + stride];
                let bot_row = &mut tail[..stride];
                scratch.copy_from_slice(top_row);
                top_row.copy_from_slice(bot_row);
                bot_row.copy_from_slice(&scratch);
            }
        }

        RgbaImage::from_raw(
            source_rectangle.width() as u32,
            source_rectangle.height() as u32,
            pixels,
        )
    }

    fn size(&self) -> PhysicalSize<u32> {
        self.size.get()
    }

    fn resize(&self, size: PhysicalSize<u32>) {
        if self.size.get() == size {
            return;
        }
        self.size.set(size);
        let device = self.inner.device.borrow_mut();
        let mut context = self.inner.context.borrow_mut();
        let s = Size2D::new(size.width as i32, size.height as i32);
        let _ = self.swap_chain.resize(&device, &mut context, s);
    }

    fn present(&self) {
        let device = self.inner.device.borrow_mut();
        let mut context = self.inner.context.borrow_mut();
        let _ = self
            .swap_chain
            .swap_buffers(&device, &mut context, PreserveBuffer::No);
    }

    fn make_current(&self) -> Result<(), PaintError> {
        self.inner.make_current()
    }

    fn gleam_gl_api(&self) -> Rc<dyn Gl> {
        self.inner.gleam_gl.clone()
    }

    fn glow_gl_api(&self) -> Arc<glow::Context> {
        // Build a real `glow::Context` over the surfman device's `get_proc_address`
        // — the SAME path servo's `SurfmanRenderingContext::new` uses for its glow.
        // (Unlike SWGL, a hardware surfman context exposes a genuine proc loader, so
        // this needs no `dlsym` shim.) The context must be current for glow's
        // immediate `GetString(GL_VERSION)` probe.
        let _ = self.inner.make_current();
        let device = self.inner.device.borrow();
        let context = self.inner.context.borrow();
        let ctx = unsafe {
            glow::Context::from_loader_function(|name| device.get_proc_address(&context, name))
        };
        Arc::new(ctx)
    }

    fn connection(&self) -> Option<surfman::Connection> {
        Some(self.inner.device.borrow().connection())
    }
}

/// Probe whether a HARDWARE GL device can be opened on this host — `true` on a native
/// desktop with a GPU, `false` inside an seL4 PD with no GPU driver VM, on a headless
/// server, or anywhere `create_hardware_adapter()` / `create_device()` fails. This is
/// the `gpu_available()` of `SERVO-INTERACTIVE.md §4.3`; [`make_rendering_context`]
/// branches on it.
///
/// Cheap and side-effect-free: it opens a connection + hardware device and drops them,
/// allocating no surface and creating no GL context.
pub fn gpu_available() -> bool {
    (|| -> Result<(), PaintError> {
        let connection = Connection::new()?;
        let adapter = connection.create_hardware_adapter()?;
        let _device = connection.create_device(&adapter)?;
        Ok(())
    })()
    .is_ok()
}

/// The render-target a [`crate::webview::ServoSwglContext`]-using caller selects at
/// runtime: the hardware [`ServoGpuContext`] when a GPU is available, else the
/// software SWGL [`crate::webview::ServoSwglContext`] fallback. Returned as
/// `Rc<dyn RenderingContext>` — the exact type `WebViewBuilder::new(servo, _)` takes —
/// so the SAME embed code (`render_url_on_servo` et al.) drives either backend. This
/// is the ONLY new branch (`SERVO-INTERACTIVE.md §4.3`); everything downstream (the
/// cap-gate, `present_frame`, the scene teeth) is shared.
pub fn make_rendering_context(width: u32, height: u32) -> Rc<dyn ServoRenderingContext> {
    match ServoGpuContext::new(width, height) {
        Ok(gpu) => Rc::new(gpu),
        Err(_) => Rc::new(crate::webview::ServoSwglContext::new(width, height)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `gpu_available()` does not panic and returns a definite bool on this host. The
    /// downstream selection ([`make_rendering_context`]) is correct for EITHER answer
    /// — this just exercises the probe.
    #[test]
    fn gpu_available_is_a_definite_probe() {
        let available = gpu_available();
        println!("GPU_PROBE gpu_available={available}");
    }

    /// **THE GPU-CONTEXT SPIKE (route a):** if a hardware GL device is available,
    /// build a [`ServoGpuContext`], drive its `gleam::Gl` to clear the framebuffer to
    /// a known color, and read the tile back via the route-a `glReadPixels` path —
    /// proving the hardware context produces real RGBA8 pixels into a tile the
    /// compositor gate can hash. If no GPU is available (seL4 PD / headless / CI box
    /// with no GL), the test documents the absence and SWGL stays the path (asserted
    /// by `make_rendering_context` falling back, exercised in
    /// `gpu_falls_back_to_swgl_when_unavailable`).
    ///
    /// Serialized on the SWGL process-wide GL lock so it does not race the SWGL tests
    /// (the host has ONE current-GL discipline across both backends).
    #[test]
    fn gpu_context_clears_to_known_color_or_documents_absence() {
        crate::swgl_context::with_gl(|| {
            const W: u32 = 64;
            const H: u32 = 48;
            const R: u8 = 0x12;
            const G: u8 = 0x34;
            const B: u8 = 0x56;
            const A: u8 = 0x78;

            let ctx = match ServoGpuContext::new(W, H) {
                Ok(ctx) => ctx,
                Err(e) => {
                    println!(
                        "GPU_SPIKE no hardware GL on this host ({e:?}) — SWGL remains the path"
                    );
                    return;
                }
            };

            ServoRenderingContext::make_current(&ctx).expect("hardware context current");
            ctx.prepare_for_rendering();
            let gl = ctx.gleam_gl_api();
            gl.clear_color(
                R as f32 / 255.0,
                G as f32 / 255.0,
                B as f32 / 255.0,
                A as f32 / 255.0,
            );
            gl.clear(gl::COLOR_BUFFER_BIT);
            gl.finish();

            let frame = ctx
                .read_frame()
                .expect("the hardware framebuffer reads back");
            assert_eq!(frame.width, W);
            assert_eq!(frame.height, H);
            assert_eq!(
                frame.bytes.len(),
                (W * H * 4) as usize,
                "RGBA8 = 4 bytes/pixel"
            );

            // Every pixel is the cleared color — real GPU rasterization into a tile.
            let mismatch = (0..(W * H) as usize).find(|&i| {
                let p = &frame.bytes[i * 4..i * 4 + 4];
                p != [R, G, B, A]
            });
            assert!(
                mismatch.is_none(),
                "every GPU-cleared pixel is the known color; first mismatch at idx {mismatch:?}"
            );
            println!(
                "GPU_SPIKE hardware-GL context cleared {W}x{H} to ({R:#x},{G:#x},{B:#x},{A:#x}) \
                 and read it back — route-a tile produced; digest={:#x}",
                frame.content_digest()
            );
        });
    }

    /// [`make_rendering_context`] always yields a usable context: the hardware one
    /// when a GPU is present, the SWGL fallback otherwise. Either way the returned
    /// `Rc<dyn RenderingContext>` reports the requested size — the runtime selection
    /// is transparent to the embed code.
    #[test]
    fn make_rendering_context_selects_a_usable_backend() {
        crate::swgl_context::with_gl(|| {
            const W: u32 = 32;
            const H: u32 = 24;
            let ctx = make_rendering_context(W, H);
            let _ = ServoRenderingContext::make_current(&*ctx);
            let size = ctx.size();
            assert_eq!(
                (size.width, size.height),
                (W, H),
                "selected backend honors the size"
            );
            println!(
                "BACKEND_SELECT gpu_available={} chosen_size={}x{}",
                gpu_available(),
                size.width,
                size.height
            );
        });
    }
}
