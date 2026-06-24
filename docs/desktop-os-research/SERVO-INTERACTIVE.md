# SERVO-INTERACTIVE — the live embedded WebView (input → re-render → tile) + the GPU/software dual backend

*The companion to [SERVO-ON-SEL4.md](SERVO-ON-SEL4.md). That doc closes **F3** —
real pixels from a confined renderer through the compositor-PD gate. This doc
covers the next two axes that turn that render from a STATIC snapshot into a LIVE
embedded surface:*

1. **Interactivity** — feeding input (scroll / click / move / keys) into a live
   `servo::WebView` and getting a fresh tile on change (the event → re-render →
   new tile loop), and
2. **The dual rendering backend** — the SOFTWARE SWGL path (CPU, no-GPU, the
   seL4 / headless-server guarantee) vs. a HARDWARE-GL path (GPU-accelerated on
   the native desktop), selected at runtime, both feeding the SAME
   backend-agnostic `present(region, content_digest)` compositor gate.

Both ride the single seam servo already exposes: the
`paint_api::rendering_context::RenderingContext` trait (`gleam::gl::Gl` underneath).
Nothing in the cap model, the scene teeth, or the digest-gate changes.

---

## 1. State today (verified in-tree)

- `servo-render/src/webview.rs` (feature `libservo`) wires a real `Servo` +
  `WebView` against the genuine `servo 0.1.1` API into a SWGL
  `RenderingContext` (`ServoSwglContext`), behind the real cap-gate
  (`CapGate: WebViewDelegate`). `render_url_on_servo` does
  `ServoBuilder → WebViewBuilder → load → spin_event_loop* → paint → read_to_image`
  and returns one `RgbaFrame`.
- `libservo` **builds and links** on this host (the `mozjs`/SpiderMonkey wall is
  passed — the rlibs are cached in `target/`). A clean `cargo build --features
  libservo` finishes in ~6–7 min; incremental rebuilds in ~1 min.
- The output `RgbaFrame` flows to `compositor_seam::present_frame` (the compositor
  gate) and to a gpui `img()` in `starbridge-v2/src/cockpit/panels_web.rs:657`.

**The gap this doc addresses:** that render was a one-shot snapshot — no events in,
no re-render, no scroll. And the only backend was CPU SWGL.

---

## 2. The interactivity API — what servo gives us (exact)

The live-input vocabulary is on `servo::WebView` (re-exported from
`embedder_traits`; verified against `servo 0.1.1` /
`servo-embedder-traits 0.1.0`):

```rust
// servo/webview.rs
impl WebView {
    pub fn notify_input_event(&self, event: InputEvent) -> InputEventId;
    pub fn notify_scroll_event(&self, scroll: Scroll, point: WebViewPoint);
    pub fn paint(&self);                       // render current tree into the RenderingContext
    pub fn resize(&self, new_size: PhysicalSize<u32>);
    pub fn set_page_zoom(&self, new_zoom: f32);
    pub fn focus(&self);
}
```

`InputEvent` (`servo-embedder-traits/input_events.rs`) is the full event algebra:

```rust
pub enum InputEvent {
    EditingAction(EditingActionEvent),   // Copy / Cut / Paste
    Ime(ImeEvent),
    Keyboard(KeyboardEvent),             // keyboard_types::KeyboardEvent (state, key, code, mods, …)
    MouseButton(MouseButtonEvent),       // { action: Down|Up, button: Left|…, point }
    MouseLeftViewport(MouseLeftViewportEvent),
    MouseMove(MouseMoveEvent),           // { point }
    Touch(TouchEvent),
    Wheel(WheelEvent),                   // { delta: WheelDelta{x,y,z,mode}, point }
}
```

Points are `WebViewPoint::{Device(DevicePoint), Page(Point2D<_,CSSPixel>)}`; scroll
deltas are `Scroll::{Delta(WebViewVector), Start, End}` where
`WebViewVector::{Device(DeviceVector2D), Page(_)}`.

**The redraw loop** (verified against servo's upstream `examples/winit_minimal.rs`):
`notify_input_event` routes *point-bearing* events to the **paint thread first for
hit-testing**, then to the constellation/script threads; layout/script/paint run on
their own threads and produce a new built frame asynchronously. The embedder then
`spin_event_loop()`s to pump those threads and calls `webview.paint()` +
`rendering_context.present()` to get the post-input frame. A winit embedder is paced
by OS `RedrawRequested` events; headless we pump `spin_event_loop` ourselves in a
bounded loop. **This is the same loop the initial page-load already uses** — the
only addition is delivering input events between two paints.

### The `notify_new_frame_ready` signal

Our `CapGate` already implements `notify_new_frame_ready` (sets a `frame_ready`
flag). A real embedder driven by an event loop wakes its proxy here and schedules a
repaint; this is the "re-render on change" trigger — servo tells us a fresh frame is
ready to read back, rather than us polling blindly.

---

## 3. The spike — EXECUTED (input → re-render → two differing tiles)

`servo-render/src/webview.rs` now carries the live-input wiring:

- **`WebInput`** — the embedder-side event lowering (`Scroll{x,y,dx,dy}`,
  `Click{x,y}`, `MouseMove{x,y}`); an embedder maps its native events to these.
- **`apply_input(&WebView, WebInput)`** — lowers a `WebInput` onto servo's
  `notify_input_event` / `notify_scroll_event` (the exact `winit_minimal`
  lowering: `Click` = `MouseButton{Down}` then `{Up}`; `Scroll` = a `Wheel`
  event + a high-level `Scroll::Delta`).
- **`render_url_then_input_on_servo(...)`** — load → paint **frame A** → deliver
  `input` → pump → paint **frame B** → return `(A, B)`. The headless analogue of
  the winit window loop.

**Proof (test `a_scroll_input_re_renders_the_webview_to_a_different_tile`,
`--features libservo`, GREEN):** a `data:` page taller than the 200px viewport — a
600px red block stacked on a 600px lime block. Frame A is the top (red); a 450px
downward scroll, then frame B is the second block (lime):

```
INTERACTIVE_SPIKE pre_scroll_red_px=48000 post_scroll_lime_px=48000
                  digest_a=0x4b691203fa8afb40 digest_b=0x61b6f0fcd600e4ab
```

48000 = the full 240×200 viewport. The whole viewport flips red → lime and the
content digests differ — the live `WebView` genuinely re-rendered in response to a
scroll input. **This is the move from static snapshot to live embedded webview,
proven by two differing tiles.** Click and pointer-move are wired through the same
`apply_input`.

### What remains to make it FLUID in the cockpit (the wiring, not new engine work)

The spike proves the engine half. To intersperse a live web pane into the gpui
cockpit (`panels_web.rs`), the remaining work is plumbing:

1. **A persistent `Servo` + `WebView` per web pane** (not the per-call build the
   spike uses). Servo's `servo_config::opts` is a process-wide `OnceCell`, so there
   is **at most one `Servo` per process** — hold ONE engine (cf.
   `CapGatedHttpEngine`) and build a `WebView` per pane on it.
2. **An event bridge**: gpui's pane delivers `MouseDown/Up/Move/ScrollWheel` over
   the pane bounds → lower to `WebInput` → `apply_input`. gpui already hit-tests to
   the element; translate the local coords to the WebView's device point.
3. **A repaint trigger**: on `notify_new_frame_ready`, read back the SWGL frame and
   `cx.notify()` the gpui view so `img()` re-paints the new tile. (Or drive a small
   timer that spins + repaints while the pane is focused.)
4. **`resize`** when the pane bounds change → `WebView::resize(PhysicalSize)`.

None of this is new engine capability — it is the same `apply_input` + read-back +
`cx.notify()` loop, bounded by the pane's focus. The CPU-readback cost per frame is
the motivation for the GPU backend below.

---

## 4. The dual rendering backend — GPU-accelerated desktop + SWGL fallback

The owner's target: **GPU-accelerated servo on the native desktop**, with the
current SWGL software path kept as the **no-GPU fallback** (seL4-embedded /
headless server). This is the SAME `RenderingContext` / `gleam::Gl` seam — only the
context's GL implementation changes.

### 4.1 The seam is backend-agnostic by construction

Servo renders **everything** through whatever `Rc<dyn RenderingContext>` the
`WebViewBuilder` is handed; WebRender draws via the `gleam::gl::Gl` that context
yields (`gleam_gl_api()`) and/or its `glow::Context` (`glow_gl_api()`). The
compositor-PD's `present(region, content_digest)` gate **hashes a tile** and admits
it through the unchanged T1/T2/T3 teeth — it does not care whether those bytes came
from a CPU `Vec<u8>` or a GPU texture readback. **So the verification story is
identical across backends; only the renderer's `gleam::Gl` differs.**

| Backend  | `RenderingContext` impl         | GL provider                          | Use                                            |
|----------|---------------------------------|--------------------------------------|------------------------------------------------|
| Software | `ServoSwglContext` (today)      | `swgl::Context` (CPU, `impl Gl`)     | seL4 PD, headless server, no-GPU — the guarantee |
| Hardware | `ServoGpuContext` (to build)    | a real GL/Metal/wgpu-backed `gleam::Gl` | native desktop — fluid, accelerated            |

### 4.2 The hardware-GL `RenderingContext` — two shapes

WebRender (which servo's `servo-paint` drives) is a `gleam::gl::Gl` /
`glow::Context` consumer. A GPU `RenderingContext` must hand servo-paint a GL
context that draws into a GPU surface:

**(a) The standalone hardware-GL context (the lower-risk first GPU step).**
Servo ships `SoftwareRenderingContext` (surfman/Mesa) and a
`WindowRenderingContext` (surfman over a real GL surface) — and surfman already
backs a hardware GL context on macOS (CGL/Metal via ANGLE) and Linux (EGL/GLX).
servo's own `examples/winit_minimal.rs` uses `WindowRenderingContext`. So the
*minimal* GPU path is to **use servo's surfman-backed hardware `RenderingContext`
against an offscreen FBO**, then read back the texture to a tile for the compositor
gate. This is GPU rasterization with a CPU readback at the present boundary — fully
accelerated layout/paint, one copy at the seam. Risk: low (it is servo's own
shipping path); cost: the readback copy per frame.

**(b) The gpui-shared GPU surface (the FLUID ideal — zero readback).**
gpui renders via Metal/blade on macOS (a wgpu-shaped GPU stack). The ideal is for
WebRender to render **into a GPU texture gpui composites directly**, so the web
content and the gpui chrome live on ONE GPU surface and intersperse with no CPU
round-trip. The requirement: a `RenderingContext` whose `gleam::Gl` / `glow` draws
into a texture **gpui can sample**. Two sub-routes:

  - **Shared device, shared texture.** If gpui exposes its underlying GPU device
    (Metal `MTLDevice` / wgpu `Device`), build a GL context (via ANGLE-on-Metal, or
    a wgpu-backed `glow`) on that **same device**, render WebRender into a texture
    allocated on it, and hand gpui that texture id to composite. No readback. This
    is the "share gpui's wgpu device → WebRender into a GPU texture gpui composites
    directly" goal. **Blocker to verify:** gpui (the `emberian/zed` fork) must
    expose its device + accept an externally-allocated texture as an `img()`-like
    source. gpui's `RenderImage` path is CPU-backed today; a GPU-texture source is a
    gpui-fork addition (a `GpuSurfaceSpecifier` element). This is the real
    engineering — it lives in the gpui fork, NOT in servo-render.
  - **glow-over-wgpu.** `glow` can target a wgpu context; if WebRender accepts the
    `glow::Context` path end-to-end (our `ServoSwglContext::glow_gl_api` already
    proves we can synthesize a `glow::Context` over a chosen GL — there we point it
    at SWGL's symbols; here we'd point it at a wgpu-backed GL), WebRender renders
    into a wgpu texture shared with gpui's wgpu device.

**Honest seam note.** Route (a) is the tractable first GPU win (accelerated render,
one readback). Route (b) is the fluid end-state and its hard part is **on the gpui
side** (a GPU-texture-source element + device sharing), not on servo's — servo will
render into any `gleam::Gl` we give it. The compositor digest-gate is unchanged
either way (it hashes the texture's tile; F1 last-hop attestation still binds the
scanned-out pixels — see SERVO-ON-SEL4 §3.2).

### 4.3 Runtime selection

```text
fn make_rendering_context(w, h) -> Rc<dyn RenderingContext> {
    if gpu_available() {            // a GL/Metal/wgpu device opened OK
        ServoGpuContext::new(w, h)  // hardware path — native desktop
    } else {
        ServoSwglContext::new(w, h) // SOFTWARE fallback — seL4 PD / headless / no-GPU
    }
}
```

`gpu_available()` = "can we open a hardware GL/Metal/wgpu device?" — false inside an
seL4 PD with no GPU driver VM, false on a headless server, true on the native
desktop. The selection is the ONLY new branch; everything downstream
(`WebViewBuilder`, the cap-gate, `present_frame`, the scene teeth) is shared. The
SWGL path is therefore **never removed** — it is the load-bearing guarantee for the
environments SERVO-ON-SEL4 targets, and the GPU path is an *acceleration* layered
above the same seam.

### 4.4 The build sketch for `ServoGpuContext` (route a, the tractable GPU step)

A new `servo-render/src/gpu_context.rs` (feature `libservo` + a new `gpu` feature),
mirroring `ServoSwglContext`:

```rust
pub struct ServoGpuContext { surfman_ctx: surfman::Context, device: surfman::Device, fbo: GLuint, … }

impl paint_api::rendering_context::RenderingContext for ServoGpuContext {
    fn make_current(&self) -> Result<(), Error> { self.device.make_context_current(&self.surfman_ctx) }
    fn gleam_gl_api(&self)  -> Rc<dyn gleam::gl::Gl> { /* gleam over the surfman hardware GL */ }
    fn glow_gl_api(&self)   -> Arc<glow::Context>     { /* glow from the surfman get_proc_address */ }
    fn connection(&self)    -> Option<surfman::Connection> { Some(self.device.connection()) }
    fn read_to_image(&self, rect) -> Option<RgbaImage> { /* glReadPixels from the FBO → tile (route a) */ }
    fn size(&self) / resize(&self) / present(&self) / prepare_for_rendering(&self) { /* surfman surface */ }
}
```

surfman already provides `Connection::new()` → `create_device()` →
`create_context()` against the host's hardware GL (CGL/Metal on macOS, EGL/GLX on
Linux); servo's `WindowRenderingContext` is the working template. `read_to_image`
(`glReadPixels`) gives route (a)'s tile for the compositor gate. Route (b) replaces
that readback with handing gpui the texture id directly — a gpui-fork change.

---

## 5. The concrete next step

1. **Cockpit live pane** (interactivity, no new engine work): hold ONE persistent
   `Servo` engine + a per-pane `WebView`, bridge gpui pane events → `apply_input`,
   repaint on `notify_new_frame_ready`. This makes the web pane scroll/click LIVE
   in the cockpit on the existing SWGL backend.
2. **GPU route (a)**: build `ServoGpuContext` (surfman hardware GL + FBO readback),
   add `gpu_available()` selection. Accelerated layout/paint, one readback at the
   present boundary; SWGL stays the fallback.
3. **GPU route (b)** (the fluid ideal): a gpui-fork `GpuSurfaceSpecifier` element +
   device sharing so WebRender renders into a gpui-composited texture — zero
   readback. The hard part is in the gpui fork; servo renders into whatever
   `gleam::Gl` it is given.

All three keep the cap-gate, the `RgbaFrame`/tile type at the present boundary, and
the compositor `present(region, content_digest)` teeth UNCHANGED. The verification
story (and F1/F2/F3 framing) is identical across backends.
