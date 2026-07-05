# gpui offscreen render — the real renderer, no GPU (the LIVE cockpit on glass, on seL4)

The seL4 `qemu_virt_aarch64` machine has no GPU, so starbridge-v2's gpui (wgpu → Vulkan)
cockpit cannot present to a window there. This is the path that renders a gpui Scene anyway —
**gpui → software Vulkan (lavapipe) → an offscreen texture → RGBA readback → the seL4
compositor framebuffer** — so a real gpui render is a Mode inside the VM, beside the live
image viewer. The blitted frame is the **LIVE `cockpit::Cockpit` element tree** (over the
fully-seeded `world::demo_world` image), captured headless and baked into the PD — see
§"The live element tree" below. (The first bring-up used a hand-built cockpit-*shaped* Scene
through this exact renderer; that swap is now closed.)

## LANDED — a real gpui render is on the seL4 framebuffer (cockpit-shaped; TAB to it)

The weld is closed end-to-end. The deos-image PD (`sel4/dregg-pd/deos-image/`) now has
**two live modes on one framebuffer**, switched with **TAB**:
- `Mode::Image` — the Pharo/Smalltalk object browser of the six real deos cells.
- `Mode::Cockpit` — a **real gpui render of the LIVE `cockpit::Cockpit` element tree** (the
  WORLD/SHELL/REFLECT layout, via `starbridge-v2/src/main.rs::render_cockpit_headless` — the
  hand-built cockpit-shaped stand-in the first bring-up used is now swapped out, see "The live
  element tree" below), blitted onto the ramfb framebuffer QEMU scans out (`src/cockpit_frame.rs`).

The cockpit frame is rendered at the framebuffer's exact `800×600` by the **actual gpui
renderer** (`gpui_wgpu::WgpuRenderer::render_scene_to_image`, the patch below) on lavapipe
(llvmpipe, `type=Cpu`, no GPU/window) on the render host — `21` quads + `322` monochrome glyph
sprites, the title bar + the three master columns (WORLD/SHELL/REFLECT) + the four-substance
tiles + the status bar — then baked into the `#![no_std]` PD as raw RGBA8
(`src/cockpit_frame.rgba`, 1.92 MiB) exactly as `image_data.rs` bakes real cells. At blit
time the PD swizzles RGBA→XRGB8888 straight into the mapped framebuffer. A keypress (TAB,
evdev 15) → the PD's `notified()` handler toggles the mode and repaints — real gpui pixels
on glass.

Reproduce + capture (both modes to PNG): `cd sel4 && make capture-image-modes` — boots
headless, screendumps the live image, `send-key TAB` over QMP, screendumps the cockpit.
Evidence: `patches/cockpit-on-sel4-framebuffer.png` (the cockpit-shaped gpui render, scanned
out of seL4 ramfb) + `patches/deos-image-on-sel4-framebuffer.png` (the cell browser, same boot) +
`patches/cockpit-render-800x600.png` (the render-host render). Serial confirms
`ramfb CONFIGURED: addr=0x60600000 XRGB8888 800x600` then `-> MODE: the starbridge-v2 COCKPIT`.

## The live element tree (the swap, closed)

The blitted frame is the LIVE `cockpit::Cockpit` element tree, not a hand-built look-alike.
The mechanism is gpui's own headless capture path, with the missing Linux renderer added:

- **Entry** — `starbridge-v2/src/main.rs::render_cockpit_headless` (`--render-cockpit <out>`,
  behind a new `headless-render` feature). It builds a `gpui::HeadlessAppContext` over
  `TestPlatform`, opens a non-shown 800×600 `Window` whose ROOT is the real `Cockpit` over the
  fully-seeded `world::demo_world` image, drives a frame (`open_window` draws; `refresh()` +
  `run_until_parked()`), then `capture_screenshot` → `Window::render_to_image` resolves that
  frame's `gpui::Scene` and renders it offscreen. `cockpit::Cockpit`'s `shell::Scene` (a
  window-manager model) resolves into a real `gpui::Scene` exactly because it now runs inside a
  live (headless) `Window` — the thing the hand-built bring-up stood in for.
- **The renderer** — `Window::render_to_image` routes through a `PlatformHeadlessRenderer`. The
  offscreen patch grew the Linux one: `gpui_wgpu::WgpuHeadlessRenderer` (wrapping a surfaceless
  `WgpuRenderer` + the new `render_scene` / existing `render_scene_to_image`), surfaced via
  `gpui_linux::current_headless_renderer` and `gpui_platform::current_headless_renderer` on
  Linux (the Metal headless renderer is the macOS counterpart). The `TestWindow`'s sprite atlas
  IS this renderer's atlas, so glyphs the element tree rasterizes during paint resolve against
  the very atlas the capture samples.
- **Scale** — gpui's headless `TestWindow` reports a fixed 2× scale, so 800×600 logical renders
  at 1600×1200 device px (the full layout) and is Lanczos-downscaled to the framebuffer's
  800×600.

Byte-proof the bake is the live render: the new `cockpit_frame.rgba` differs from the old
hand-built one in 1,376,735 / 1,920,000 bytes. Evidence:
`patches/cockpit-on-sel4-framebuffer-LIVE.png` (live cockpit out of seL4 ramfb) +
`patches/cockpit-render-800x600-LIVE.png` (the render-host render). The plumbing
(render → RGBA → XRGB8888 → ramfb → scanout → TAB mode) is unchanged and end-to-end.

## Proven (not theorized)

`docs/desktop-os-research/patches/gpui-offscreen-proof.png` (1024×640 RGBA8) is a real gpui
scene — a cockpit-shaped layout with crisp anti-aliased text, rounded bordered panels, the
world/shell/reflect columns — rendered **with no GPU and no window** on the render host via lavapipe
(`llvmpipe (LLVM 20.1.8), backend=Vulkan, type=Cpu`), through the *actual* `WgpuRenderer`
the real cockpit uses. Scene = 18 quads + 258 monochrome glyph sprites; BGRA→RGBA + premultiplied
alpha + 256-byte row alignment all correct.

## The patch — `patches/gpui-offscreen.patch`

A ~615-line diff against zed's `gpui_wgpu` (the renderer leaf the whole gpui stack already depends
on). `cargo check` + `cargo clippy -p gpui_wgpu` clean; the windowed path is intact (the surface
became `Option`, all 5 sites guarded). Exactly the three functions the feasibility lane scoped,
modelled on the Metal `render_scene_to_image` (`gpui_macos/src/metal_renderer.rs:628`):
- `wgpu_context.rs`: `offscreen_instance()` (`display: None`) + `new_offscreen()` +
  `select_offscreen_adapter_and_device()` (`ZED_OFFSCREEN_PREFER_CPU=1` floats lavapipe to the top).
- `wgpu_renderer.rs`: **(a)** `draw_scene_to_view(scene, &TextureView, w, h)` — the extracted
  shared drawing core (globals + encoder/pass/overflow-grow/submit, minus `present()`); `draw()`
  now = acquire frame → `draw_scene_to_view` → present. **(b)** `render_scene_to_image(scene,
  Size<DevicePixels>) -> (Vec<u8> rgba, u32, u32)` — owned `Bgra8Unorm` texture
  (`RENDER_ATTACHMENT|COPY_SRC`) → `draw_scene_to_view` → `copy_texture_to_buffer` → `map_async`
  + `poll(Wait)` → BGRA→RGBA swizzle (returns raw RGBA, adds no dep). **(c)** `new_offscreen()`
  surfaceless ctor.

Reproduce: patched fork on the render host `~/src/zed`; harness `/tmp/gpui-offscreen-poc/`; run with
`VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json ZED_OFFSCREEN_PREFER_CPU=1`.

## The dregg fork (where the patch lives)

The chain is `starbridge-v2 --features gpui-ui → gpui + gpui_platform → gpui_linux (gpui_wgpu)`,
so the patch lands exactly where the stack already depends. It is a dregg-owned fork branch:

- **`emberian/zed@dregg-offscreen`** — off `fca2ccd` (starbridge-v2's previously-pinned rev; the
  gpui/gpui_wgpu/gpui_platform/gpui_linux crates are byte-identical to `fca2ccd` there — the one
  commit between `fca2ccd` and the PoC `cccc7b2` touches only editor/agent_ui), commit
  `407a6ffd977d82b828e392f92db5cb34edea9549`. starbridge-v2's `gpui` + `gpui_platform` git deps
  point at it, plus a new `gpui_wgpu` dep at the same rev (the `headless-render` feature pulls the
  `CosmicTextSystem` text system + `WgpuHeadlessRenderer` directly). The canonical patch file
  `patches/gpui-offscreen.patch` carries the full diff (8 files: the offscreen renderer +
  the headless wiring below).

What the patch adds on top of the original surfaceless renderer (`new_offscreen` /
`render_scene_to_image`, the macOS `MetalRenderer::render_scene_to_image` analogue):

- `gpui_wgpu`: `WgpuRenderer::render_scene` (the no-readback present analogue) +
  `WgpuHeadlessRenderer: gpui::PlatformHeadlessRenderer` (wraps a surfaceless `WgpuRenderer`),
  a `test-support` feature (pulls `gpui/test-support` + `image`).
- `gpui_linux`: `current_headless_renderer()` → the boxed `WgpuHeadlessRenderer`.
- `gpui_platform`: `current_headless_renderer()` routes to `gpui_linux` on Linux (the Metal
  headless renderer is the macOS branch; both feed gpui's `HeadlessAppContext`/`TestPlatform`).

This is what makes gpui's own headless capture (`Window::render_to_image`) work on Linux — the
mechanism `render_cockpit_headless` drives to get the live element tree onto the framebuffer.
