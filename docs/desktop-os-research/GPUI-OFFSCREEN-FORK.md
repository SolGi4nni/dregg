# gpui offscreen render — the real renderer, no GPU (a cockpit-shaped Scene on glass, on seL4)

The seL4 `qemu_virt_aarch64` machine has no GPU, so starbridge-v2's gpui (wgpu → Vulkan)
cockpit cannot present to a window there. This is the path that renders a gpui Scene anyway —
**gpui → software Vulkan (lavapipe) → an offscreen texture → RGBA readback → the seL4
compositor framebuffer** — so a real gpui render is a Mode inside the VM, beside the live
image viewer. (What renders today is a hand-built *cockpit-shaped* Scene through this exact
renderer; swapping in the live `cockpit::Cockpit` element tree is the one named frontier — §below.)

## LANDED — a real gpui render is on the seL4 framebuffer (cockpit-shaped; TAB to it)

The weld is closed end-to-end. The deos-image PD (`sel4/dregg-pd/deos-image/`) now has
**two live modes on one framebuffer**, switched with **TAB**:
- `Mode::Image` — the Pharo/Smalltalk object browser of the six real deos cells.
- `Mode::Cockpit` — a **real gpui render of a starbridge-v2-cockpit-shaped Scene** (the
  WORLD/SHELL/REFLECT layout, hand-built — see the frontier note below), blitted onto the
  ramfb framebuffer QEMU scans out (`src/cockpit_frame.rs`).

The cockpit frame is rendered at the framebuffer's exact `800×600` by the **actual gpui
renderer** (`gpui_wgpu::WgpuRenderer::render_scene_to_image`, the patch below) on lavapipe
(llvmpipe, `type=Cpu`, no GPU/window) on persvati — `21` quads + `322` monochrome glyph
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
`patches/cockpit-render-800x600.png` (the persvati render). Serial confirms
`ramfb CONFIGURED: addr=0x60600000 XRGB8888 800x600` then `-> MODE: the starbridge-v2 COCKPIT`.

**The honest frontier that remains** (named, not hidden): the blitted frame is a hand-built
cockpit-shaped gpui `Scene` pushed through the *identical* renderer path the real `Cockpit`
resolves to — NOT yet the live `cockpit::Cockpit` element tree. Swapping it in needs a
headless gpui `App`/`Window` driving `cockpit::Cockpit` (its `shell::Scene` is a
window-manager model that only resolves to a gpui `Scene` inside a live `Window`), then
`render_scene_to_image` on that Scene → the same `cockpit_frame.rgba` bake. The plumbing
(render → RGBA → XRGB8888 → ramfb → scanout → TAB mode) is now PROVEN; this is the one
remaining swap, in starbridge-v2 (a headless cockpit-render entry beside `run_window`,
`main.rs`).

## Proven (not theorized)

`docs/desktop-os-research/patches/gpui-offscreen-proof.png` (1024×640 RGBA8) is a real gpui
scene — a cockpit-shaped layout with crisp anti-aliased text, rounded bordered panels, the
world/shell/reflect columns — rendered **with no GPU and no window** on persvati via lavapipe
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

Reproduce: patched fork on persvati `~/src/zed`; harness `/tmp/gpui-offscreen-poc/`; run with
`VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json ZED_OFFSCREEN_PREFER_CPU=1`.

## Vendor-into-dregg plan (the next lane)

The chain is `starbridge-v2 --features gpui-ui → gpui + gpui_platform → gpui_linux (gpui_wgpu)`,
so the patch lands exactly where the stack already depends.

1. **Land the patch on starbridge-v2's pinned rev.** starbridge-v2 pins zed
   `rev = fca2ccd403e8d13c8f4b968cda2f2c322f420f5a` (the PoC fork is at `cccc7b2`). Re-apply the
   diff onto `fca2ccd`'s `gpui_wgpu` (the `draw`/`new_internal` anchors are stable — expect
   line-offset fuzz only). **Preferred:** push a dregg-owned fork branch (`breadstuffs/zed@offscreen-fork`
   off `fca2ccd`) and repoint the `gpui` + `gpui_platform` git deps at it (clean, reviewable,
   survives rebuilds). Alt: a `[patch]` overlay in starbridge-v2's manifest (lighter, but git-source
   `[patch]` is finicky workspace-wide).
2. **Wire it to the seL4 framebuffer.** Implement `PlatformHeadlessRenderer` for a wgpu renderer
   (using `new_offscreen` + `render_scene_to_image` — ~1 thin impl, the heavy lifting is done), add
   a headless cockpit-render entry beside `run_window` (`main.rs:124`): build the `Cockpit` element
   tree in a headless `App` (text_system = `CosmicTextSystem`), drive a frame, `render_scene_to_image`,
   then blit the RGBA into the VM framebuffer (same byte format the live image-viewer Mode already
   writes). For first bring-up, push a hand-built Scene (as the PoC does) to prove the seL4 plumbing,
   then swap in the real cockpit element tree.

The honest frontier beyond this: the cockpit's `shell::Scene` is a window-manager model, not a gpui
`Scene` — the real cockpit element tree needs a live headless `App`/`Window` (step 2's harness), which
this PoC stands in for with a hand-authored cockpit-shaped Scene through the identical renderer path.
