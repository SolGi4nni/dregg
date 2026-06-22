//! Offscreen screenshot capture for the deos-zed surfaces.
//!
//! The demos ([`crate::Editor`] via `demo`, [`crate::DocViewer`] via `merge_demo`)
//! are windowed-only: they call `gpui_platform::application().with_assets(..)` +
//! `cx.open_window`, which needs a display server. Where `screencapture` is blocked
//! (CI, the atlas crawler, a headless box) there is no window to grab.
//!
//! [`capture_surface`] drives any gpui surface to a painted frame entirely
//! offscreen and writes the captured RGBA out as a PNG. It mirrors starbridge-v2's
//! `render_cockpit_headless`: a [`gpui::HeadlessAppContext`] over `TestPlatform` +
//! the offscreen wgpu renderer (`current_headless_renderer`, lavapipe on Linux),
//! with a no-system-fonts [`CosmicTextSystem`] (deterministic text shaping) and
//! `gpui_component::init` so the kit widgets find their `Theme` global.
//!
//! Both demos route their `--screenshot <out.png>` mode here.

use std::borrow::Cow;
use std::path::Path;
use std::sync::Arc;

use anyhow::{Context as _, Result};
use gpui::{px, size, App, Entity, HeadlessAppContext, PlatformTextSystem, Render, Window};
use gpui_wgpu::CosmicTextSystem;

// Vendored OFL fonts (the same two starbridge-v2's render_cockpit_headless ships):
// Lilex is the monospace fallback used when an unknown family is requested (the
// editor asks for a code font; CosmicTextSystem falls back to Lilex), IBM Plex Sans
// covers the proportional UI text. No system fonts => deterministic shaping.
static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// Drive a surface to a painted frame in a headless gpui app and write it to `out`
/// as a PNG. `build_root` constructs the root view (typically wrapped in
/// `gpui_component::Root`) exactly as the windowed demo would, but inside the
/// offscreen app where `gpui_component::init` has already run.
///
/// Returns `(width, height)` of the captured device-pixel image. gpui's headless
/// `TestWindow` reports a fixed 2.0 scale factor, so a logical `w`x`h` window
/// resolves to a `2w`x`2h` capture (crisp; no downscale — these PNGs are for the
/// atlas, not the seL4 framebuffer).
pub fn capture_surface<V: Render + 'static>(
    out: &Path,
    w: f32,
    h: f32,
    build_root: impl FnOnce(&mut Window, &mut App) -> Entity<V>,
) -> Result<(u32, u32)> {
    // 1. Real text shaping with no system fonts (deterministic), Lilex fallback.
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .context("loading the embedded OFL fonts into the headless text system")?;

    // 2. Headless app over TestPlatform + the offscreen wgpu renderer
    //    (current_headless_renderer => WgpuHeadlessRenderer; lavapipe when
    //    ZED_OFFSCREEN_PREFER_CPU=1). Its sprite atlas backs the window.
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });

    // 2b. The kit's Theme global. The editor + doc-viewer render gpui-component
    //     widgets that read `gpui_component::theme::Theme` at paint time; the
    //     WINDOWED path inits it at boot, so the headless App must too or any kit
    //     widget panics "no state of type gpui_component::theme::Theme".
    cx.update(|cx| gpui_component::init(cx));

    // 3. Open a headless (hidden, unfocused) window whose root IS the surface.
    let window = cx.open_window(size(px(w), px(h)), build_root)?;

    // 4. Drive to a fully-rendered frame, then capture the resolved gpui Scene.
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx
        .capture_screenshot(window.into())
        .context("capturing the offscreen window (no renderer? need the offscreen wgpu backend)")?;

    let (cw, ch) = (captured.width(), captured.height());
    if let Some(parent) = out.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent).ok();
        }
    }
    captured
        .save(out)
        .with_context(|| format!("writing the PNG to {}", out.display()))?;
    Ok((cw, ch))
}
