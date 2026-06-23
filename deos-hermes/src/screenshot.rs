//! Offscreen screenshot capture for the confined-agent dock surface.
//!
//! The [`crate::cockpit_surface::AgentDockView`] is a gpui view; mounting it in
//! starbridge-v2's dock needs a display server. Where `screencapture` is blocked
//! (CI, the atlas crawler, a headless box) there is no window to grab.
//!
//! [`capture_dock`] drives the dock surface to a painted frame entirely offscreen
//! and writes the captured RGBA out as a PNG. It mirrors deos-zed's
//! `screenshot::capture_surface` / starbridge-v2's `render_cockpit_headless`: a
//! [`gpui::HeadlessAppContext`] over `TestPlatform` + the offscreen wgpu renderer
//! (`current_headless_renderer`, lavapipe on Linux), with a no-system-fonts
//! [`CosmicTextSystem`] (deterministic text shaping) and `gpui_component::init`
//! so the kit widgets find their `Theme` global.

use std::borrow::Cow;
use std::path::Path;
use std::sync::Arc;

use anyhow::{Context as _, Result};
use gpui::{px, size, App, Entity, HeadlessAppContext, PlatformTextSystem, Render, Window};
use gpui_wgpu::CosmicTextSystem;

// The same two vendored OFL fonts deos-zed / starbridge-v2 ship for headless
// capture. Referenced from deos-zed's assets so the binary blobs are not
// duplicated in this crate. Lilex = monospace fallback, IBM Plex Sans = UI text.
// No system fonts => deterministic shaping.
static LILEX: &[u8] = include_bytes!("../../deos-zed/assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../../deos-zed/assets/fonts/IBMPlexSans-Regular.ttf");

/// Drive a surface to a painted frame in a headless gpui app and write it to
/// `out` as a PNG. `build_root` constructs the root view exactly as the mounted
/// dock would, inside the offscreen app where `gpui_component::init` has run.
///
/// Returns `(width, height)` of the captured device-pixel image (gpui's headless
/// `TestWindow` reports a 2.0 scale factor, so a logical `w`x`h` resolves to a
/// `2w`x`2h` capture).
pub fn capture_surface<V: Render + 'static>(
    out: &Path,
    w: f32,
    h: f32,
    build_root: impl FnOnce(&mut Window, &mut App) -> Entity<V>,
) -> Result<(u32, u32)> {
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .context("loading the embedded OFL fonts into the headless text system")?;

    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(|cx| gpui_component::init(cx));

    let window = cx.open_window(size(px(w), px(h)), build_root)?;
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx
        .capture_screenshot(window.into())
        .context("capturing the offscreen window (need the offscreen wgpu backend)")?;

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

/// Capture the confined-agent dock surface (chat + tool-call ledger + mandate
/// inspector) rendered from `model`, writing a PNG to `out`.
pub fn capture_dock(out: &Path, model: crate::surface::AgentDockModel) -> Result<(u32, u32)> {
    use crate::cockpit_surface::AgentDockView;
    capture_surface(out, 760., 560., move |_window, cx| {
        cx.new(|cx| AgentDockView::new(model, cx))
    })
}
