//! **Headless render** — bake a gpui view to a PNG offscreen, no window, no GPU display.
//!
//! This is the SAME path starbridge-v2's `render_cockpit_headless` bakes through
//! (`HeadlessAppContext::with_platform` + `gpui_platform::current_headless_renderer`
//! offscreen wgpu + `CosmicTextSystem` + `capture_screenshot`), reduced to a small
//! reusable harness over an arbitrary `Render` view. It is what makes "the view-tree
//! renders to real gpui-component pixels" provable by RUNNING + a captured frame.
//!
//! The harness keeps the [`gpui::HeadlessAppContext`] live across multiple captures so a
//! test can: render frame 1 → fire a real verified turn through the applet → re-render
//! (immediate-mode re-read) → capture frame 2 showing the advanced value.

use std::borrow::Cow;
use std::sync::Arc;

use gpui::{
    px, size, AnyWindowHandle, HeadlessAppContext, PlatformTextSystem, Render, WindowHandle,
};
use gpui_wgpu::CosmicTextSystem;
use image::RgbaImage;

/// A live headless gpui app that can open a window over a `Render` view and capture
/// frames to RGBA. Holds the app + the open window so repeated captures (across turns)
/// reflect the SAME live view.
pub struct HeadlessRender {
    cx: HeadlessAppContext,
}

impl HeadlessRender {
    /// Boot a headless gpui app with real text shaping (no system fonts → deterministic)
    /// and gpui-component initialized + the dark theme applied (so kit widgets — the
    /// real `Button`/`Label` — have their `Theme` global, exactly as the cockpit bake
    /// inits it). `fonts` are TTF blobs to register; the first family is the fallback.
    pub fn boot(fallback_family: &str, fonts: &[&'static [u8]]) -> anyhow::Result<Self> {
        let text_system: Arc<dyn PlatformTextSystem> =
            Arc::new(CosmicTextSystem::new_without_system_fonts(fallback_family));
        text_system.add_fonts(fonts.iter().map(|b| Cow::Borrowed(*b)).collect())?;

        let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
            gpui_platform::current_headless_renderer()
        });

        // gpui-component reads its `Theme` global at render time — init it (and force a
        // dark theme) on this headless App, just as the cockpit's headless bake does.
        cx.update(|cx| gpui_component::init(cx));
        cx.update(|cx| {
            gpui_component::theme::Theme::change(gpui_component::theme::ThemeMode::Dark, None, cx)
        });

        Ok(Self { cx })
    }

    /// Open a headless window (logical `w`×`h`) whose root is the view built by
    /// `build_root`. Returns the window handle; capture it with [`Self::capture`].
    pub fn open<V: Render + 'static>(
        &mut self,
        w: f32,
        h: f32,
        build_root: impl FnOnce(&mut gpui::Window, &mut gpui::App) -> gpui::Entity<V>,
    ) -> anyhow::Result<WindowHandle<V>> {
        let window = self.cx.open_window(size(px(w), px(h)), build_root)?;
        self.cx.run_until_parked();
        Ok(window)
    }

    /// Force a refresh + capture the resolved gpui Scene to an RGBA image (the offscreen
    /// wgpu render). gpui's headless window reports a 2.0 scale factor, so the returned
    /// image is 2w×2h device pixels.
    pub fn capture(&mut self, window: AnyWindowHandle) -> anyhow::Result<RgbaImage> {
        self.cx.update_window(window, |_, window, _cx| window.refresh())?;
        self.cx.run_until_parked();
        Ok(self.cx.capture_screenshot(window)?)
    }

    /// Run an update against the live `App` (e.g. notify the view to re-render), then
    /// settle. The view re-reads the model off the live ledger on its next render, so a
    /// turn fired on the shared applet (outside the view) shows up after a `capture`
    /// (which refreshes the window).
    pub fn update<R>(&mut self, f: impl FnOnce(&mut gpui::App) -> R) -> R {
        let r = self.cx.update(f);
        self.cx.run_until_parked();
        r
    }

    /// Reach a window's ROOT entity to update it (e.g. drive the fine-grained
    /// `AppletView::on_committed_turn` hook after a turn), then settle. This is how a
    /// committed turn's touched slots are fed to the renderer's signal registry so ONLY
    /// the dirty bindings re-read on the next paint.
    pub fn update_root<V: Render + 'static, R>(
        &mut self,
        window: WindowHandle<V>,
        f: impl FnOnce(&mut V, &mut gpui::Window, &mut gpui::Context<V>) -> R,
    ) -> anyhow::Result<R> {
        let r = window.update(&mut self.cx, f)?;
        self.cx.run_until_parked();
        Ok(r)
    }
}
