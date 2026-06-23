//! Mount [`deos_zed::Editor`] as a [`CockpitSurface`] — the deos editor pane.
//!
//! READY-TO-DROP, NOT-YET-WIRED. This file forwards the cockpit's
//! [`CockpitSurface`] trait to the inherent methods on
//! [`deos_zed::cockpit_surface::EditorSurface`]. It is intentionally left out of
//! `dock/mod.rs` so it touches nothing actively-worked; mounting it is exactly
//! two edits, both confined to the dock module (NOT `cockpit.rs`):
//!
//!   1. Add to `starbridge-v2/Cargo.toml` (a cross-workspace path dep is fine —
//!      deos-zed pins the SAME gpui fork, so one gpui resolves across both):
//!
//!      ```toml
//!      deos-zed = { path = "../deos-zed", default-features = false, features = ["cockpit-surface", "highlight-common"] }
//!      ```
//!
//!   2. Add `pub mod editor_surface;` to `starbridge-v2/src/dock/mod.rs`.
//!
//! Then the cockpit can do:
//!
//! ```ignore
//! use crate::dock::editor_surface::EditorPane;
//! use deos_zed::fs::RealFs;
//!
//! let surface = EditorPane::new(next_surface_id(), RealFs::arc(), project_root, window, cx);
//! pane.add_surface(Box::new(surface), window, cx); // hosts in a dock tab
//! ```
//!
//! Swap `RealFs::arc()` for a firmament-backed `Arc<dyn Fs>` and the same pane
//! edits sovereign cells with receipted saves — see
//! `deos-zed/FIRMAMENT-FS-SEAM.md`.

use deos_zed::cockpit_surface::EditorSurface;
use gpui::{AnyElement, App, FocusHandle, IntoElement, SharedString, Window};

use super::surface::{CockpitSurface, SurfaceId};

/// A dock-hostable wrapper around a deos-zed editor surface.
pub struct EditorPane(EditorSurface);

impl EditorPane {
    pub fn new(
        id: u64,
        fs: std::sync::Arc<dyn deos_zed::fs::Fs>,
        root: std::path::PathBuf,
        window: &mut Window,
        cx: &mut App,
    ) -> Self {
        EditorPane(EditorSurface::new(id, fs, root, window, cx))
    }

    /// Build a SEEDED editor pane: an in-memory buffer filled with `revisions`
    /// (the last shown; priors are on-ledger patches) under the virtual `name`
    /// (drives syntax highlighting), plus a real file tree over `fs`/`root`. What
    /// the headless showcase bake uses — disk-free highlighted code with a real
    /// `N patches · on-ledger` status.
    pub fn seeded(
        id: u64,
        fs: std::sync::Arc<dyn deos_zed::fs::Fs>,
        root: std::path::PathBuf,
        name: &str,
        revisions: &[&str],
        window: &mut Window,
        cx: &mut App,
    ) -> Self {
        EditorPane(EditorSurface::seeded(id, fs, root, name, revisions, window, cx))
    }

    /// Access the underlying editor entity (host-side open/save).
    pub fn editor(&self) -> &gpui::Entity<deos_zed::editor::Editor> {
        self.0.editor()
    }
}

impl CockpitSurface for EditorPane {
    fn item_id(&self) -> SurfaceId {
        SurfaceId(self.0.surface_id())
    }

    fn tab_label(&self) -> SharedString {
        // CockpitSurface::tab_label takes no cx; the live title is rendered in
        // tab_content instead. This static label is the stable fallback.
        SharedString::from("editor")
    }

    fn tab_content(&self, _window: &mut Window, cx: &mut App) -> AnyElement {
        use gpui::{div, ParentElement};
        div().child(self.0.tab_label(cx)).into_any_element()
    }

    fn render_body(&mut self, window: &mut Window, cx: &mut App) -> AnyElement {
        self.0.render_body(window, cx)
    }

    fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.0.focus_handle(cx)
    }

    fn is_dirty(&self, cx: &App) -> bool {
        self.0.is_dirty(cx)
    }

    fn boxed_clone(&self) -> Box<dyn CockpitSurface> {
        Box::new(EditorPane(self.0.clone()))
    }
}
