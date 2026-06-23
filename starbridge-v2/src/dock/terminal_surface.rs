//! Mount [`deos_terminal::TerminalView`] as a [`CockpitSurface`] — a REAL
//! terminal (alacritty PTY + grid) as a cockpit dock pane. Run cargo/git/shells
//! INSIDE deos: the terminal half of the self-hosting dev loop, the sibling of
//! [`super::editor_surface`].
//!
//! READY-TO-DROP, NOT-YET-WIRED — exactly like `editor_surface.rs`, this file is
//! intentionally left out of `dock/mod.rs` so it touches nothing actively-worked
//! (the existing metaphorical command-surface in `crate::terminal` and the
//! actively-edited `cockpit.rs` are both untouched). Mounting it is two edits,
//! both confined to the dock module (NOT `cockpit.rs`):
//!
//!   1. Add to `starbridge-v2/Cargo.toml` (a cross-workspace path dep is fine —
//!      deos-terminal pins the SAME gpui fork `emberian/zed@407a6ff`, so one gpui
//!      resolves across both):
//!
//!      ```toml
//!      deos-terminal = { path = "../deos-terminal", features = ["cockpit-surface"] }
//!      ```
//!
//!   2. Add `pub mod terminal_surface;` to `starbridge-v2/src/dock/mod.rs`.
//!
//! Then the cockpit can do:
//!
//! ```ignore
//! use crate::dock::terminal_surface::TerminalPane;
//!
//! let surface = TerminalPane::spawn_shell(next_surface_id(), cx)?;
//! pane.update(cx, |pane, cx| {
//!     pane.add_item(Box::new(surface), window, cx) // hosts in a dock tab
//! });
//! ```
//!
//! The pane then renders a live shell, routes keystrokes to its PTY, streams
//! output, and resizes the grid to the pane. (A later step can swap the host
//! `$SHELL` spawn for a firmament-cap-gated command exec — the same seam the
//! metaphorical `crate::terminal` command-surface already models — so the dock
//! terminal runs under a real capability.)

use deos_terminal::cockpit_surface::TerminalSurface;
use gpui::{AnyElement, App, FocusHandle, IntoElement, SharedString, Window};

use super::surface::{CockpitSurface, SurfaceId};

/// A dock-hostable wrapper around a deos-terminal surface.
pub struct TerminalPane(TerminalSurface);

impl TerminalPane {
    /// Spawn `$SHELL` on a PTY and wrap it as a mountable pane.
    pub fn spawn_shell(id: u64, cx: &mut App) -> anyhow::Result<Self> {
        Ok(TerminalPane(TerminalSurface::spawn_shell(id, cx)?))
    }

    /// Wrap an already-built terminal view entity.
    pub fn from_view(id: u64, view: gpui::Entity<deos_terminal::TerminalView>) -> Self {
        TerminalPane(TerminalSurface::from_view(id, view))
    }

    /// Mount a SEEDED terminal pane: a grid driven by a recorded byte stream (a
    /// captured shell session) with NO live PTY. Deterministic — what the
    /// headless showcase bake uses (a real terminal grid showing a recorded
    /// `cargo`/`git` session, no `$SHELL` race).
    pub fn seeded(id: u64, cols: u16, rows: u16, bytes: &[u8], cx: &mut App) -> Self {
        TerminalPane(TerminalSurface::seeded(id, cols, rows, bytes, cx))
    }

    /// Access the underlying terminal view entity (host-side input/inspection).
    pub fn view(&self) -> &gpui::Entity<deos_terminal::TerminalView> {
        self.0.view()
    }
}

impl CockpitSurface for TerminalPane {
    fn item_id(&self) -> SurfaceId {
        SurfaceId(self.0.surface_id())
    }

    fn tab_label(&self) -> SharedString {
        // The trait's tab_label takes no cx; the live title is rendered in
        // tab_content instead. This static label is the stable fallback.
        SharedString::from("terminal")
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
        // Dirty while the child process is alive — closing the tab kills a
        // running shell/command.
        self.0.is_dirty(cx)
    }

    fn boxed_clone(&self) -> Box<dyn CockpitSurface> {
        Box::new(TerminalPane(self.0.clone()))
    }
}
