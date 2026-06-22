//! [`TerminalSurface`] — a cloneable, dock-hostable handle around a
//! [`TerminalView`] entity, shaped to the cockpit's `CockpitSurface` trait.
//!
//! This module intentionally does NOT depend on starbridge-v2's `CockpitSurface`
//! trait (that would invert the dependency). Instead it exposes inherent methods
//! with the same shapes the trait needs — `surface_id`, `tab_label`,
//! `render_body`, `focus_handle`, `is_dirty` — and starbridge-v2's thin
//! `dock::terminal_surface::TerminalPane` forwards the trait to them. This mirrors
//! exactly how `deos_zed::cockpit_surface::EditorSurface` mounts the editor pane.
//!
//! A `TerminalSurface` is a cheap handle (an `Entity<TerminalView>` + an id), so
//! `Clone` is cheap — satisfying the `boxed_clone` the dock needs when a pane is
//! split.

use gpui::{
    div, AnyElement, App, AppContext, Entity, FocusHandle, IntoElement, ParentElement, SharedString,
    Styled, Window,
};

use crate::model::{Terminal, TermSize};
use crate::view::TerminalView;

/// A dock-mountable terminal surface: a stable id plus the live terminal view.
#[derive(Clone)]
pub struct TerminalSurface {
    id: u64,
    view: Entity<TerminalView>,
}

impl TerminalSurface {
    /// Mount an already-built [`TerminalView`] entity as a surface.
    pub fn from_view(id: u64, view: Entity<TerminalView>) -> Self {
        Self { id, view }
    }

    /// Spawn `$SHELL` and wrap it as a surface. Returns an error if the PTY
    /// can't be opened.
    pub fn spawn_shell(id: u64, cx: &mut App) -> anyhow::Result<Self> {
        let terminal = Terminal::spawn(
            None,
            std::env::current_dir().ok(),
            std::env::vars().collect(),
            TermSize::new(80, 24),
        )?;
        let view = cx.new(|cx| TerminalView::new(terminal, cx));
        Ok(Self { id, view })
    }

    /// The live terminal view entity (host-side input/inspection).
    pub fn view(&self) -> &Entity<TerminalView> {
        &self.view
    }

    pub fn surface_id(&self) -> u64 {
        self.id
    }

    /// The tab label — the running program's title if the shell set one (OSC 0/2),
    /// else a generic "terminal".
    pub fn tab_label(&self, cx: &App) -> SharedString {
        let title = self.view.read(cx).terminal.title();
        match title {
            Some(t) if !t.trim().is_empty() => SharedString::from(t),
            _ => SharedString::from("terminal"),
        }
    }

    /// Render the terminal body — the live view entity, which gpui re-renders on
    /// its own repaint loop.
    pub fn render_body(&mut self, _window: &mut Window, _cx: &mut App) -> AnyElement {
        div()
            .size_full()
            .child(self.view.clone())
            .into_any_element()
    }

    pub fn focus_handle(&self, cx: &App) -> FocusHandle {
        use gpui::Focusable;
        self.view.read(cx).focus_handle(cx)
    }

    /// A terminal is "dirty" (worth a marker) while its child process is alive —
    /// closing the tab would kill a running shell/command. Once the shell exits,
    /// it is clean.
    pub fn is_dirty(&self, cx: &App) -> bool {
        !self.view.read(cx).terminal.has_exited()
    }
}
