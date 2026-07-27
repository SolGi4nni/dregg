//! Mount [`deos_matrix::chat::ChatView`] as a [`CockpitSurface`] — the deos-chat
//! pane (the social/multiplayer layer over the dregg world).
//!
//! READY-TO-DROP, NOT-YET-WIRED. This file forwards the cockpit's
//! [`CockpitSurface`] trait to the inherent methods on
//! [`deos_matrix::cockpit_surface::ChatSurface`]. It is intentionally left out of
//! `dock/mod.rs` so it touches nothing actively-worked; mounting it is exactly
//! two edits, both confined to the dock module (NOT `cockpit.rs`):
//!
//!   1. Add to `starbridge-v2/Cargo.toml` (a cross-workspace path dep is fine —
//!      deos-matrix pins the SAME gpui fork, so one gpui resolves across both):
//!
//!      ```toml
//!      deos-matrix = { path = "../deos-matrix", default-features = false, features = ["cockpit-surface"] }
//!      ```
//!
//!   2. Add `pub mod chat_surface;` to `starbridge-v2/src/dock/mod.rs`.
//!
//! Then the cockpit can do:
//!
//! ```ignore
//! // IGNORED: `window`, `cx` and `pane` are live gpui handles that exist ONLY inside a
//! // running `gpui_platform::application().run(..)` callback; a doctest has no windowing
//! // platform to hand one out. `next_surface_id()` is the host dock's counter.
//! use crate::dock::chat_surface::ChatPane;
//! use deos_matrix::source::MockSource;            // or the live MatrixHandle
//! use std::sync::Arc;
//!
//! let source = Arc::new(MockSource::seeded());     // offline; swap for MatrixHandle when logged in
//! let surface = ChatPane::new(next_surface_id(), source, window, cx);
//! pane.add_surface(Box::new(surface), window, cx);  // hosts in a dock tab
//! ```
//!
//! The chat renders against the `ChatSource` seam; `MockSource` (recorded sync)
//! makes the pane real offline, the live `MatrixHandle` (login + sync) drops in
//! unchanged. The `⬡ attach membrane` affordance routes to the comms-PD's
//! `MembraneHost` — see `docs/deos/MEMBRANE-MERGE-SEAM.md`.

use deos_matrix::cockpit_surface::ChatSurface;
use gpui::{AnyElement, App, FocusHandle, SharedString, Window};

use super::surface::{CockpitSurface, SurfaceId};

/// A dock-hostable wrapper around a deos-matrix chat surface.
pub struct ChatPane(ChatSurface);

impl ChatPane {
    pub fn new(
        id: u64,
        source: std::sync::Arc<dyn deos_matrix::source::ChatSource>,
        window: &mut Window,
        cx: &mut App,
    ) -> Self {
        ChatPane(ChatSurface::new(id, source, window, cx))
    }
}

impl CockpitSurface for ChatPane {
    fn item_id(&self) -> SurfaceId {
        SurfaceId(self.0.item_id())
    }

    fn tab_label(&self) -> SharedString {
        SharedString::from(self.0.tab_label())
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
        Box::new(ChatPane(self.0.boxed_clone()))
    }
}
