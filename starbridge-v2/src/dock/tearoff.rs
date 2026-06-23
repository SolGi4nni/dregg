//! SURFACE MIGRATION — the Local→Surface tear-off: a dock pane pops OUT into its
//! own OS window, its surface IDENTITY preserved.
//!
//! This is the first concrete migration of `docs/deos/SURFACE-MIGRATION.md`:
//! relocating a [`SurfaceCapability`](crate::surface::SurfaceCapability) along the
//! firmament [`Target`](dregg_firmament::Target) distance axis from `Surface`
//! (composited inside the cockpit's single window) to its OWN `Surface` window — a
//! second OS window the same compositor authority drives. The cell behind the
//! surface, its caps, and its history are UNCHANGED; only the *backing transport*
//! (which OS window paints it) moves. At `n = 1` this is the firmament's strong-
//! local collapse: the pop-out is immediate and consistent, the torn-off window
//! reflects the SAME live world the dock pane did.
//!
//! ## What this module is
//!
//! gpui supports multiple OS windows ([`App::open_window`](gpui::App::open_window)).
//! A tear-off:
//!   1. mints a fresh OS window whose root view is a [`TornOffWindow`],
//!   2. records it in a [`WindowRegistry`] (keyed by the torn-off surface's
//!      stable id — the SAME [`SurfaceId`] the dock pane used, so identity is
//!      preserved across the move),
//!   3. renders that surface's body in the new window by RE-ENTERING the host
//!      through a stored render callback (the exact `panel_for_tab` re-entry the
//!      in-dock [`TabSurface`](super) uses — so the torn-off window paints the
//!      identical live body, over the identical cell, every frame).
//!
//! Pop-BACK closes the OS window and drops the registry entry; the host's dock
//! pane was never removed (the tear-off is non-destructive — the surface is
//! *mirrored* into a window, and on pop-back the window simply goes away). A later
//! slice can make tear-off *move* the pane out of the dock and pop-back graft it
//! home; this slice keeps the simpler, safe mirror semantics so the cockpit's
//! single-window path is untouched.
//!
//! ## Why the host is referenced abstractly
//!
//! [`TornOffWindow`] does NOT know the cockpit type — it holds a boxed
//! `render` callback `Fn(&mut Window, &mut App) -> AnyElement`. The cockpit
//! constructs that callback over its own `WeakEntity` + the surface's `Tab` (the
//! identity), so this module stays in `dock/` with a `gpui`-only dependency, the
//! same decoupling [`CockpitSurface`](super::surface::CockpitSurface) keeps. The
//! callback is the seam through which the *same* `SurfaceCapability`-gated body
//! reaches the new window — it is NOT a copy of the surface's state.
//!
//! Windowed-only: a tear-off opens a real OS window, so it is never exercised by
//! the headless bake (which renders one offscreen window). The cockpit gates the
//! pop-out behind a live `&mut Window` (a ⌘K command / a pane "↗ pop out"
//! control), exactly as it gates the dev-pane spawns.

use std::collections::HashMap;

use gpui::{
    div, prelude::*, px, AnyElement, App, Bounds, Context, Focusable, FocusHandle, IntoElement,
    Render, SharedString, TitlebarOptions, Window, WindowBounds, WindowHandle, WindowOptions,
};

use super::surface::SurfaceId;
use super::theme;

/// A stable identity for a torn-off surface as it moves between the dock and a
/// window. It is the SAME id the in-dock pane used for the surface (the cockpit
/// passes its `Tab::index()` / dev-surface id straight through), so the registry
/// and the in-dock pane agree on "which surface" — the identity the migration
/// preserves. (A newtype alias over the dock's [`SurfaceId`] for call-site
/// clarity at the tear-off seam.)
pub type TornSurfaceId = SurfaceId;

/// The root view of a TORN-OFF OS window: it renders one cockpit surface's body
/// by re-entering the host through the stored `render` callback, exactly the body
/// the surface showed in the dock. Cheap — it holds a label, a focus handle, and
/// a boxed callback; the callback closes over the host's weak handle, so the
/// window paints the live surface without owning any of its state.
pub struct TornOffWindow {
    /// The surface this window hosts (the identity the tear-off preserves).
    id: TornSurfaceId,
    /// The window title / the surface's operator-facing label.
    label: SharedString,
    /// Renders the surface's body — the re-entry into the host (the cockpit's
    /// `panel_for_tab`), the SAME seam [`TabSurface`](super) renders through. Boxed
    /// so this module needs no knowledge of the host type.
    #[allow(clippy::type_complexity)]
    render: Box<dyn Fn(&mut Window, &mut App) -> AnyElement + 'static>,
    focus: FocusHandle,
}

impl TornOffWindow {
    /// Build a torn-off window root over `id`/`label` with a body `render`
    /// callback. The callback is invoked each frame on the new window's thread
    /// (gpui is single-threaded; all windows share the one [`App`]), so it sees
    /// the live host state — the torn-off body advances with the world like the
    /// in-dock one.
    pub fn new(
        id: TornSurfaceId,
        label: impl Into<SharedString>,
        render: impl Fn(&mut Window, &mut App) -> AnyElement + 'static,
        cx: &mut Context<Self>,
    ) -> Self {
        Self {
            id,
            label: label.into(),
            render: Box::new(render),
            focus: cx.focus_handle(),
        }
    }

    pub fn surface_id(&self) -> TornSurfaceId {
        self.id
    }

    pub fn label(&self) -> &SharedString {
        &self.label
    }
}

impl Focusable for TornOffWindow {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }
}

impl Render for TornOffWindow {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        // Re-enter the host to build the live body. Borrow the callback out of
        // `self` across the call so the `&mut Context<Self>` (which derefs to
        // `&mut App`) can be handed in — the same take-then-restore the pane uses
        // for its surfaces' `render_body`.
        let render = std::mem::replace(
            &mut self.render,
            Box::new(|_, _| div().into_any_element()),
        );
        let body = render(window, cx);
        self.render = render;

        div()
            .track_focus(&self.focus)
            .flex()
            .flex_col()
            .size_full()
            .bg(theme::bg())
            // A slim torn-off chrome strip: the surface label + a "↩ pop back"
            // affordance hint. The actual pop-back is driven by the host (it owns
            // the registry + the window handle); this strip is the operator's
            // marker that the window is a torn-off mirror, not a second cockpit.
            .child(
                div()
                    .flex()
                    .flex_row()
                    .items_center()
                    .gap_2()
                    .h(px(28.))
                    .px_2()
                    .bg(theme::panel())
                    .border_b_1()
                    .border_color(theme::border())
                    .text_xs()
                    .text_color(theme::muted())
                    .child(SharedString::from("↗ torn-off surface"))
                    .child(
                        div()
                            .text_color(theme::text())
                            .child(self.label.clone()),
                    ),
            )
            .child(div().flex_1().overflow_hidden().child(body))
    }
}

/// The registry of TORN-OFF WINDOWS — the cockpit's record of which surfaces are
/// currently popped out into their own OS windows, keyed by the surface's stable
/// id. It is the migration's bookkeeping: a surface is in EXACTLY one of two
/// places along the firmament distance axis at a time from the operator's view —
/// composited in the dock, or torn off into its window — and this map is how the
/// cockpit knows which, so a second pop-out of the same surface re-focuses the
/// existing window instead of minting a duplicate.
///
/// gpui's [`WindowHandle`] is `Copy`; the registry stores it so pop-back can close
/// the window ([`Window::remove_window`](gpui::Window::remove_window) via the
/// handle) and re-focus can raise it.
#[derive(Default)]
pub struct WindowRegistry {
    torn: HashMap<TornSurfaceId, WindowHandle<TornOffWindow>>,
}

impl WindowRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Whether `id`'s surface is currently torn off into its own window.
    pub fn is_torn_off(&self, id: TornSurfaceId) -> bool {
        self.torn.contains_key(&id)
    }

    /// The number of currently-open torn-off windows.
    pub fn len(&self) -> usize {
        self.torn.len()
    }

    pub fn is_empty(&self) -> bool {
        self.torn.is_empty()
    }

    /// The handle for `id`'s torn-off window, if it is torn off (so the host can
    /// raise/focus an already-open one rather than duplicate it).
    pub fn handle(&self, id: TornSurfaceId) -> Option<WindowHandle<TornOffWindow>> {
        self.torn.get(&id).copied()
    }

    /// TEAR OFF `id` into a fresh OS window (the Local→Surface migration). If the
    /// surface is already torn off, this re-activates the existing window and
    /// returns its handle (no duplicate) — the migration is idempotent in the
    /// operator's surface identity. Otherwise it opens a new OS window whose root
    /// is a [`TornOffWindow`] rendering `render` (the host's re-entry over the
    /// SAME surface), records the handle, and returns it.
    ///
    /// `render` MUST close over the host's live handle so the window paints the
    /// live surface (the identity-preserving seam). `label` titles the window.
    ///
    /// Returns the window handle, or the gpui error if the platform refused the
    /// window (surfaced fail-closed by the caller; nothing is recorded on error).
    pub fn tear_off(
        &mut self,
        id: TornSurfaceId,
        label: impl Into<SharedString>,
        render: impl Fn(&mut Window, &mut App) -> AnyElement + 'static,
        cx: &mut App,
    ) -> anyhow::Result<WindowHandle<TornOffWindow>> {
        if let Some(existing) = self.torn.get(&id).copied() {
            // Already torn off — bring the existing window forward, don't mint a
            // second one over the same surface (identity is one-window).
            cx.activate(false);
            let _ = existing.update(cx, |_root, window, _cx| {
                window.activate_window();
            });
            return Ok(existing);
        }

        let label: SharedString = label.into();
        let title = label.clone();
        let bounds = Bounds::centered(None, gpui::size(px(720.), px(560.)), cx);
        let handle = cx.open_window(
            WindowOptions {
                window_bounds: Some(WindowBounds::Windowed(bounds)),
                titlebar: Some(TitlebarOptions {
                    title: Some(format!("deos — {title}").into()),
                    ..Default::default()
                }),
                ..Default::default()
            },
            |_window, cx| cx.new(|cx| TornOffWindow::new(id, label.clone(), render, cx)),
        )?;
        self.torn.insert(id, handle);
        Ok(handle)
    }

    /// POP BACK `id`'s torn-off window: close the OS window and drop the registry
    /// entry (the surface is once again only in the dock). A no-op if the surface
    /// is not torn off. Returns whether a window was closed.
    ///
    /// This is the inverse migration (Surface-window → Surface-in-dock). Because
    /// the tear-off was a non-destructive MIRROR (the dock pane was never removed),
    /// pop-back is just closing the second window — the surface keeps its identity
    /// and its in-dock seat throughout.
    pub fn pop_back(&mut self, id: TornSurfaceId, cx: &mut App) -> bool {
        let Some(handle) = self.torn.remove(&id) else {
            return false;
        };
        let _ = handle.update(cx, |_root, window, _cx| {
            window.remove_window();
        });
        true
    }

    /// Prune entries whose OS window has been closed by the user (the platform
    /// titlebar close button), so the registry does not leak handles to dead
    /// windows. Called by the host each frame it tears off / pops back; a handle
    /// whose `entity` no longer resolves is dropped. Returns the number pruned.
    pub fn prune_closed(&mut self, cx: &App) -> usize {
        let before = self.torn.len();
        self.torn.retain(|_id, handle| handle.entity(cx).is_ok());
        before - self.torn.len()
    }
}
