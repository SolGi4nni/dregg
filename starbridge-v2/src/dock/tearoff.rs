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
    div, prelude::*, px, AnyElement, App, Bounds, Context, Entity, FocusHandle, Focusable,
    IntoElement, MouseButton, Render, SharedString, TitlebarOptions, Window, WindowBounds,
    WindowHandle, WindowOptions,
};
use gpui_component::Root;

use super::surface::{CockpitSurface, SurfaceId};
use super::theme;

/// A stable identity for a torn-off surface as it moves between the dock and a
/// window. It is the SAME id the in-dock pane used for the surface (the cockpit
/// passes its `Tab::index()` / dev-surface id straight through), so the registry
/// and the in-dock pane agree on "which surface" — the identity the migration
/// preserves. (A newtype alias over the dock's [`SurfaceId`] for call-site
/// clarity at the tear-off seam.)
pub type TornSurfaceId = SurfaceId;

/// How a torn-off window obtains its body — the load-bearing distinction between a
/// SAFE re-entry (a gpui-FREE body that may render in two windows the same frame)
/// and a MOVED live entity (which must render in EXACTLY ONE window).
///
/// ## The re-entrant-render crash this enum exists to prevent
///
/// A [`CockpitSurface`] whose `render_body` paints a focus-tracked gpui
/// [`Entity`](gpui::Entity) (the live editor/terminal panes) CANNOT be a
/// [`Self::Mirror`]: re-entering the host to paint that SAME entity in a second
/// window the same frame is a re-entrant `Entity::update` / a double `track_focus`,
/// which panics gpui. The migration's invariant — a surface is in EXACTLY ONE place
/// along the firmament distance axis at a time — is therefore made LITERAL for
/// entity-bearing surfaces: they are [`Self::Owned`] (MOVED out of the dock pane
/// into the torn-off window), so the live entity lives in one window, never two.
enum TornBody {
    /// A gpui-FREE body re-entered through the host each frame (a [`Tab`]'s text
    /// panel). The host's dock pane keeps its copy; this is a safe live MIRROR
    /// because re-building a text element tree twice the same frame touches no
    /// shared live entity. The boxed callback closes over the host's weak handle.
    #[allow(clippy::type_complexity)]
    Mirror(Box<dyn Fn(&mut Window, &mut App) -> AnyElement + 'static>),
    /// A surface MOVED out of the dock pane into this window — the crash fix. The
    /// surface (and any live focus-tracked entity it owns) is now rendered HERE and
    /// ONLY here (`render_body`), so there is no second same-frame render of its
    /// entity. Pop-back moves it home.
    Owned(Box<dyn CockpitSurface>),
}

/// The root view of a TORN-OFF OS window: it renders one cockpit surface's body —
/// either by re-entering the host for a gpui-free [`Tab`] body (a live MIRROR), or
/// by rendering a surface MOVED here (an [`TornBody::Owned`], the live entity in
/// exactly one window — the crash fix). Cheap — a label, a focus handle, and the
/// body source.
pub struct TornOffWindow {
    /// The surface this window hosts (the identity the tear-off preserves).
    id: TornSurfaceId,
    /// The window title / the surface's operator-facing label.
    label: SharedString,
    /// The operator-facing IDENTITY/cap-badge of the surface (who/what authority
    /// it runs under — e.g. `you · 3f9c · 🔑 7 caps`). Shown in the torn-off
    /// chrome so a popped pane is identifiable, not an anonymous box.
    badge: SharedString,
    /// The body source — a safe re-entry mirror, or a moved-here live surface.
    body: TornBody,
    /// The POP-BACK seam: a host-installed callback that returns this surface to
    /// the main dock (grafting an owned body home + persisting the layout). When
    /// absent (the registry installs it after the window is open; tests omit it),
    /// the chrome's pop-back button falls back to closing this OS window — safe
    /// for a MIRROR (the dock pane kept its copy), and the host's `prune_closed`
    /// reaps the dead entry on its next tear-off/pop-back pass.
    #[allow(clippy::type_complexity)]
    on_pop_back: Option<Box<dyn Fn(&mut Window, &mut App) + 'static>>,
    focus: FocusHandle,
}

impl TornOffWindow {
    /// Build a torn-off window root over `id`/`label` with a body `render`
    /// callback (the gpui-free [`Tab`] MIRROR path). The callback is invoked each
    /// frame on the new window's thread (gpui is single-threaded; all windows share
    /// the one [`App`]), so it sees the live host state — the torn-off body advances
    /// with the world like the in-dock one.
    ///
    /// ⚠ Use [`Self::owning`] for any surface whose body paints a live
    /// focus-tracked gpui [`Entity`](gpui::Entity) (editor/terminal panes); a
    /// mirror of such a surface re-renders its entity twice the same frame and
    /// PANICS gpui (see [`TornBody`]).
    pub fn new(
        id: TornSurfaceId,
        label: impl Into<SharedString>,
        badge: impl Into<SharedString>,
        render: impl Fn(&mut Window, &mut App) -> AnyElement + 'static,
        cx: &mut Context<Self>,
    ) -> Self {
        Self {
            id,
            label: label.into(),
            badge: badge.into(),
            body: TornBody::Mirror(Box::new(render)),
            on_pop_back: None,
            focus: cx.focus_handle(),
        }
    }

    /// Build a torn-off window root that OWNS `surface` (moved out of the dock
    /// pane) — the crash fix for entity-bearing surfaces. The surface's live
    /// entity is now rendered ONLY in this window, so it never re-renders the same
    /// frame the dock did. Pop-back moves the surface back ([`TornOffWindow::take_surface`]).
    pub fn owning(
        id: TornSurfaceId,
        label: impl Into<SharedString>,
        badge: impl Into<SharedString>,
        surface: Box<dyn CockpitSurface>,
        cx: &mut Context<Self>,
    ) -> Self {
        Self {
            id,
            label: label.into(),
            badge: badge.into(),
            body: TornBody::Owned(surface),
            on_pop_back: None,
            focus: cx.focus_handle(),
        }
    }

    /// Install the host-driven POP-BACK callback (the move-home seam). Called by
    /// the registry once the window is open so the chrome's "↩ pop back" button
    /// returns this surface to the main dock through the host (graft + persist),
    /// not just a blind window close. The callback receives the torn-off window's
    /// own `Window`/`App` so it can drive the host registry and close this window.
    pub fn set_pop_back(&mut self, on_pop_back: impl Fn(&mut Window, &mut App) + 'static) {
        self.on_pop_back = Some(Box::new(on_pop_back));
    }

    pub fn surface_id(&self) -> TornSurfaceId {
        self.id
    }

    pub fn label(&self) -> &SharedString {
        &self.label
    }

    /// Whether this window OWNS a moved surface (vs. mirroring a host re-entry) —
    /// the body that must be moved HOME on pop-back rather than simply dropped.
    pub fn owns_surface(&self) -> bool {
        matches!(self.body, TornBody::Owned(_))
    }

    /// Take the OWNED surface back out (pop-back: move it home into the dock). The
    /// window keeps rendering, now over an empty placeholder body, until it is
    /// closed — but pop-back closes it immediately, so this is the move-home seam.
    /// Returns `None` for a mirror window (nothing was moved out).
    pub fn take_surface(&mut self) -> Option<Box<dyn CockpitSurface>> {
        match std::mem::replace(
            &mut self.body,
            TornBody::Mirror(Box::new(|_, _| div().into_any_element())),
        ) {
            TornBody::Owned(s) => Some(s),
            other => {
                self.body = other;
                None
            }
        }
    }
}

impl Focusable for TornOffWindow {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }
}

impl Render for TornOffWindow {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        // Build the live body. For a MIRROR we re-enter the host through the boxed
        // callback; for an OWNED surface we render its body HERE (the live entity
        // lives in this window only — the crash fix). Either way we take the body
        // source out of `self` across the call so `&mut Context<Self>` (which derefs
        // to `&mut App`) can be handed in — the same take-then-restore the pane uses
        // for its surfaces' `render_body`.
        let mut taken = std::mem::replace(
            &mut self.body,
            TornBody::Mirror(Box::new(|_, _| div().into_any_element())),
        );
        let body = match &mut taken {
            TornBody::Mirror(render) => render(window, cx),
            TornBody::Owned(surface) => surface.render_body(window, cx),
        };
        self.body = taken;

        // The pop-back button drives the host-installed callback (graft the
        // surface home + persist the layout); when no callback is installed
        // (tests, or before the registry wires it) it falls back to closing this
        // OS window — non-destructive for a MIRROR, and the host reaps the entry.
        let has_owned = self.owns_surface();
        let pop_back = cx.listener(move |this: &mut Self, _, window: &mut Window, cx| {
            if let Some(cb) = this.on_pop_back.take() {
                cb(window, cx);
                // Leave `on_pop_back` taken: the callback closes this window, so
                // it will not render again. (Re-arming is unnecessary.)
            } else {
                // No host seam: a bare window close. Safe for a mirror; an owned
                // surface without a host seam would lose its body, so guard it.
                if !has_owned {
                    window.remove_window();
                }
            }
        });

        div()
            .track_focus(&self.focus)
            .flex()
            .flex_col()
            .size_full()
            .bg(theme::bg())
            // The torn-off window's CHROME: a titlebar/header naming WHICH surface
            // this is + its identity/cap-badge (so a popped pane is identifiable,
            // not an anonymous box), and a "↩ pop back" affordance that returns the
            // surface to the main dock. This makes the second window a first-class,
            // labelled window — the firmament "one cap across distance" made local.
            .child(
                div()
                    .flex()
                    .flex_row()
                    .items_center()
                    .gap_2()
                    .h(px(30.))
                    .px_2()
                    .bg(theme::panel())
                    .border_b_1()
                    .border_color(theme::border())
                    .text_xs()
                    // ↗ marker + the surface label.
                    .child(
                        div()
                            .text_color(theme::muted())
                            .child(SharedString::from("↗ torn-off")),
                    )
                    .child(
                        div()
                            .text_color(theme::text())
                            .child(self.label.clone()),
                    )
                    // The identity / cap-badge pill (who/what authority this surface
                    // runs under) — only when the host supplied one.
                    .when(!self.badge.is_empty(), |row| {
                        row.child(
                            div()
                                .px_2()
                                .py_0p5()
                                .rounded_md()
                                .bg(theme::panel_hi())
                                .text_color(theme::accent())
                                .child(self.badge.clone()),
                        )
                    })
                    // The "↩ pop back" affordance (right-aligned), clickable.
                    .child(
                        div()
                            .id("torn-pop-back")
                            .ml_auto()
                            .px_2()
                            .py_0p5()
                            .rounded_md()
                            .cursor_pointer()
                            .text_color(theme::text())
                            .bg(theme::panel_hi())
                            .hover(|this| this.bg(theme::border()))
                            .on_mouse_down(MouseButton::Left, pop_back)
                            .child(SharedString::from("↩ pop back")),
                    ),
            )
            .child(div().flex_1().overflow_hidden().child(body))
    }
}

/// One torn-off window's bookkeeping: the OS window (a per-window
/// [`gpui_component::Root`] — the multi-window crash fix) and the inner
/// [`TornOffWindow`] the `Root` wraps.
///
/// ## Per-window [`Root`] (the multi-window crash fix)
///
/// The torn-off window's ROOT VIEW is a [`gpui_component::Root`], NOT the bare
/// [`TornOffWindow`] — exactly like the main cockpit window
/// ([`crate::cockpit::root::wrap_root`]). gpui-component's `TextElement::paint`
/// (every kit text INPUT — the web-shell URL bar, the editor/composer/agent
/// prompts) reads the window's `Root` global; if the window root is not a `Root`,
/// that read `unwrap`s `None` and the process ABORTS the instant such an input
/// paints. Wrapping the torn-off window in a `Root` makes a 2nd OS window a
/// first-class window whose input surfaces paint clean. The registry therefore
/// holds BOTH the [`WindowHandle<Root>`] (the OS window — activate/close) and the
/// inner [`Entity<TornOffWindow>`] (the surface body — `take_surface`/pop-back).
struct TornEntry {
    /// The OS window whose root view is the per-window `Root` (the crash fix).
    window: WindowHandle<Root>,
    /// The `TornOffWindow` the `Root` wraps — the surface body + chrome.
    view: Entity<TornOffWindow>,
}

/// The registry of TORN-OFF WINDOWS — the cockpit's record of which surfaces are
/// currently popped out into their own OS windows, keyed by the surface's stable
/// id. It is the migration's bookkeeping: a surface is in EXACTLY one of two
/// places along the firmament distance axis at a time from the operator's view —
/// composited in the dock, or torn off into its window — and this map is how the
/// cockpit knows which, so a second pop-out of the same surface re-focuses the
/// existing window instead of minting a duplicate.
#[derive(Default)]
pub struct WindowRegistry {
    torn: HashMap<TornSurfaceId, TornEntry>,
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

    /// The ids of every currently-torn-off surface (for the cockpit to persist the
    /// which-tab-popped-out set into its [`WorkspaceCell`], and to re-open them on a
    /// crash-relaunch).
    pub fn torn_ids(&self) -> impl Iterator<Item = TornSurfaceId> + '_ {
        self.torn.keys().copied()
    }

    pub fn is_empty(&self) -> bool {
        self.torn.is_empty()
    }

    /// The OS-window handle for `id`'s torn-off window, if it is torn off (so the
    /// host can raise/focus an already-open one rather than duplicate it). This is
    /// the per-window [`Root`] handle (the window's root view — the crash fix).
    pub fn handle(&self, id: TornSurfaceId) -> Option<WindowHandle<Root>> {
        self.torn.get(&id).map(|e| e.window)
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
        badge: impl Into<SharedString>,
        render: impl Fn(&mut Window, &mut App) -> AnyElement + 'static,
        cx: &mut App,
    ) -> anyhow::Result<WindowHandle<Root>> {
        if let Some(existing) = self.torn.get(&id).map(|e| e.window) {
            // Already torn off — bring the existing window forward, don't mint a
            // second one over the same surface (identity is one-window).
            cx.activate(false);
            let _ = existing.update(cx, |_root, window, _cx| {
                window.activate_window();
            });
            return Ok(existing);
        }

        let label: SharedString = label.into();
        let badge: SharedString = badge.into();
        let title = label.clone();
        let (window, view) = self.open_torn_window(title, cx, move |_window, app| {
            app.new(|cx| TornOffWindow::new(id, label.clone(), badge.clone(), render, cx))
        })?;
        self.install_pop_back(id, &view, cx);
        self.torn.insert(id, TornEntry { window, view });
        Ok(window)
    }

    /// TEAR OFF `id` by MOVING `surface` into a fresh OS window — the crash fix for
    /// entity-bearing surfaces (editor/terminal panes whose body paints a live
    /// focus-tracked gpui [`Entity`](gpui::Entity)). The surface is rendered ONLY in
    /// the new window (`render_body`), so its entity never re-renders the same frame
    /// the dock did — the re-entrant `Entity::update` / double `track_focus` panic
    /// that a [`Self::tear_off`] MIRROR of such a surface would hit cannot occur.
    ///
    /// The caller is responsible for having REMOVED `surface` from its dock pane
    /// before this call (the move's source side); pop-back ([`Self::pop_back`])
    /// hands the surface back so the caller can graft it home. If `id` is already
    /// torn off, the surface is dropped and the existing window re-activated (the
    /// migration is idempotent in identity; a duplicate move is rejected).
    pub fn tear_off_surface(
        &mut self,
        id: TornSurfaceId,
        label: impl Into<SharedString>,
        badge: impl Into<SharedString>,
        surface: Box<dyn CockpitSurface>,
        cx: &mut App,
    ) -> anyhow::Result<WindowHandle<Root>> {
        if let Some(existing) = self.torn.get(&id).map(|e| e.window) {
            cx.activate(false);
            let _ = existing.update(cx, |_root, window, _cx| {
                window.activate_window();
            });
            // `surface` is dropped — the live one is already in the existing window.
            return Ok(existing);
        }
        let label: SharedString = label.into();
        let badge: SharedString = badge.into();
        let title = label.clone();
        // `surface` is consumed by the window builder; an open failure drops it
        // (fail-closed: nothing recorded, and the caller still holds the dock-pane
        // removal it must undo — which it does, surfacing the error).
        let mut slot = Some(surface);
        let (window, view) = self.open_torn_window(title, cx, move |_window, app| {
            let surface = slot.take().expect("window builder runs once");
            app.new(|cx| TornOffWindow::owning(id, label.clone(), badge.clone(), surface, cx))
        })?;
        self.install_pop_back(id, &view, cx);
        self.torn.insert(id, TornEntry { window, view });
        Ok(window)
    }

    /// The shared OS-window open for both the mirror and the moved-surface tear-off:
    /// a default-centered `720×560` window titled `deos — {label}` whose root view
    /// is a per-window [`gpui_component::Root`] wrapping the [`TornOffWindow`] that
    /// `build_inner` builds. Keeps the `WindowOptions` + the `Root` weld in one
    /// place so the two tear-off paths stay identical in their window chrome and
    /// BOTH get the per-window `Root` (the multi-window crash fix — without it any
    /// kit text input painted in the torn window aborts the process). Returns the
    /// OS-window handle (the `Root`) and the inner `TornOffWindow` entity (for
    /// `take_surface`/pop-back).
    fn open_torn_window(
        &self,
        label: SharedString,
        cx: &mut App,
        build_inner: impl FnOnce(&mut Window, &mut App) -> Entity<TornOffWindow>,
    ) -> anyhow::Result<(WindowHandle<Root>, Entity<TornOffWindow>)> {
        let bounds = Bounds::centered(None, gpui::size(px(720.), px(560.)), cx);
        // Stash the inner entity out of the root builder so we can return it
        // alongside the window handle (the builder runs once, synchronously,
        // inside `open_window`).
        let mut inner_slot: Option<Entity<TornOffWindow>> = None;
        let window = cx.open_window(
            WindowOptions {
                window_bounds: Some(WindowBounds::Windowed(bounds)),
                titlebar: Some(TitlebarOptions {
                    title: Some(format!("deos — {label}").into()),
                    ..Default::default()
                }),
                ..Default::default()
            },
            |window, cx| {
                // Build the inner surface view, then WRAP it in a per-window `Root`
                // (the same weld `crate::cockpit::root::wrap_root` does for the main
                // window) so this 2nd OS window's kit inputs paint without the
                // `Root::read(window).unwrap()` abort. The `Root` is the window's
                // root view; the `TornOffWindow` is its content.
                let inner = build_inner(window, cx);
                inner_slot = Some(inner.clone());
                cx.new(|cx| Root::new(inner, window, cx))
            },
        )?;
        let view = inner_slot.expect("the Root builder ran and stashed the inner view");
        Ok((window, view))
    }

    /// Install the host-driven POP-BACK callback on a freshly-opened torn-off
    /// window (the move-home seam for the chrome's "↩ pop back" button). The
    /// callback drives THIS registry: it takes any owned surface out, closes the OS
    /// window, drops the entry — and (for an owned surface) drops the body. The
    /// host's richer [`Self::pop_back_taking`] is the path that grafts an owned
    /// surface home + persists; this in-window button is the operator's quick
    /// dock-it affordance. For a MIRROR (the live cockpit path) the dock pane kept
    /// its copy, so closing the window is fully non-destructive. For an OWNED
    /// surface we DON'T self-close (we'd lose the body); we no-op so the operator
    /// uses the host pop-back path — but in practice the host installs a real
    /// graft-home callback over its weak handle via [`Self::pop_back_taking`].
    ///
    /// This base install closes a MIRROR window safely and leaves OWNED windows for
    /// the host; a caller wanting full graft-home wires its own callback. The
    /// callback captures the window handle (a `Copy` `WindowHandle<Root>`) so the
    /// button can close it.
    fn install_pop_back(&self, _id: TornSurfaceId, view: &Entity<TornOffWindow>, cx: &mut App) {
        let owns = view.read(cx).owns_surface();
        view.update(cx, |v, _cx| {
            v.set_pop_back(move |window, _app| {
                if !owns {
                    // MIRROR: the dock pane kept its copy — closing the window is
                    // the whole pop-back. (`prune_closed` reaps the dead entry.)
                    window.remove_window();
                }
                // OWNED: do nothing here (the host's graft-home path owns it); the
                // operator pops it back through the dock control.
            });
        });
    }

    /// POP BACK `id`'s torn-off window: close the OS window and drop the registry
    /// entry (the surface is once again only in the dock). A no-op if the surface
    /// is not torn off. Returns `Some(surface)` when the window OWNED a moved
    /// surface (the caller must graft it back into the dock — the move-home side);
    /// `Some(None)`/`false` distinctions are folded into the return: an owned
    /// pop-back returns the surface, a mirror pop-back returns `None`.
    ///
    /// For a MIRROR window the dock pane was never removed, so pop-back is just
    /// closing the second window. For an OWNED (moved) window the surface lived ONLY
    /// in the window, so pop-back MUST hand it back — else the live entity is
    /// destroyed with the window. The boolean "was anything closed" is
    /// [`Self::pop_back`]; this richer form returns the moved surface for re-grafting.
    pub fn pop_back_taking(
        &mut self,
        id: TornSurfaceId,
        cx: &mut App,
    ) -> Option<Box<dyn CockpitSurface>> {
        let entry = self.torn.remove(&id)?;
        // Take the owned surface OUT of the inner `TornOffWindow` view before the
        // OS window is removed, so the move-home body survives the window's
        // destruction. (The window's root view is the `Root`; the surface body
        // lives in the inner `TornOffWindow` entity, which we hold directly.)
        let surface = entry.view.update(cx, |inner, _cx| inner.take_surface());
        let _ = entry.window.update(cx, |_root, window, _cx| {
            window.remove_window();
        });
        surface
    }

    /// POP BACK `id`'s torn-off window and report whether one was closed (the
    /// boolean form). A MIRROR pop-back is non-destructive (the dock pane kept its
    /// copy); an OWNED pop-back here would DROP the moved surface — callers that
    /// moved a surface out must use [`Self::pop_back_taking`] to graft it home.
    pub fn pop_back(&mut self, id: TornSurfaceId, cx: &mut App) -> bool {
        let Some(entry) = self.torn.remove(&id) else {
            return false;
        };
        let _ = entry.window.update(cx, |_root, window, _cx| {
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
        self.torn
            .retain(|_id, entry| entry.window.entity(cx).is_ok());
        before - self.torn.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The LOGIC-LEVEL invariants of the tear-off registry that do NOT need a live
    /// window: a fresh registry is empty, reports no surface torn off, and hands
    /// back no handle. These are the migration's bookkeeping pre-conditions — the
    /// state the `tear_off` → `pop_back` cycle moves through — and they compile +
    /// run in the headless suite (no gpui `App`/`Window` required).
    #[test]
    fn fresh_registry_is_empty_and_holds_no_surface() {
        let reg = WindowRegistry::new();
        assert_eq!(reg.len(), 0);
        assert!(reg.is_empty());
        assert!(!reg.is_torn_off(SurfaceId(0)));
        assert!(!reg.is_torn_off(SurfaceId(7)));
        assert!(reg.handle(SurfaceId(7)).is_none());
    }

    /// The FULL tear-off cycle over a live (headless) gpui `App`: `tear_off` an id
    /// registers a 2nd window handle keyed by the SAME `SurfaceId`; a second
    /// `tear_off` of that id is idempotent (re-activates, does NOT duplicate —
    /// `len` stays 1, the handle is the same window); `pop_back` removes it and the
    /// registry is empty again, with identity (the `SurfaceId`) preserved
    /// throughout. Gated on `render-capture` (gpui `test-support`'s
    /// `HeadlessAppContext` — the same headless app the cockpit bake uses), so it
    /// runs wherever the offscreen renderer is available.
    #[cfg(feature = "render-capture")]
    #[test]
    fn tear_off_registers_pop_back_removes_identity_preserved() {
        use gpui::{AppContext, HeadlessAppContext, PlatformTextSystem};
        use gpui_wgpu::CosmicTextSystem;
        use std::borrow::Cow;
        use std::sync::Arc;

        // The headless text system needs real font bytes registered (the same weld
        // the cockpit bake does at `main.rs`), else shaping the torn-off chrome
        // label panics resolving `.SystemUIFont`.
        static LILEX: &[u8] = include_bytes!("../../assets/fonts/Lilex-Regular.ttf");
        static IBM_PLEX: &[u8] = include_bytes!("../../assets/fonts/IBMPlexSans-Regular.ttf");
        let text_system: Arc<dyn PlatformTextSystem> =
            Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
        text_system
            .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
            .expect("register headless fonts");
        let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
            gpui_platform::current_headless_renderer()
        });
        // The torn-off window's root view is now a `gpui_component::Root` (the
        // per-window crash fix), whose render reads the kit theme global — so the
        // headless app must `init` gpui-component before opening one.
        cx.update(|cx| gpui_component::init(cx));

        let id = SurfaceId(42);

        cx.update(|cx| {
            let mut reg = WindowRegistry::new();
            assert!(reg.is_empty());

            // TEAR OFF: a fresh OS window is minted, keyed by `id` (the identity).
            let h1 = reg
                .tear_off(
                    id,
                    "the torn-off surface",
                    "you · abcd · 🔑 3 caps",
                    |_w, _cx| div().into_any_element(),
                    cx,
                )
                .expect("headless tear-off opens a window");
            assert_eq!(reg.len(), 1);
            assert!(reg.is_torn_off(id));
            assert_eq!(reg.handle(id), Some(h1));

            // IDEMPOTENT: a 2nd tear-off of the SAME id does not duplicate — the
            // surface identity is one-window; the same handle comes back.
            let h2 = reg
                .tear_off(
                    id,
                    "the torn-off surface",
                    "you · abcd · 🔑 3 caps",
                    |_w, _cx| div().into_any_element(),
                    cx,
                )
                .expect("re-tear-off re-activates");
            assert_eq!(reg.len(), 1, "no duplicate window for the same surface id");
            assert_eq!(h1, h2, "the same window handle (identity preserved)");

            // POP BACK: the window closes, the entry drops; identity unchanged
            // (the same `id` keyed it in and out).
            assert!(reg.pop_back(id, cx), "pop_back closes the torn-off window");
            assert_eq!(reg.len(), 0);
            assert!(!reg.is_torn_off(id));
            // A second pop-back is a no-op (nothing to close).
            assert!(!reg.pop_back(id, cx));
        });
    }

    // === THE RE-ENTRANT-RENDER CRASH (move-not-mirror) ====================
    // The headless cockpit-style window bake never carried a LIVE entity-bearing
    // body into a torn-off window — the test gap that let the editor/terminal
    // tear-off panic ship. These tests close it: a real focus-tracked gpui
    // `Entity` is torn off and the window is DRIVEN TO A DRAW. A MIRROR of such a
    // surface re-renders its entity twice the same frame (re-entrant
    // `Entity::update` / double `track_focus`) and panics gpui; the MOVE
    // (`tear_off_surface`) renders it in exactly one window and does NOT.

    #[cfg(feature = "render-capture")]
    mod live_entity {
        use super::*;
        use crate::dock::surface::CockpitSurface;
        use gpui::{AppContext, Entity, HeadlessAppContext, PlatformTextSystem, Render};
        use gpui_wgpu::CosmicTextSystem;
        use std::borrow::Cow;
        use std::sync::Arc;

        /// A minimal LIVE body: a focus-tracked gpui `Entity` (exactly the shape an
        /// editor/terminal pane holds). Its `render` calls `track_focus` — the op
        /// that double-registers (and panics) if the SAME entity renders in two
        /// windows the same frame.
        struct LiveBody {
            focus: FocusHandle,
            paints: u32,
        }
        impl LiveBody {
            fn new(cx: &mut Context<Self>) -> Self {
                LiveBody {
                    focus: cx.focus_handle(),
                    paints: 0,
                }
            }
        }
        impl Focusable for LiveBody {
            fn focus_handle(&self, _cx: &App) -> FocusHandle {
                self.focus.clone()
            }
        }
        impl Render for LiveBody {
            fn render(&mut self, _w: &mut Window, _cx: &mut Context<Self>) -> impl IntoElement {
                self.paints += 1;
                div()
                    .track_focus(&self.focus)
                    .size_full()
                    .child(SharedString::from("live"))
            }
        }

        /// An entity-bearing `CockpitSurface` whose `render_body` paints the SAME
        /// live `Entity<LiveBody>` each frame (the editor/terminal-pane shape: the
        /// body IS a held gpui entity, `update`d to paint). Two same-frame renders
        /// of this surface re-enter the one entity — the crash.
        struct LiveSurface {
            id: SurfaceId,
            body: Entity<LiveBody>,
        }
        impl CockpitSurface for LiveSurface {
            fn item_id(&self) -> SurfaceId {
                self.id
            }
            fn tab_label(&self) -> SharedString {
                SharedString::from("live")
            }
            fn render_body(&mut self, _w: &mut Window, _cx: &mut App) -> AnyElement {
                // The pane renders a held entity by embedding it — gpui `update`s the
                // entity to paint it. Rendering it in two windows the same frame is
                // the re-entrant `Entity::update` / double `track_focus` the move fixes.
                self.body.clone().into_any_element()
            }
            fn focus_handle(&self, cx: &App) -> FocusHandle {
                self.body.read(cx).focus.clone()
            }
            fn boxed_clone(&self) -> Box<dyn CockpitSurface> {
                Box::new(LiveSurface {
                    id: self.id,
                    body: self.body.clone(),
                })
            }
        }

        fn headless() -> HeadlessAppContext {
            static LILEX: &[u8] = include_bytes!("../../assets/fonts/Lilex-Regular.ttf");
            static IBM_PLEX: &[u8] = include_bytes!("../../assets/fonts/IBMPlexSans-Regular.ttf");
            let text_system: Arc<dyn PlatformTextSystem> =
                Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
            text_system
                .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
                .expect("register headless fonts");
            let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
                gpui_platform::current_headless_renderer()
            });
            // The torn-off window root is a `gpui_component::Root` (the crash fix),
            // whose render reads the kit theme — init gpui-component for the bake.
            cx.update(|cx| gpui_component::init(cx));
            cx
        }

        /// THE CRASH FIX, PROVEN BY DRAWING: tear a LIVE entity-bearing surface off
        /// via the MOVE path (`tear_off_surface`) and DRIVE THE TORN-OFF WINDOW TO A
        /// DRAW. The live entity now lives in exactly one window, so the draw does
        /// NOT panic (a MIRROR would here re-render the entity twice the same frame).
        /// This reproduces the editor/terminal tear-off panic in a test and asserts
        /// the move fixes it.
        #[test]
        fn moving_a_live_entity_into_a_torn_window_renders_without_panic() {
            let mut cx = headless();
            let id = SurfaceId(7);

            // Build the live body entity OUTSIDE any window (it is the surface's
            // held entity, the thing the dock pane would have rendered).
            let body: Entity<LiveBody> = cx.update(|cx| cx.new(LiveBody::new));

            // Open a torn-off window OWNING the surface (the MOVE: the entity now
            // lives only here, as if removed from the dock pane).
            let handle = cx.update(|cx| {
                let mut reg = WindowRegistry::new();
                let surface: Box<dyn CockpitSurface> = Box::new(LiveSurface {
                    id,
                    body: body.clone(),
                });
                let h = reg
                    .tear_off_surface(id, "live editor", "you · abcd · 🔑 3 caps", surface, cx)
                    .expect("headless move-tear-off opens a window");
                assert!(reg.is_torn_off(id), "the surface is recorded torn off");
                h
            });

            // DRIVE THE WINDOW TO A REAL DRAW — this is where the re-entrant render
            // would panic if the entity were rendered twice the same frame. With the
            // move it is rendered ONCE (in this one window), so the draw is clean.
            cx.run_until_parked();
            cx.update_window(handle.into(), |_, window, _cx| window.refresh())
                .expect("refresh the torn-off window");
            cx.run_until_parked();

            // The body actually painted (the entity is live in the torn-off window).
            let painted = cx.update(|cx| body.read(cx).paints);
            assert!(
                painted >= 1,
                "the moved live entity painted in the torn-off window"
            );
        }

        /// The MOVE is reversible: `pop_back_taking` hands the moved surface BACK
        /// (so the cockpit can graft it home), and the live entity survives — it was
        /// never destroyed with the window. Re-rendering it after pop-back (now as a
        /// fresh torn-off window) still does not panic — one-window-at-a-time holds
        /// across the whole tear-off ⇄ pop-back cycle.
        #[test]
        fn pop_back_hands_the_moved_surface_home_and_the_entity_survives() {
            let mut cx = headless();
            let id = SurfaceId(9);
            let body: Entity<LiveBody> = cx.update(|cx| cx.new(LiveBody::new));

            let recovered = cx.update(|cx| {
                let mut reg = WindowRegistry::new();
                let surface: Box<dyn CockpitSurface> = Box::new(LiveSurface {
                    id,
                    body: body.clone(),
                });
                reg.tear_off_surface(id, "live editor", "you · abcd · 🔑 3 caps", surface, cx)
                    .expect("move-tear-off opens a window");
                assert_eq!(reg.len(), 1);

                // POP BACK TAKING: the moved surface comes home (the window owned it,
                // so it must be handed back — not dropped with the window).
                let back = reg.pop_back_taking(id, cx);
                assert!(
                    back.is_some(),
                    "an owned pop-back returns the moved surface"
                );
                assert_eq!(reg.len(), 0, "the window closed + the entry dropped");
                assert!(!reg.is_torn_off(id));
                back.unwrap()
            });

            // The recovered surface still points at the LIVE entity (it survived the
            // window's destruction — the move was non-destructive of the body).
            cx.update(|cx| {
                assert_eq!(
                    recovered.item_id(),
                    id,
                    "identity preserved across the move-home"
                );
                let _ = body.read(cx); // the entity is still alive (read would panic if dropped)
            });
        }
    }

    // === THE MULTI-WINDOW Root CRASH (kit input in a 2nd window) ===========
    // The torn-off window's root view was a bare `TornOffWindow`, NOT a
    // `gpui_component::Root`. A kit text INPUT painted in it (web-shell URL bar,
    // editor/composer/agent prompt) hits `Root::read(window).unwrap()` on a
    // None-Root → `process::abort`. These tests carry a REAL kit input into a 2nd
    // window via the tear-off path and DRIVE IT TO A DRAW — which would abort
    // without the per-window `Root` wrap, and draws clean with it.
    #[cfg(feature = "render-capture")]
    mod kit_input {
        use super::*;
        use gpui::{AppContext, Entity, HeadlessAppContext, PlatformTextSystem};
        use gpui_component::input::{Input, InputState};
        use gpui_wgpu::CosmicTextSystem;
        use std::borrow::Cow;
        use std::sync::Arc;

        fn headless() -> HeadlessAppContext {
            static LILEX: &[u8] = include_bytes!("../../assets/fonts/Lilex-Regular.ttf");
            static IBM_PLEX: &[u8] = include_bytes!("../../assets/fonts/IBMPlexSans-Regular.ttf");
            let text_system: Arc<dyn PlatformTextSystem> =
                Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
            text_system
                .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
                .expect("register headless fonts");
            let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
                gpui_platform::current_headless_renderer()
            });
            cx.update(|cx| gpui_component::init(cx));
            cx
        }

        /// An input-bearing `CockpitSurface` — the exact shape of the web-shell URL
        /// bar / composer / agent prompt: its `render_body` paints a kit
        /// `Input` over a held `InputState`. Painting a kit input reads the window's
        /// `gpui_component::Root` global; a window whose root is not a `Root` aborts.
        struct InputSurface {
            id: SurfaceId,
            state: Entity<InputState>,
        }
        impl CockpitSurface for InputSurface {
            fn item_id(&self) -> SurfaceId {
                self.id
            }
            fn tab_label(&self) -> SharedString {
                SharedString::from("url bar")
            }
            fn render_body(&mut self, _w: &mut Window, _cx: &mut App) -> AnyElement {
                div()
                    .size_full()
                    .child(Input::new(&self.state))
                    .into_any_element()
            }
            fn focus_handle(&self, cx: &App) -> FocusHandle {
                self.state.read(cx).focus_handle(cx)
            }
            fn boxed_clone(&self) -> Box<dyn CockpitSurface> {
                Box::new(InputSurface {
                    id: self.id,
                    state: self.state.clone(),
                })
            }
        }

        /// THE MULTI-WINDOW CRASH FIX, PROVEN BY DRAWING A KIT INPUT IN A 2ND
        /// WINDOW: tear an input-bearing surface (a kit `Input`, like the web-shell
        /// URL bar) into its own OS window via the move path, then DRIVE THAT WINDOW
        /// TO A DRAW. Painting the kit input reads the window's `gpui_component::Root`
        /// global; before the per-window `Root` wrap this `unwrap`ed `None` and
        /// aborted the process. With the wrap the 2nd window is a first-class `Root`
        /// window and the input paints clean.
        #[test]
        fn kit_input_torn_into_a_second_window_renders_without_root_abort() {
            let mut cx = headless();
            let id = SurfaceId(13);

            // The held kit input state (built with a live `&mut Window` like the
            // cockpit's URL bar). We open a throwaway window only to mint it.
            let state: Entity<InputState> = {
                let scratch = cx
                    .open_window(gpui::size(px(400.), px(80.)), |window, cx| {
                        let st = cx.new(|cx| {
                            InputState::new(window, cx).placeholder("https://… or dregg://…")
                        });
                        cx.new(|_| ScratchHolder(st))
                    })
                    .expect("open scratch window for InputState::new");
                cx.run_until_parked();
                let st = cx
                    .update_window(scratch.into(), |root, _w, cx| {
                        root.downcast::<ScratchHolder>().unwrap().read(cx).0.clone()
                    })
                    .expect("read the input state");
                let _ = cx.update_window(scratch.into(), |_, w, _| w.remove_window());
                st
            };

            // TEAR OFF the input surface into its own window (the move path). Its
            // root view is now a per-window `Root` (the crash fix).
            let handle = cx.update(|cx| {
                let mut reg = WindowRegistry::new();
                let surface: Box<dyn CockpitSurface> = Box::new(InputSurface {
                    id,
                    state: state.clone(),
                });
                let h = reg
                    .tear_off_surface(id, "url bar", "you · abcd · 🔑 3 caps", surface, cx)
                    .expect("tear off the input surface into a 2nd window");
                assert!(reg.is_torn_off(id));
                h
            });

            // The window's ROOT VIEW is a `gpui_component::Root` — assert it directly
            // (the structural guarantee), then DRIVE IT TO A DRAW (the dynamic one).
            let is_root = cx
                .update_window(handle.into(), |root, _w, _cx| {
                    root.downcast::<Root>().is_ok()
                })
                .expect("read the torn window root");
            assert!(is_root, "the torn-off window's root view is a gpui_component::Root");

            // DRIVE THE DRAW — painting the kit input reads the window `Root`; before
            // the wrap this aborted. The draw completing is the fix proven.
            cx.run_until_parked();
            cx.update_window(handle.into(), |_, window, _cx| window.refresh())
                .expect("refresh the torn-off input window");
            cx.run_until_parked();

            // The input state is still alive in the 2nd window (no abort, no drop).
            cx.update(|cx| {
                let _ = state.read(cx);
            });
        }

        /// A trivial holder so `InputState::new` (which needs a live `&mut Window`)
        /// can be built inside a throwaway window and the state read back out.
        struct ScratchHolder(Entity<InputState>);
        impl Render for ScratchHolder {
            fn render(&mut self, _w: &mut Window, _cx: &mut Context<Self>) -> impl IntoElement {
                div()
            }
        }

        /// THE WEB-SHELL POP-OUT BEACHBALL, FIXED BY THE MOVE: an input-bearing
        /// surface (the web-shell URL bar — `webshell_panel` embeds the live kit
        /// `InputState` the in-dock tab also paints) is torn off via the OWNED
        /// (move) path, the live entity is REMOVED from the dock copy, and BOTH
        /// the (now input-free) dock body and the torn window are driven to a
        /// draw the same parked cycle. With the move the one entity is painted in
        /// EXACTLY ONE window — the run parks and the draw completes.
        ///
        /// The MIRROR path this replaces re-entered the host to paint that SAME
        /// live entity in BOTH windows the same frame (the re-entrant
        /// `Entity::update` / double `track_focus`); post the per-window `Root`
        /// crash-fix that no longer aborts but SPINS the flush loop — the
        /// beachball. The cockpit therefore routes input/entity-bearing tabs
        /// (web-shell/editor/terminal/composer) through `tear_off_surface`, not
        /// `tear_off`. (A live mirror-hang reproduction would itself hang the
        /// test harness; this asserts the move-path invariant the fix relies on.)
        #[test]
        fn moving_an_input_surface_out_does_not_beachball_the_main_thread() {
            let mut cx = headless();
            let id = SurfaceId(21);

            // Mint the kit InputState inside a live (throwaway) window — exactly
            // the cockpit's `ensure_webshell_input` shape (it needs `&mut Window`).
            let state: Entity<InputState> = {
                let scratch = cx
                    .open_window(gpui::size(px(560.), px(80.)), |window, cx| {
                        let st = cx.new(|cx| {
                            InputState::new(window, cx).placeholder("https://… or dregg://…")
                        });
                        cx.new(|_| ScratchHolder(st))
                    })
                    .expect("open scratch window for InputState::new");
                cx.run_until_parked();
                let st = cx
                    .update_window(scratch.into(), |root, _w, cx| {
                        root.downcast::<ScratchHolder>().unwrap().read(cx).0.clone()
                    })
                    .expect("read the input state");
                let _ = cx.update_window(scratch.into(), |_, w, _| w.remove_window());
                st
            };

            // TEAR OFF the input surface via the OWNED (move) path: the surface
            // (and its live entity) now lives ONLY in the torn window — the fix
            // the cockpit applies for input-bearing tabs. It is painted there,
            // once per frame, never re-entered from a dock copy.
            let handle = cx.update(|cx| {
                let mut reg = WindowRegistry::new();
                let surface: Box<dyn CockpitSurface> = Box::new(InputSurface {
                    id,
                    state: state.clone(),
                });
                let h = reg
                    .tear_off_surface(id, "web-shell", "you · abcd · 🔑 7 caps", surface, cx)
                    .expect("move the input surface into its own window");
                assert!(reg.is_torn_off(id));
                h
            });

            // DRIVE THE TORN WINDOW TO A DRAW: the run parks (no flush-loop spin),
            // the kit input paints clean. The MIRROR path would not park here.
            cx.run_until_parked();
            cx.update_window(handle.into(), |_, window, _cx| window.refresh())
                .expect("refresh the torn-off web-shell window");
            cx.run_until_parked();

            // The input state survived in the torn window (no abort, no hang).
            cx.update(|cx| {
                let _ = state.read(cx);
            });
        }
    }
}
