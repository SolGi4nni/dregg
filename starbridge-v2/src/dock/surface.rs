//! [`CockpitSurface`] — the slim item trait a [`Pane`](super::pane::Pane) hosts.
//!
//! Zed's `ItemHandle`/`Item` carry ~60 methods bound to a code editor's world
//! (`project_path`, `save`, `serialize`, `breadcrumbs`, `pixel_position_of_cursor`,
//! the navigation history, the searchable bar, …). None of that is meaningful for
//! a dregg cockpit surface, which is just "a labelled body that renders itself."
//!
//! So this trait is the cockpit-shaped ~8-method core: a tab label + tab content,
//! a render-body, identity, an activation hook, a focus handle, a dirty flag, and a
//! boxed clone so a surface can be moved between panes. A cockpit panel — each of
//! the `*_panel(cx)` closures in `cockpit.rs` — wraps itself as a `CockpitSurface`
//! to live inside a resizable/splittable [`Pane`].

use gpui::{AnyElement, App, FocusHandle, IntoElement, SharedString, Window};

/// A stable identity for a surface within a pane (used for tab activation,
/// removal, and active-item tracking). Cockpit code can derive these from the
/// existing `Tab` enum discriminant or any monotonic counter.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SurfaceId(pub u64);

impl SurfaceId {
    pub fn as_u64(self) -> u64 {
        self.0
    }
}

impl From<u64> for SurfaceId {
    fn from(v: u64) -> Self {
        SurfaceId(v)
    }
}

/// A hostable cockpit surface — the slim, cockpit-shaped analogue of Zed's
/// `ItemHandle`. Anything a [`Pane`](super::pane::Pane) can show in a tab and
/// render in its body.
///
/// Most methods have cockpit-friendly defaults; a minimal implementation needs
/// only [`CockpitSurface::item_id`], [`CockpitSurface::tab_label`],
/// [`CockpitSurface::render_body`], [`CockpitSurface::focus_handle`], and
/// [`CockpitSurface::boxed_clone`].
pub trait CockpitSurface: 'static {
    /// Stable identity within a pane.
    fn item_id(&self) -> SurfaceId;

    /// The short label shown in the tab strip. Returned as a `SharedString` so
    /// the tab-bar renderer stays object-safe (no `impl IntoElement` in the
    /// vtable). Cockpit panels return their `Tab::label()`.
    fn tab_label(&self) -> SharedString;

    /// Optional richer tab content (icon + label, a pill, a dirty dot). Defaults
    /// to the plain [`CockpitSurface::tab_label`] wrapped in a `div`. Override to
    /// paint a custom tab. The default is provided as an `AnyElement` so the
    /// trait stays object-safe.
    fn tab_content(&self, _window: &mut Window, _cx: &mut App) -> AnyElement {
        use gpui::{div, ParentElement};
        div().child(self.tab_label()).into_any_element()
    }

    /// Render the surface's body into the pane's content area. This is the
    /// cockpit's `*_panel(cx)` call: it returns the live element tree for the
    /// surface, rebuilt each frame from the running `World`.
    fn render_body(&mut self, window: &mut Window, cx: &mut App) -> AnyElement;

    /// The focus handle for this surface — the pane focuses it on activation.
    fn focus_handle(&self, cx: &App) -> FocusHandle;

    /// Called when the surface is deactivated (another tab/pane became active).
    /// Cockpit surfaces may flush transient view-state here. Default: no-op.
    fn deactivated(&mut self, _window: &mut Window, _cx: &mut App) {}

    /// Whether the surface has unsaved/uncommitted state worth a dirty marker in
    /// the tab. Default: clean.
    fn is_dirty(&self, _cx: &App) -> bool {
        false
    }

    /// Clone this surface into a fresh box (so it can be moved/duplicated across
    /// panes on split). A cockpit surface is a thin handle onto the shared
    /// `Rc<RefCell<World>>`, so the clone is cheap.
    fn boxed_clone(&self) -> Box<dyn CockpitSurface>;
}

impl Clone for Box<dyn CockpitSurface> {
    fn clone(&self) -> Self {
        self.boxed_clone()
    }
}
