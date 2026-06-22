//! A slim [`Dock`] — the Left/Bottom/Right edge container, adapted (heavily
//! trimmed) from Zed's `workspace::dock`.
//!
//! A dock is an edge strip that holds one or more [`DockPanel`]s and shows the
//! active one. It renders a 6px [`DraggedDock`] resize handle on its inner edge
//! (a `cursor_col_resize`/`cursor_row_resize` strip that emits a drag event the
//! host workspace turns into a width/height change).
//!
//! TRIMMED vs Zed (which is ~56K of editor-bound machinery): the
//! `SettingsStore`/`TerminalDockPosition` observers, the `proto::PanelId` remote
//! identity, the collab/zoom/modal-layer plumbing, the `PanelHandle` Arc<dyn>
//! erasure with its three `Subscription`s per entry, the `PanelButtons` status
//! strip, and the persistence (`DockData`/`serialized_dock`). What remains is the
//! position + open/active state + the resize handle, which is the integration
//! seam a cockpit dock needs.
//!
//! Panels here are hosted as [`Entity<Pane>`](super::pane::Pane) so a dock can
//! itself hold a tabbed, even splittable, surface — the same currency the
//! central [`PaneGroup`](super::pane_group::PaneGroup) uses.

use gpui::{
    deferred, div, prelude::*, px, App, Context, Entity, EventEmitter, FocusHandle, Focusable,
    IntoElement, MouseButton, MouseDownEvent, MouseUpEvent, Pixels, Render, StyleRefinement,
    Window,
};

use super::pane::Pane;
use super::theme;

pub const RESIZE_HANDLE_SIZE: Pixels = px(6.);

/// Which edge a dock lives on.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DockPosition {
    Left,
    Bottom,
    Right,
}

impl DockPosition {
    pub fn label(&self) -> &'static str {
        match self {
            Self::Left => "Left",
            Self::Bottom => "Bottom",
            Self::Right => "Right",
        }
    }

    /// The axis the dock resizes along.
    pub fn axis(&self) -> gpui::Axis {
        match self {
            Self::Left | Self::Right => gpui::Axis::Horizontal,
            Self::Bottom => gpui::Axis::Vertical,
        }
    }
}

/// Emitted by the resize handle's `on_drag`. The host workspace listens for this
/// (and the mouse position) to recompute the dock's size along its axis. Carries
/// the dock's position so a single workspace-level handler can route the drag.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DraggedDock(pub DockPosition);

impl Render for DraggedDock {
    fn render(&mut self, _: &mut Window, _: &mut Context<Self>) -> impl IntoElement {
        // A drag preview element; the actual resize is computed by the host from
        // the pointer position, so this paints nothing.
        div()
    }
}

/// A dockable panel. The cockpit's slim analogue of Zed's `Panel` trait, shorn
/// of the proto remote-id, settings, zoom, and icon-button machinery.
pub trait DockPanel: 'static {
    /// A stable name for the panel (used as the dispatch/key context).
    fn panel_name(&self) -> &'static str;
    /// The pane that renders this panel's body.
    fn pane(&self) -> Entity<Pane>;
    /// The panel's default size along the dock axis.
    fn default_size(&self) -> Pixels;
    /// The panel's minimum size along the dock axis.
    fn min_size(&self) -> Pixels {
        px(120.)
    }
}

struct PanelEntry {
    panel: Box<dyn DockPanel>,
    /// Current size along the dock axis (width for L/R, height for Bottom).
    size: Pixels,
}

/// An edge strip hosting one or more [`DockPanel`]s.
pub struct Dock {
    position: DockPosition,
    panel_entries: Vec<PanelEntry>,
    is_open: bool,
    active_panel_index: Option<usize>,
    focus_handle: FocusHandle,
}

impl EventEmitter<DraggedDock> for Dock {}

impl Focusable for Dock {
    fn focus_handle(&self, _: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl Dock {
    pub fn new(position: DockPosition, cx: &mut Context<Self>) -> Self {
        Self {
            position,
            panel_entries: Vec::new(),
            is_open: false,
            active_panel_index: None,
            focus_handle: cx.focus_handle(),
        }
    }

    pub fn position(&self) -> DockPosition {
        self.position
    }

    pub fn is_open(&self) -> bool {
        self.is_open
    }

    pub fn set_open(&mut self, open: bool, cx: &mut Context<Self>) {
        if self.is_open != open {
            self.is_open = open;
            cx.notify();
        }
    }

    pub fn add_panel(&mut self, panel: Box<dyn DockPanel>, cx: &mut Context<Self>) -> usize {
        let size = panel.default_size();
        let index = self.panel_entries.len();
        self.panel_entries.push(PanelEntry { panel, size });
        if self.active_panel_index.is_none() {
            self.active_panel_index = Some(index);
            self.is_open = true;
        }
        cx.notify();
        index
    }

    pub fn activate_panel(&mut self, index: usize, cx: &mut Context<Self>) {
        if index < self.panel_entries.len() {
            self.active_panel_index = Some(index);
            cx.notify();
        }
    }

    pub fn active_panel_index(&self) -> Option<usize> {
        self.active_panel_index
    }

    fn visible_entry(&self) -> Option<&PanelEntry> {
        if !self.is_open {
            return None;
        }
        self.active_panel_index.and_then(|ix| self.panel_entries.get(ix))
    }

    /// Set the active panel's size along the dock axis (clamped to min). `None`
    /// resets to the panel's default — the double-click behaviour.
    pub fn resize_active_panel(&mut self, size: Option<Pixels>, cx: &mut Context<Self>) {
        if let Some(entry) = self
            .active_panel_index
            .and_then(|ix| self.panel_entries.get_mut(ix))
        {
            let new = match size {
                Some(s) => s.max(entry.panel.min_size()).max(RESIZE_HANDLE_SIZE),
                None => entry.panel.default_size(),
            };
            entry.size = new;
            cx.notify();
        }
    }

    /// The active panel's current size along the dock axis.
    pub fn active_size(&self) -> Option<Pixels> {
        self.visible_entry().map(|e| e.size)
    }
}

impl Render for Dock {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let position = self.position;
        let dispatch_context = self
            .visible_entry()
            .map(|e| e.panel.panel_name())
            .unwrap_or("Dock");

        if let Some(entry) = self.visible_entry() {
            let pane = entry.panel.pane();
            let create_resize_handle = || {
                let handle = div()
                    .id("dock-resize-handle")
                    .on_drag(DraggedDock(position), |dock, _, _, cx| {
                        cx.stop_propagation();
                        cx.new(|_| dock.clone())
                    })
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(|_, _: &MouseDownEvent, _, cx| {
                            cx.stop_propagation();
                        }),
                    )
                    .on_mouse_up(
                        MouseButton::Left,
                        cx.listener(|dock, e: &MouseUpEvent, _window, cx| {
                            if e.click_count == 2 {
                                dock.resize_active_panel(None, cx);
                                cx.stop_propagation();
                            }
                        }),
                    )
                    .occlude();
                match position {
                    DockPosition::Left => deferred(
                        handle
                            .absolute()
                            .right(-RESIZE_HANDLE_SIZE / 2.)
                            .top(px(0.))
                            .h_full()
                            .w(RESIZE_HANDLE_SIZE)
                            .cursor_col_resize(),
                    ),
                    DockPosition::Bottom => deferred(
                        handle
                            .absolute()
                            .top(-RESIZE_HANDLE_SIZE / 2.)
                            .left(px(0.))
                            .w_full()
                            .h(RESIZE_HANDLE_SIZE)
                            .cursor_row_resize(),
                    ),
                    DockPosition::Right => deferred(
                        handle
                            .absolute()
                            .top(px(0.))
                            .left(-RESIZE_HANDLE_SIZE / 2.)
                            .h_full()
                            .w(RESIZE_HANDLE_SIZE)
                            .cursor_col_resize(),
                    ),
                }
            };

            div()
                .id("dock-panel")
                .key_context(dispatch_context)
                .track_focus(&self.focus_handle)
                .relative()
                .flex()
                .bg(theme::panel())
                .border_color(theme::border())
                .overflow_hidden()
                .map(|this| match position.axis() {
                    gpui::Axis::Horizontal => this.w_full().h_full().flex_row(),
                    gpui::Axis::Vertical => this.h_full().w_full().flex_col(),
                })
                .map(|this| match position {
                    DockPosition::Left => this.border_r_1(),
                    DockPosition::Right => this.border_l_1(),
                    DockPosition::Bottom => this.border_t_1(),
                })
                .child(
                    div()
                        .map(|this| match position.axis() {
                            gpui::Axis::Horizontal => this.w_full().h_full(),
                            gpui::Axis::Vertical => this.h_full().w_full(),
                        })
                        .child(
                            gpui::AnyView::from(pane)
                                .cached(StyleRefinement::default().flex().flex_col().size_full()),
                        ),
                )
                .child(create_resize_handle())
        } else {
            div()
                .id("dock-panel")
                .key_context(dispatch_context)
                .track_focus(&self.focus_handle)
        }
    }
}
