//! A slim [`Pane`] — the ~15% core of Zed's `workspace::Pane`, adapted for the
//! dregg cockpit.
//!
//! A pane is a gpui [`Entity`] holding an ordered list of
//! [`CockpitSurface`](super::surface::CockpitSurface)s and an active index. It
//! renders a tab bar (one tab per surface) over the active surface's body. The
//! [`PaneGroup`](super::pane_group::PaneGroup) arranges panes into resizable
//! splits and renders each as `AnyView::from(pane.clone())`.
//!
//! STRIPPED from Zed's `Pane` (354K of editor-bound machinery): the
//! `WeakEntity<Project>`, diagnostics decorations, pinned/preview tabs, the
//! save/close confirmation modals, external-path drag-and-drop, the navigation
//! history, the searchable toolbar, and the ~30 registered actions. What remains
//! is the surface list + the swappable tab-bar/body render, which is all a
//! cockpit pane needs.

use std::mem;

use gpui::{
    div, prelude::*, px, App, Context, FocusHandle, Focusable, IntoElement, MouseButton,
    ParentElement, Render, SharedString, Styled, Window,
};

use super::surface::{CockpitSurface, SurfaceId};
use super::theme;

/// A horizontal stack of tabbed surfaces with one active body.
pub struct Pane {
    /// The hosted surfaces, in tab order.
    items: Vec<Box<dyn CockpitSurface>>,
    /// Index into [`Pane::items`] of the surface whose body is shown.
    active_item_index: usize,
    /// The pane's own focus handle (distinct from any surface's). Focusing the
    /// pane delegates to the active surface.
    focus_handle: FocusHandle,
    /// Set by [`PaneGroup::mark_positions`](super::pane_group::PaneGroup) so a
    /// pane knows whether it sits in the central group (vs a dock). Cosmetic.
    pub in_center_group: bool,
    /// A custom tab-bar renderer, swappable so the cockpit can theme tabs
    /// however it likes. `None` uses the built-in [`Pane::default_tab_bar`].
    #[allow(clippy::type_complexity)]
    render_tab_bar:
        Option<Box<dyn Fn(&mut Pane, &mut Window, &mut Context<Pane>) -> gpui::AnyElement>>,
}

impl Pane {
    /// Create an empty pane. Build it with [`Pane::add_item`].
    pub fn new(_window: &mut Window, cx: &mut Context<Self>) -> Self {
        Self {
            items: Vec::new(),
            active_item_index: 0,
            focus_handle: cx.focus_handle(),
            in_center_group: false,
            render_tab_bar: None,
        }
    }

    /// Construct a pane already populated with `items`, the first active.
    pub fn with_items(
        items: Vec<Box<dyn CockpitSurface>>,
        _window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Self {
        Self {
            items,
            active_item_index: 0,
            focus_handle: cx.focus_handle(),
            in_center_group: false,
            render_tab_bar: None,
        }
    }

    /// Install a custom tab-bar renderer (the cockpit's themed tab strip).
    pub fn set_render_tab_bar(
        &mut self,
        render: impl Fn(&mut Pane, &mut Window, &mut Context<Pane>) -> gpui::AnyElement + 'static,
    ) {
        self.render_tab_bar = Some(Box::new(render));
    }

    pub fn items(&self) -> &[Box<dyn CockpitSurface>] {
        &self.items
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn active_item_index(&self) -> usize {
        self.active_item_index
    }

    pub fn active_item(&self) -> Option<&dyn CockpitSurface> {
        self.items.get(self.active_item_index).map(|b| b.as_ref())
    }

    pub fn active_item_mut(&mut self) -> Option<&mut Box<dyn CockpitSurface>> {
        self.items.get_mut(self.active_item_index)
    }

    /// Append a surface and make it active. Returns its index.
    pub fn add_item(
        &mut self,
        item: Box<dyn CockpitSurface>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> usize {
        let index = self.items.len();
        self.items.push(item);
        self.activate_item(index, window, cx);
        cx.notify();
        index
    }

    /// Activate the surface at `index` (clamped). Deactivates the previous active
    /// surface and focuses the new one.
    pub fn activate_item(&mut self, index: usize, window: &mut Window, cx: &mut Context<Self>) {
        if self.items.is_empty() {
            return;
        }
        let index = index.min(self.items.len() - 1);
        let prev = mem::replace(&mut self.active_item_index, index);
        if prev != index {
            if let Some(prev_item) = self.items.get_mut(prev) {
                prev_item.deactivated(window, cx);
            }
        }
        if let Some(item) = self.items.get(index) {
            let handle = item.focus_handle(cx);
            handle.focus(window, cx);
        }
        cx.notify();
    }

    /// Activate by surface identity. Returns whether the surface was found.
    pub fn activate_item_by_id(
        &mut self,
        id: SurfaceId,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> bool {
        if let Some(ix) = self.items.iter().position(|i| i.item_id() == id) {
            self.activate_item(ix, window, cx);
            true
        } else {
            false
        }
    }

    /// Remove the surface at `index`, keeping the active index valid.
    pub fn remove_item(&mut self, index: usize, _window: &mut Window, cx: &mut Context<Self>) {
        if index >= self.items.len() {
            return;
        }
        self.items.remove(index);
        if self.active_item_index >= self.items.len() {
            self.active_item_index = self.items.len().saturating_sub(1);
        } else if index < self.active_item_index {
            self.active_item_index -= 1;
        }
        cx.notify();
    }

    /// Remove a surface by identity.
    pub fn remove_item_by_id(
        &mut self,
        id: SurfaceId,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        if let Some(ix) = self.items.iter().position(|i| i.item_id() == id) {
            self.remove_item(ix, window, cx);
        }
    }

    /// The location of the cursor in window space, used by directional pane
    /// navigation. The cockpit has no text cursor, so this is always `None`
    /// (callers fall back to the pane's bounding-box center).
    pub fn pixel_position_of_cursor(&self, _cx: &App) -> Option<gpui::Point<gpui::Pixels>> {
        None
    }

    /// The built-in tab strip: one clickable tab per surface, the active one
    /// highlighted, with a dirty dot. Used when no custom renderer is installed.
    fn default_tab_bar(
        &mut self,
        _window: &mut Window,
        cx: &mut Context<Self>,
    ) -> gpui::AnyElement {
        let active = self.active_item_index;
        let mut row = div()
            .flex()
            .flex_row()
            .items_center()
            .gap_1()
            .h(px(30.))
            .px_1()
            .bg(theme::panel())
            .border_b_1()
            .border_color(theme::border());

        for (ix, item) in self.items.iter().enumerate() {
            let is_active = ix == active;
            let label: SharedString = item.tab_label();
            let dirty = item.is_dirty(cx);
            row = row.child(
                div()
                    .id(("cockpit-tab", ix))
                    .flex()
                    .flex_row()
                    .items_center()
                    .gap_1()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .text_xs()
                    .text_color(if is_active {
                        theme::text()
                    } else {
                        theme::muted()
                    })
                    .when(is_active, |this| this.bg(theme::panel_hi()))
                    .hover(|this| this.bg(theme::panel_hi()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |pane, _, window, cx| {
                            pane.activate_item(ix, window, cx);
                        }),
                    )
                    .child(label)
                    .when(dirty, |this| {
                        this.child(
                            div()
                                .size(px(6.))
                                .rounded_full()
                                .bg(theme::accent()),
                        )
                    }),
            );
        }
        row.into_any_element()
    }
}

impl Focusable for Pane {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl Render for Pane {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        // Tab bar: custom if installed, else the built-in strip.
        let tab_bar = if let Some(render) = self.render_tab_bar.take() {
            let el = render(self, window, cx);
            self.render_tab_bar = Some(render);
            el
        } else {
            self.default_tab_bar(window, cx)
        };

        // Body: the active surface renders itself. Take it out to satisfy the
        // borrow checker (render_body takes `&mut self` on the surface), then
        // restore it.
        let body = if let Some(mut item) = (self.active_item_index < self.items.len())
            .then(|| self.items.remove(self.active_item_index))
        {
            let el = item.render_body(window, cx);
            self.items.insert(self.active_item_index, item);
            el
        } else {
            div()
                .flex_1()
                .flex()
                .items_center()
                .justify_center()
                .text_color(theme::muted())
                .child("empty pane")
                .into_any_element()
        };

        div()
            .key_context("Pane")
            .track_focus(&self.focus_handle)
            .flex()
            .flex_col()
            .size_full()
            .bg(theme::bg())
            .child(tab_bar)
            .child(div().flex_1().overflow_hidden().child(body))
    }
}
