//! The `Render for Cockpit` impl — the top-level frame: drain live, fold dynamics, witness the tab, lay out the rail + the hosted pane group.

use super::*;

impl Render for Cockpit {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        // LIVE: drain the node's receipt stream first so this frame reflects every
        // receipt that arrived (per-receipt `cx.notify()`, not a snapshot reload).
        self.drain_live_stream(cx);
        // M2 DELTA LOOP: fold this frame's dynamics into per-slice invalidation so
        // the projection memo reflects exactly the cells that changed (O(changed),
        // not O(ledger)) — the producer↔consumer JOIN (EFFICIENCY-WELD-PLAN §2.1).
        self.fold_dynamics();
        // M3 WIDEN + OPTIMISTIC NAV: witness the active tab into the workspace cell —
        // but OFF the paint path. The scattered free `self.tab = …` draft writes (the
        // §3.5 stream weight class) and the `set_tab` clicks both reconcile here, but
        // the `SetField` commit (a real executor turn) is DEFERRED + coalesced onto the
        // foreground async executor rather than run synchronously in this frame. While
        // it is pending, `active_tab()` dispatches on the optimistic draft, so the panel
        // is correct this very frame; the cell catches up a beat later. Clean ⟹ the
        // guard inside makes this a cheap bool/compare (no task, no commit).
        self.schedule_witness_tab(cx);
        // NAV HISTORY: record this frame's UI state so back/forward (← → / ⌘[ ⌘])
        // can step through wherever you've been (the nav API made navigable).
        self.record_nav();

        // L6 PANED WORKSPACE: seed the right pane's `PaneGroup` on first render
        // (ONE pane holding all tabs as surfaces — the un-split base case), then
        // sync the un-split pane's active surface to the witnessed `active_tab()`
        // so flat-tab navigation (⌘K / the nav API) keeps driving the base pane.
        self.ensure_pane_group(window, cx);
        self.sync_base_pane_active(window, cx);
        // CRASH-RELAUNCH RESTORATION: once (on the first render, after the pane group
        // exists), re-open the OS windows the durable image records as torn off — the
        // restoration half of the Local→Surface migration. A reopened image carries
        // the witnessed torn-off-tabs bitset on the `WorkspaceCell`; this re-pops those
        // windows (deferred opens). Guarded so it runs exactly once.
        if !self.torn_restored {
            self.torn_restored = true;
            self.restore_torn_windows(cx);
        }
        // THE WEB-SHELL URL BAR — seed the gpui-component text input entity on the
        // first paint (it needs a live `&mut Window` + the Enter subscription), so
        // the browser surface has its real address bar ready when navigated to.
        self.ensure_webshell_input(window, cx);
        // Build the right pane's element: the `PaneGroup` rendered with the
        // active-pane decorator (a 2px accent border on the focused pane). Built
        // before the root `div()` so the `&self.pane_group` + `&self.active_pane`
        // borrows don't tangle with the rest of the tree.
        let right_pane: gpui::AnyElement =
            match (self.pane_group.as_ref(), self.active_pane.as_ref()) {
                (Some(group), Some(active)) => {
                    let decorator = ActivePaneDecorator::new(active, theme::accent());
                    group.render(&decorator, window, cx).into_any_element()
                }
                // Defensive fallback (never on the live path once seeded): the flat
                // dispatch, so the right pane is never blank.
                _ => self.workspace(cx),
            };

        let palette_open = self.palette.is_open();
        let dock_open = self.dock_open;

        // THE COHERENT FRAME (docs/deos/COCKPIT-UX.md): one stable chrome —
        //   TOP BAR (identity + cap-badge · ledger clock · ⌘K/⌘J)
        //   ┌──────────┬─────────────────────────────────────────┐
        //   │  5-MODE  │  MODE SUB-NAV (the mode's surfaces)       │
        //   │   RAIL   │  ┌──────────┬─────────┬──────────────┐   │
        //   │          │  │ context  │ inspect │ MAIN PANE     │   │
        //   │          │  │ (cells)  │ +block  │ (the surface) │   │
        //   │          │  └──────────┴─────────┴──────────────┘   │
        //   └──────────┴─────────────────────────────────────────┘
        //   DEV DOCK (collapsible, ⌘J) — the dev strip, any mode
        //
        // The three inner columns are the persistent INSPECTION CONTEXT (the cell
        // world + the reflected object + the blocklace) wrapping the active
        // surface — kept intact; the frame adds the top bar, the rail, the mode
        // sub-nav, and the dock around them.
        let body = div()
            .flex()
            .flex_1()
            .min_h_0()
            .w_full()
            // Left context rail: the cell world + the live dynamics feed.
            .child(
                div()
                    .flex()
                    .flex_col()
                    .w(px(300.))
                    .h_full()
                    .border_r_1()
                    .border_color(theme::border())
                    .bg(theme::panel())
                    .child(
                        div()
                            .id("cockpit-scroll-cells")
                            .flex_1()
                            .overflow_y_scroll()
                            // The LIVE NODE strip (only when `--node` is connected):
                            // the remote-federation watch. Re-homed here off the old
                            // rail header (the top bar carries identity now).
                            .children(self.live_node_strip())
                            .child(self.cell_world(cx)),
                    )
                    .child(
                        div()
                            .border_t_1()
                            .border_color(theme::border())
                            .child(self.dynamics_feed()),
                    ),
            )
            // Center: the reflected object over the blocklace (the inspect context).
            .child(
                div()
                    .flex()
                    .flex_col()
                    .w(px(420.))
                    .h_full()
                    .border_r_1()
                    .border_color(theme::border())
                    .child(
                        div()
                            .id("cockpit-scroll-inspector")
                            .flex_1()
                            .overflow_y_scroll()
                            .child(self.inspector()),
                    )
                    .child(
                        div()
                            .id("cockpit-scroll-blocklace")
                            .flex_1()
                            .overflow_y_scroll()
                            .border_t_1()
                            .border_color(theme::border())
                            .bg(theme::panel())
                            .child(self.blocklace(cx)),
                    ),
            )
            // THE MAIN PANE — the active surface for the current mode, over the
            // L6 paned workspace (one pane tabbed over every surface; ⊞ splits).
            // The nav bar (back/forward/pins/macro + you-are-here) rides above it.
            .child(
                div()
                    .flex()
                    .flex_col()
                    .flex_1()
                    .h_full()
                    .child(self.nav_bar(cx))
                    .child(div().flex_1().overflow_hidden().child(right_pane)),
            );

        div()
            .id("cockpit-root")
            .track_focus(&self.focus)
            .key_context("Cockpit")
            // ⌘K + ⌘J + the palette's typing/selection all flow through one handler.
            .on_key_down(cx.listener(|this, ev: &KeyDownEvent, _w, cx| {
                this.on_key(ev, cx);
            }))
            .relative()
            .flex()
            .flex_col()
            .size_full()
            .bg(theme::bg())
            .text_color(theme::text())
            .font_family("Menlo")
            // THE TOP BAR — identity + cap-badge · ledger clock · ⌘K · ⌘J.
            .child(self.top_bar(cx))
            // THE RAIL + the main content area.
            .child(
                div()
                    .flex()
                    .flex_1()
                    .min_h_0()
                    .w_full()
                    // THE LEFT RAIL — the FIVE MODES (the coherence).
                    .child(self.mode_rail(cx))
                    // The main content: the mode sub-nav over the body.
                    .child(
                        div()
                            .flex()
                            .flex_col()
                            .flex_1()
                            .min_w_0()
                            .h_full()
                            .child(self.mode_subnav(cx))
                            .child(body),
                    ),
            )
            // THE DEV DOCK — the collapsible bottom dev strip (⌘J).
            .when(dock_open, |root| root.child(self.dev_dock(cx)))
            // THE ⌘K COMMAND PALETTE overlay (absolute, on top) when open.
            .when(palette_open, |root| root.child(self.palette_overlay(cx)))
    }
}
