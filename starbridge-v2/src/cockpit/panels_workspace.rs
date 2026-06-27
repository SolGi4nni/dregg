//! Workspace/dock plumbing (tab bar, pane group, splits) + home/shell/agent/swarm/debugger/replay/cipherclerk/objects/graph/organs panels.

use super::*;

/// The dedicated state slot the AGENT-MEMORY affordance uses as the agent's
/// legible "working counter" — a clean field (the demo agent's slot 0 already
/// carries seeded state) so the ⊕ advance / ⛂ checkpoint / ↺ resume readouts
/// start at 0 and increment by one. The checkpoint still captures EVERY plane;
/// this is only the slot the panel surfaces as the visible working value.
pub(crate) const AGENT_MEM_SLOT: usize = 5;

impl Cockpit {
    pub(crate) fn dynamics_feed(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_0p5().p_2();
        col = col.child(section_title("DYNAMICS · live").mb_1());
        // INHABIT/DEV · the live dynamics-feed card AS the surface — the deos-js feed card
        // over the live World (the header + a live entry-count bind + recent rows). Built on
        // the paint path (`ensure_mode_card`).
        //
        // NOTHING DRAWS TWICE (HIG). When the dynamics card mounts it REPLACES the native
        // text feed in these bounds — the plain-text tail below is gated so it draws ONLY
        // when the card is NOT mounted (an early return after hosting the card). So exactly
        // ONE dynamics view draws here, never the card stacked over the native feed.
        // Fail-soft: on the gpui-free / card-pane-off build (or a build error → no mount),
        // the text feed renders as the surface, so the strip is never blank.
        #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
        if let Some(mount) = self
            .mode_cards
            .get(&starbridge_v2::dock::card_surface::ModeCard::Dynamics)
        {
            mount.entity.update(cx, |_card, cx| cx.notify());
            col = col.child(
                div()
                    .min_h(px(120.))
                    .border_1()
                    .border_color(theme::accent())
                    .rounded_md()
                    .bg(theme::panel())
                    .child(mount.entity.clone()),
            );
            return col;
        }
        let _ = cx;
        let tail = w.dynamics().tail(12);
        if tail.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child("(quiet)"));
        }
        for ev in tail.iter().rev() {
            let is_reject = matches!(ev, dynamics::WorldEvent::TurnRejected { .. });
            col = col.child(
                div()
                    .text_xs()
                    .text_color(if is_reject {
                        theme::bad()
                    } else {
                        theme::muted()
                    })
                    .child(format!("· {}", ev.label())),
            );
        }
        col
    }

    // --- the workspace tab bar + the four feature panels ---------------------

    /// The flat tab strip that switched the right-pane workspace BEFORE the L6
    /// paned migration. Retained as the canonical styling reference: each pane's
    /// own tab strip ([`Self::install_pane_tab_bar`]) reproduces this look, themed
    /// per-pane and driving the pane's surfaces. Kept so the flat strip is one
    /// edit away should the un-split single-pane base want it back.
    #[allow(dead_code)]
    pub(crate) fn tab_bar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let mut row = div()
            .flex()
            .flex_wrap()
            .gap_1()
            .p_2()
            .border_b_1()
            .border_color(theme::border());
        // M3 WIDEN — the active-tab highlight reads the witnessed cell selector too.
        let active_tab = self.active_tab();
        for t in Tab::ALL {
            let active = active_tab == t;
            row = row.child(
                div()
                    .id(SharedString::from(format!("tab-{}", t.label())))
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .bg(if active {
                        theme::panel_hi()
                    } else {
                        theme::panel()
                    })
                    .text_xs()
                    .text_color(if active {
                        theme::accent()
                    } else {
                        theme::muted()
                    })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            // M3 WIDEN — a tab click witnesses through `set_tab` (the
                            // single selector seam: lazy-boots SWARM + commits the cell).
                            this.set_tab(t, cx);
                        }),
                    )
                    .child(t.label()),
            );
        }
        row
    }

    /// The active right-pane workspace panel.
    pub(crate) fn workspace(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        // M3 WIDEN — the dispatch SELECTOR is the witnessed [`WorkspaceCell`] read
        // (`render(workspace_subgraph)`, §3.4), not the Rust field.
        self.panel_for_tab(self.active_tab(), cx)
    }

    /// Render the body for an EXPLICIT tab — the single per-tab dispatch, factored
    /// out of [`Self::workspace`] so the dock's [`TabSurface`] can render any tab's
    /// body (not just the witnessed-active one) when a pane shows a surface other
    /// than the cockpit's `active_tab()`. The 28-arm match is unchanged; its source
    /// moved from `active_tab()` to the passed `tab`.
    pub(crate) fn panel_for_tab(&self, tab: Tab, cx: &mut Context<Self>) -> gpui::AnyElement {
        // A surface lives in EXACTLY ONE place along the firmament distance axis:
        // composited in the dock, OR torn off into its own window. When `tab` is
        // torn off, the IN-DOCK render path (this one) must NOT also paint the
        // live body — several surfaces (web-shell URL bar, editor/composer/agent
        // prompts) embed a shared live focus-tracked kit `Entity`, and painting
        // that SAME entity in both the dock window and the torn window the same
        // frame is a re-entrant `Entity::update` / double `track_focus` that
        // (post the per-window `Root` crash-fix) spins the flush loop into a HANG
        // (the web-shell pop-out beachball). So the dock shows a placeholder; the
        // torn window paints the real body via `panel_for_tab_forced`.
        if self.tab_is_torn_off(tab) {
            return self.torn_off_placeholder(tab);
        }
        self.panel_for_tab_forced(tab, cx)
    }

    /// The IN-DOCK placeholder for a tab that is currently torn off into its own
    /// window — a calm "this surface is in its own window" card with a pop-back
    /// affordance, shown WHERE the live body would be so the dock never paints a
    /// surface that also lives in a torn window (the one-window invariant — the
    /// web-shell pop-out beachball fix). The live body is in the torn window.
    fn torn_off_placeholder(&self, tab: Tab) -> gpui::AnyElement {
        let label = tab.label();
        div()
            .flex()
            .flex_col()
            .items_center()
            .justify_center()
            .gap_2()
            .size_full()
            .p_3()
            .child(
                div()
                    .text_color(theme::muted())
                    .child(SharedString::from(format!("↗ {label} is torn off"))),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(SharedString::from(
                        "This surface is live in its own window. Pop it back (↩ in that \
                         window, or the pane's ↩ control) to dock it here again.",
                    )),
            )
            .into_any_element()
    }

    /// Render `tab`'s LIVE body unconditionally — used by the torn-off window's
    /// mirror callback, which is the surface's ONE rendering site while torn (the
    /// dock shows [`Self::torn_off_placeholder`] instead). Going through this
    /// instead of [`Self::panel_for_tab`] is what keeps a torn surface painted in
    /// exactly one window.
    pub(crate) fn panel_for_tab_forced(
        &self,
        tab: Tab,
        cx: &mut Context<Self>,
    ) -> gpui::AnyElement {
        match tab {
            Tab::Home => self.home_panel().into_any_element(),
            Tab::Shell => self.shell_panel(cx).into_any_element(),
            // OPERATE · the agent-activity card AS the surface (the mode's main pane is a
            // deos-js card over the live World), Rust agent panel as fail-soft fallback.
            #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
            Tab::Agent => self.mode_card_surface(
                starbridge_v2::dock::card_surface::ModeCard::Agent,
                cx,
                |this, cx| this.agent_panel(cx).into_any_element(),
            ),
            #[cfg(not(all(feature = "dev-surfaces", feature = "card-pane")))]
            Tab::Agent => self.agent_panel(cx).into_any_element(),
            Tab::Swarm => self.swarm_panel(cx).into_any_element(),
            // INHABIT · the ocap-graph card AS the surface (the live cap web as a card).
            #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
            Tab::Graph => self.mode_card_surface(
                starbridge_v2::dock::card_surface::ModeCard::Graph,
                cx,
                |this, _cx| this.graph_panel().into_any_element(),
            ),
            #[cfg(not(all(feature = "dev-surfaces", feature = "card-pane")))]
            Tab::Graph => self.graph_panel().into_any_element(),
            Tab::Organs => self.organs_panel().into_any_element(),
            Tab::Proofs => self.proofs_panel().into_any_element(),
            Tab::WebOfCells => self.web_of_cells_panel(cx).into_any_element(),
            Tab::WebShell => self.webshell_panel(cx).into_any_element(),
            // AUTHOR · the what-links-here card AS the surface (live backlinks as a card).
            #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
            Tab::LinksHere => self.mode_card_surface(
                starbridge_v2::dock::card_surface::ModeCard::Links,
                cx,
                |this, cx| this.links_here_panel(cx).into_any_element(),
            ),
            #[cfg(not(all(feature = "dev-surfaces", feature = "card-pane")))]
            Tab::LinksHere => self.links_here_panel(cx).into_any_element(),
            Tab::Powerbox => self.powerbox_panel(cx).into_any_element(),
            Tab::Moldable => self.moldable_panel(cx).into_any_element(),
            Tab::InspectAct => self.inspect_act_panel(cx).into_any_element(),
            Tab::ServiceExplorer => self.service_explorer_panel(cx).into_any_element(),
            Tab::Workspace => self.workspace_panel(cx).into_any_element(),
            Tab::Wonder => self.wonder_panel(cx).into_any_element(),
            Tab::Lanes => self.lanes_panel(cx).into_any_element(),
            Tab::Time => self.time_panel(cx).into_any_element(),
            Tab::Share => self.share_panel(cx).into_any_element(),
            Tab::Docs => self.docs_panel(cx).into_any_element(),
            Tab::Trust => self.trust_tab(cx).into_any_element(),
            Tab::Devtools => self.devtools_panel(cx).into_any_element(),
            Tab::Buffer => self.buffer_panel(cx).into_any_element(),
            Tab::Terminal => self.terminal_panel(cx).into_any_element(),
            // AUTHOR · the composition-composer card AS the surface.
            #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
            Tab::Composer => self.mode_card_surface(
                starbridge_v2::dock::card_surface::ModeCard::Composer,
                cx,
                |this, cx| this.composer(cx).into_any_element(),
            ),
            #[cfg(not(all(feature = "dev-surfaces", feature = "card-pane")))]
            Tab::Composer => self.composer(cx).into_any_element(),
            Tab::Simulate => self.simulate_panel(cx).into_any_element(),
            // INHABIT · the object-roster card AS the surface (the live cell roster).
            #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
            Tab::Objects => self.mode_card_surface(
                starbridge_v2::dock::card_surface::ModeCard::Objects,
                cx,
                |this, _cx| this.objects_panel().into_any_element(),
            ),
            #[cfg(not(all(feature = "dev-surfaces", feature = "card-pane")))]
            Tab::Objects => self.objects_panel().into_any_element(),
            Tab::Debugger => self.debugger_panel().into_any_element(),
            Tab::Replay => self.replay_panel().into_any_element(),
            Tab::Cipherclerk => self.cipherclerk_panel(cx).into_any_element(),
            Tab::Editor => self.editor_panel().into_any_element(),
        }
    }

    // === THE L6 PANED WORKSPACE ===========================================
    // The right pane's flat 28-tab list, hosted as a resizable/splittable
    // `PaneGroup`. The base case is ONE pane holding every tab as a `TabSurface`
    // (so it looks like the old tabbed pane); a split puts two surfaces
    // side-by-side behind the draggable divider.

    /// Seed [`Self::pane_group`] on first render: ONE [`Pane`] holding every
    /// [`Tab`] as a [`TabSurface`], its active surface synced to the cockpit's
    /// `active_tab()`. Idempotent — a no-op once seeded.
    pub(crate) fn ensure_pane_group(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        if self.pane_group.is_some() {
            return;
        }
        let weak = cx.entity().downgrade();
        let active = self.active_tab();
        let pane = self.build_seed_pane(weak.clone(), active, window, cx);
        self.active_pane = Some(pane.clone());
        self.pane_group = Some(PaneGroup::new(pane));
    }

    /// Keep the UN-SPLIT base pane's active surface in step with the witnessed
    /// [`active_tab`](Self::active_tab), so the flat navigation seams (⌘K, the
    /// nav-history back/forward, `select_tab_named`) still drive the right pane.
    /// A NO-OP once the group is split (more than one pane): split panes are
    /// steered independently by their own tab strips, so a flat-tab change must
    /// not stomp them. Costs a cheap `panes().len()` + one read per frame.
    pub(crate) fn sync_base_pane_active(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        let single = self
            .pane_group
            .as_ref()
            .map(|g| g.panes().len() == 1)
            .unwrap_or(false);
        if !single {
            return;
        }
        let want = DockSurfaceId(self.active_tab().index() as u64);
        if let Some(pane) = self.active_pane.clone() {
            pane.update(cx, |pane, cx| {
                if pane.active_item().map(|s| s.item_id()) != Some(want) {
                    pane.activate_item_by_id(want, window, cx);
                }
            });
        }
    }

    /// Build a fresh pane populated with all 28 tabs as surfaces, themed tab bar
    /// installed, with `active` activated. `which` lets a split seed a pane that
    /// opens on a *different* tab than the source (so the two panes show two
    /// different surfaces).
    pub(crate) fn build_seed_pane(
        &self,
        weak: WeakEntity<Cockpit>,
        active: Tab,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Entity<Pane> {
        cx.new(|cx| {
            let items: Vec<Box<dyn CockpitSurface>> = Tab::ALL
                .iter()
                .map(|t| {
                    Box::new(TabSurface::new(*t, weak.clone(), cx.focus_handle()))
                        as Box<dyn CockpitSurface>
                })
                .collect();
            let mut pane = Pane::with_items(items, window, cx);
            pane.activate_item_by_id(DockSurfaceId(active.index() as u64), window, cx);
            Self::install_pane_tab_bar(&mut pane, weak.clone());
            pane
        })
    }

    /// Install the cockpit-themed tab strip on `pane` (the swappable
    /// `render_tab_bar`): one clickable tab per surface + a ⊞ split button, all
    /// styled like the cockpit's flat tab bar. A tab click activates that surface
    /// in the pane AND syncs the cockpit's witnessed active tab; ⊞ splits this
    /// pane to the right.
    pub(crate) fn install_pane_tab_bar(pane: &mut Pane, weak: WeakEntity<Cockpit>) {
        pane.set_render_tab_bar(move |pane: &mut Pane, _window, cx| {
            let active = pane.active_item_index();
            let mut row = div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .p_2()
                .border_b_1()
                .border_color(theme::border());

            // The ⊞ SPLIT control — grafts a fresh pane (opening on the next
            // surface) beside this one (the draggable divider appears between them).
            {
                let weak = weak.clone();
                // WEAK self-handle (not a strong `cx.entity()`) so the closure the
                // pane stores does not retain the pane in a reference cycle.
                let this_pane = cx.entity().downgrade();
                row = row.child(
                    div()
                        .id("pane-split")
                        .px_2()
                        .py_1()
                        .rounded_md()
                        .bg(theme::panel())
                        .text_xs()
                        .text_color(theme::accent())
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::border()))
                        .on_mouse_down(MouseButton::Left, move |_ev, window, app| {
                            if let Some(src) = this_pane.upgrade() {
                                let _ = weak.update(app, |cockpit, cx| {
                                    cockpit.split_pane(&src, SplitDirection::Right, window, cx);
                                });
                            }
                        })
                        .child("⊞ split"),
                );
            }

            // The ↗ POP OUT control — SURFACE MIGRATION (Local→Surface): tear the
            // pane's ACTIVE surface off into its own OS window, identity preserved.
            // It TOGGLES: while the surface is torn off it reads "↩ pop in" and
            // closes the window (the inverse migration). Drives the cockpit's
            // `tear_off_tab` / `pop_back_tab` (deferred, so the window op runs with
            // the app at rest). The torn-off window renders the same body over the
            // same cell. A no-op in the headless bake (no second window opens there).
            {
                let weak = weak.clone();
                // The active surface's tab + whether it is currently torn off (read
                // through the host so the control's label reflects live state).
                let pane_tab = pane
                    .active_item()
                    .map(|s| Tab::from_index(s.item_id().as_u64() as usize));
                let is_torn = pane_tab
                    .and_then(|_t| weak.upgrade())
                    .map(|c| c.read(cx).tab_is_torn_off(pane_tab.unwrap()))
                    .unwrap_or(false);
                row = row.child(
                    div()
                        .id("pane-popout")
                        .px_2()
                        .py_1()
                        .rounded_md()
                        .bg(theme::panel())
                        .text_xs()
                        .text_color(theme::accent())
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::border()))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |pane: &mut Pane, _ev, _window, cx| {
                                // GUARDED at the event boundary: gpui dispatches this
                                // mouse-down from an Obj-C `nounwind` callback, so a
                                // panic here would `process::abort` the whole cockpit
                                // (ember's pop-out crash). `guard_ui_event` contains
                                // any panic as a logged no-op. See `Cockpit::guard_ui_event`.
                                Cockpit::guard_ui_event("pane-popout", || {
                                    // Toggle the surface THIS pane is showing between
                                    // its own window and the dock (a split pane may show
                                    // a different tab than the cockpit's active one).
                                    let tab = pane
                                        .active_item()
                                        .map(|s| Tab::from_index(s.item_id().as_u64() as usize));
                                    if let Some(tab) = tab {
                                        let _ = weak.update(cx, |cockpit, cx| {
                                            if cockpit.tab_is_torn_off(tab) {
                                                cockpit.pop_back_tab(tab, cx);
                                            } else {
                                                cockpit.tear_off_tab_deferred(tab, cx);
                                            }
                                        });
                                    }
                                });
                            }),
                        )
                        .child(if is_torn { "↩ pop in" } else { "↗ pop out" }),
                );
            }

            for (ix, item) in pane.items().iter().enumerate() {
                let is_active = ix == active;
                let label = item.tab_label();
                let weak = weak.clone();
                row = row.child(
                    div()
                        .id(("pane-tab", ix))
                        .px_2()
                        .py_1()
                        .rounded_md()
                        .bg(if is_active {
                            theme::panel_hi()
                        } else {
                            theme::panel()
                        })
                        .text_xs()
                        .text_color(if is_active {
                            theme::accent()
                        } else {
                            theme::muted()
                        })
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::border()))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |pane: &mut Pane, _ev, window, cx| {
                                pane.activate_item(ix, window, cx);
                                // Sync the cockpit's witnessed active tab to the
                                // surface this pane now shows (the single selector
                                // seam — lazy-boots SWARM + commits the cell).
                                if let Some(tab) = pane
                                    .active_item()
                                    .map(|s| Tab::from_index(s.item_id().as_u64() as usize))
                                {
                                    let _ = weak.update(cx, |cockpit, cx| {
                                        cockpit.set_tab(tab, cx);
                                    });
                                }
                            }),
                        )
                        .child(label),
                );
            }
            row.into_any_element()
        });
    }

    /// Split `src` in `direction`: mint a fresh pane (opening on the next tab so
    /// the two panes show different surfaces) and graft it beside `src` in the
    /// [`PaneGroup`], with the new pane active. The draggable [`PaneAxisElement`]
    /// divider then sits between them, resizable.
    pub(crate) fn split_pane(
        &mut self,
        src: &Entity<Pane>,
        direction: SplitDirection,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        // The new pane opens on a DIFFERENT surface than the source's active one
        // (the next tab), so a split visibly yields two distinct surfaces.
        let src_active = src
            .read(cx)
            .active_item()
            .map(|s| Tab::from_index(s.item_id().as_u64() as usize))
            .unwrap_or(Tab::Home);
        let next = Tab::from_index((src_active.index() + 1) % Tab::ALL.len());
        let weak = cx.entity().downgrade();

        let new_pane = self.build_seed_pane(weak, next, window, cx);
        if let Some(group) = self.pane_group.as_mut() {
            group.split(src, &new_pane, direction);
        }
        self.active_pane = Some(new_pane);
        cx.notify();
    }

    // === THE SELF-HOSTING DEV PANES (edit/build deos INSIDE deos) =========
    // The deos EDITOR + TERMINAL, mounted on-demand as their own split panes.
    // A dev surface is spawned FRESH on invocation (a live window) — never in
    // `build_seed_pane` (which also runs in the headless bake), so the bake
    // never spawns a PTY or touches disk. Each opens in its OWN single-surface
    // pane grafted beside the active pane, with a self-contained tab bar (it
    // does NOT sync the cockpit's witnessed `active_tab`, since these surfaces
    // are not [`Tab`]s — their ids live in a high range, away from the 0..27
    // tab ids).

    /// The id base for the on-demand dev surfaces (editor/terminal), kept far
    /// above the `0..27` [`Tab`] ids so a dev surface never collides with a
    /// `TabSurface`. [`Self::next_dev_surface_id`] offsets it by the live pane
    /// count so two terminals/editors open side by side with distinct ids.
    const DEV_SURFACE_ID_BASE: u64 = 1000;

    /// Defer an open (`open_terminal_pane` / `open_editor_pane`) so it runs with
    /// a live `&mut Window` AFTER the current Context update unwinds. `dispatch`
    /// is driven from the key/palette handler with only a `Context` in hand;
    /// re-entering the cockpit's own window synchronously here would find its
    /// window box already taken (we are inside its update). Deferring lets the
    /// window return to its slot first, then [`App::with_window`] re-enters it
    /// (the cockpit↔window mapping is already registered by render) and hands the
    /// open method the `(&mut Window, &mut Context)` it needs.
    #[cfg(feature = "dev-surfaces")]
    pub(crate) fn open_dev_pane_deferred(
        &mut self,
        cx: &mut Context<Self>,
        open: fn(&mut Cockpit, &mut Window, &mut Context<Cockpit>),
    ) {
        let weak = cx.entity().downgrade();
        let entity_id = cx.entity_id();
        cx.defer(move |app: &mut App| {
            app.with_window(entity_id, |window, app| {
                let _ = weak.update(app, |this, cx| open(this, window, cx));
            });
        });
    }

    /// Open a LIVE TERMINAL pane: spawn `$SHELL` on a real PTY and graft it as a
    /// split beside the active pane. The terminal half of the self-hosting dev
    /// loop — run cargo/git INSIDE deos. Spawn happens only here (a live window),
    /// never in the headless bake. A spawn failure logs and is a no-op.
    #[cfg(feature = "dev-surfaces")]
    pub(crate) fn open_terminal_pane(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        use starbridge_v2::dock::terminal_surface::TerminalPane;

        let id = self.next_dev_surface_id();
        let surface: Box<dyn CockpitSurface> = match TerminalPane::spawn_shell(id, cx) {
            Ok(pane) => Box::new(pane),
            Err(e) => {
                // Fail-soft: a missing $SHELL / PTY error must not take down the
                // cockpit — log and leave the workspace untouched.
                eprintln!("open_terminal_pane: could not spawn shell: {e:#}");
                self.last_outcome = Some(format!("could not open terminal: {e}"));
                cx.notify();
                return;
            }
        };
        self.graft_dev_pane(surface, window, cx);
    }

    /// Open a LIVE EDITOR pane: a deos-zed editor rooted at the repo cwd, grafted
    /// as a split beside the active pane. The editor half of the self-hosting dev
    /// loop — edit deos's own sources INSIDE deos. Built only here (a live
    /// window), never in the headless bake.
    #[cfg(feature = "dev-surfaces")]
    pub(crate) fn open_editor_pane(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        use starbridge_v2::dock::editor_surface::EditorPane;

        let id = self.next_dev_surface_id();
        let root = std::env::current_dir().unwrap_or_else(|_| std::path::PathBuf::from("."));

        // The seed project the editor opens onto — file-cells installed on the
        // LIVE cockpit `World`, so a save lands on the ledger this cockpit's own
        // cell inspector reads (one ledger, one save path). First entry is opened
        // in the buffer; saving it fires a real cap-gated turn.
        #[cfg(feature = "embedded-executor")]
        const EDITOR_SEED: &[(&str, &str)] = &[
            (
                "/deos/main.rs",
                "// edit me — every save here is a RECEIPTED dregg turn on the LIVE cockpit ledger.\n\
                 // a save shows up in the cockpit's own cell inspector as a new cell + receipt.\n\
                 fn main() {\n    println!(\"hello from a sovereign cell\");\n}\n",
            ),
            (
                "/deos/notes.md",
                "# on-ledger notes\n\nThis file is a cell on the live World. Saving it is a\n\
                 cap-gated turn the cockpit inspector can see — not a disk write.\n",
            ),
        ];

        // Mount the editor OVER the live cockpit `World` (the shared-ledger seam):
        // the editor edits the SAME ledger the inspector reads. Fail-soft to the
        // per-editor firmament default if the shared mount errors, so a mount
        // failure can never take down the cockpit — but say so loudly.
        #[cfg(feature = "embedded-executor")]
        let surface: Box<dyn CockpitSurface> = {
            match EditorPane::firmament_over(
                id,
                self.world.clone(),
                root.clone(),
                EDITOR_SEED,
                window,
                cx,
            ) {
                Ok(pane) => Box::new(pane),
                Err(e) => {
                    eprintln!(
                        "open_editor_pane: shared-World mount failed, falling back to \
                         per-editor firmament: {e:#}"
                    );
                    Box::new(EditorPane::new(
                        id,
                        deos_zed::fs::RealFs::arc(),
                        root,
                        window,
                        cx,
                    ))
                }
            }
        };
        #[cfg(not(feature = "embedded-executor"))]
        let surface: Box<dyn CockpitSurface> = {
            let fs = deos_zed::fs::RealFs::arc();
            Box::new(EditorPane::new(id, fs, root, window, cx))
        };

        self.graft_dev_pane(surface, window, cx);
    }

    /// Open a LIVE CARD pane: a hyperdreggmedia CARD ([`CardSurface`]) grafted as a
    /// split beside the active pane — THE keystone joy-path surface. The card binds
    /// + fires against the cockpit's LIVE `World` (the operator's `user` anchor
    ///   cell): its `bind` re-reads that cell's counter off the live ledger and its
    ///   `+1` button fires ONE cap-gated verified turn through `World::commit_turn` —
    ///   a receipt the cockpit's own cell inspector immediately sees (the SAME ledger
    ///   the editor pane saves onto). A child clicks the +1 and the count rises; the
    ///   turn bottoms out in the verified executor. Built only here (a live window) —
    ///   the headless bake (`render_card_pane_headless`) is the separate PNG path.
    ///
    /// Boots a SpiderMonkey runtime to AUTHOR the view-tree (the engine is a
    /// process-global singleton, so a second open after one already booted fails;
    /// it is fail-soft — logged, the workspace untouched). The `card-pane` feature
    /// pulls deos-js + deos-view; this method is compiled only when it is on (with
    /// `dev-surfaces`'s graft machinery).
    #[cfg(all(
        feature = "dev-surfaces",
        feature = "card-pane",
        feature = "embedded-executor"
    ))]
    pub(crate) fn open_card_pane(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        use starbridge_v2::dock::card_surface::build_card_surface;

        let id = self.next_dev_surface_id();
        // The card's substance: the operator's own `user` anchor cell (anchors =
        // [treasury, service, user]) — the SAME cell the `--render-card-pane` bake
        // binds, so the dock card and the proven PNG card drive one cell.
        let agent = self.anchors[2];

        // Boot SpiderMonkey to author the card's `deos.ui.*` tree. The engine is a
        // process-global singleton; a boot failure (e.g. a second open) is
        // fail-soft so it can never take down the cockpit — but say so loudly.
        let mut rt = match deos_js::JsRuntime::new() {
            Ok(rt) => rt,
            Err(e) => {
                eprintln!("open_card_pane: could not boot SpiderMonkey: {e}");
                self.last_outcome = Some(format!(
                    "could not open card (SpiderMonkey boots once per process): {e}"
                ));
                cx.notify();
                return;
            }
        };

        let surface: Box<dyn CockpitSurface> =
            match build_card_surface(id, &mut rt, self.world.clone(), agent, cx) {
                Ok(card) => Box::new(card),
                Err(e) => {
                    eprintln!(
                        "open_card_pane: could not author the card over the live World: {e:#}"
                    );
                    self.last_outcome = Some(format!("could not open card: {e}"));
                    cx.notify();
                    return;
                }
            };
        self.graft_dev_pane(surface, window, cx);
    }

    /// Open a LIVE AGENT pane: the CONFINED HERMES agent dock, grafted as a split
    /// beside the active pane. The ADOS dev-loop made visible — a chat pane, the
    /// tool-call ledger (every tool-call a cap-gated RECEIPTED turn, or an in-band
    /// refusal), and the live mandate inspector. Seeded with a self-contained demo
    /// model (a real `HermesGateway` admitting an allowed + a refused tool-call) so
    /// the ledger + inspector render without a live ACP session attached. Built
    /// only here (a live window), never in the headless bake.
    #[cfg(feature = "dev-surfaces")]
    pub(crate) fn open_agent_pane(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        use starbridge_v2::dock::hermes_surface::AgentPane;

        let id = self.next_dev_surface_id();
        let surface: Box<dyn CockpitSurface> =
            Box::new(AgentPane::interactive(id, "deos-agent", window, cx));
        self.graft_dev_pane(surface, window, cx);
    }

    /// Open the deos MEMBRANE pane: the deos-matrix chat surface ([`ChatPane`])
    /// grafted as a split beside the active pane — the social/multiplayer layer
    /// where **a message IS a cap-bounded world-fork**.
    ///
    /// The transport is the dregg world itself (`WorldChatSource`): rooms are real
    /// cells, a send is a real verified turn, the timeline is read back from real
    /// cell state — never a mock. The pane is wrapped in [`CommsPdSource`], an
    /// executor-backed `ChatSource` holding a real fork of the chat world, so the
    /// `⬡ attach membrane` affordance is GENUINE: it mints a real `MembraneFrustum`
    /// (a "screenshot of the moment" — an anti-amplification frustum culled in view
    /// of the local user's cell), and a received membrane rehydrates → drives →
    /// stitches a real `Cell` fork through the branch-and-stitch settlement gate
    /// (the math is proven in `SettlementSoundness.lean`). Because the source holds
    /// an executor, `membrane_capable()` is true and the membrane fire button is
    /// LIVE (not the disabled "open in deos to rehydrate" of a bare transport).
    ///
    /// This is the WINDOWED mount of the pane that previously rendered only in the
    /// headless `--render-guest`/`--render-showcase` PNG bakes — the same
    /// construction (`guest.rs`/`showcase.rs`), grafted into a clickable dock split.
    /// Built only here (a live window). Needs `dev-surfaces` (the deos-matrix
    /// `ChatSource` + the graft machinery) and `embedded-executor` (the `World` the
    /// comms-PD source forks).
    #[cfg(all(feature = "dev-surfaces", feature = "embedded-executor"))]
    pub(crate) fn open_membrane_pane(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        use starbridge_v2::dock::chat_surface::ChatPane;
        use std::sync::Arc;

        let id = self.next_dev_surface_id();

        // CHAT — fully REAL, no mock anywhere (the guest/showcase bake construction).
        // The TRANSPORT is the dregg world itself (`WorldChatSource`): rooms are real
        // cells, a sent message is a real verified turn. The MEMBRANE affordances are
        // REAL too: the comms-PD source wraps the world-chat and snapshots a fork of
        // the SAME chat world (the "screenshot a moment"), rehydrating/driving/
        // stitching genuine `Cell` frusta. Every membrane button drives the real
        // executor — never a mock envelope.
        let world_chat = crate::world_chat::WorldChatSource::seeded("@ember:deos.local");
        let membrane_world = world_chat.fork_world();
        let focus = world_chat.me_cell();
        let transport: Arc<dyn deos_matrix::source::ChatSource> = Arc::new(world_chat);
        let source: Arc<dyn deos_matrix::source::ChatSource> = Arc::new(
            crate::comms_pd_source::CommsPdSource::new(transport, membrane_world, focus, 3),
        );

        let surface: Box<dyn CockpitSurface> = Box::new(ChatPane::new(id, source, window, cx));
        self.graft_dev_pane(surface, window, cx);
    }

    /// Mint a dev-surface id in the high range (away from the `0..27` tab ids).
    /// Derived from the live pane count so repeated opens get distinct ids
    /// without a persistent counter field; a dev surface lives alone in its own
    /// pane, so uniqueness only needs to hold across simultaneously-open dev
    /// panes, which a growing pane count provides.
    #[cfg(feature = "dev-surfaces")]
    pub(crate) fn next_dev_surface_id(&self) -> u64 {
        let panes = self
            .pane_group
            .as_ref()
            .map(|g| g.panes().len() as u64)
            .unwrap_or(0);
        Self::DEV_SURFACE_ID_BASE + panes
    }

    /// Build a single-surface pane holding `surface`, install the dev-pane tab
    /// bar, and graft it as a right split beside the active pane (mirroring
    /// [`Self::split_pane`]'s `PaneGroup::split` + active-pane + notify). Seeds
    /// the pane group first if the window has not rendered yet.
    #[cfg(feature = "dev-surfaces")]
    fn graft_dev_pane(
        &mut self,
        surface: Box<dyn CockpitSurface>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        // The dev pane grafts beside an existing pane, so make sure the base
        // group exists (normally seeded on first render; this covers an open
        // dispatched before the first paint).
        self.ensure_pane_group(window, cx);

        let weak = cx.entity().downgrade();
        let new_pane = cx.new(|cx| {
            let mut pane = Pane::with_items(vec![surface], window, cx);
            Self::install_dev_pane_tab_bar(&mut pane, weak.clone());
            pane
        });

        // Graft beside the current active pane (or the group root if none).
        let anchor = self
            .active_pane
            .clone()
            .or_else(|| self.pane_group.as_ref().map(|g| g.first_pane()));
        if let (Some(group), Some(anchor)) = (self.pane_group.as_mut(), anchor) {
            group.split(&anchor, &new_pane, SplitDirection::Right);
        } else if self.pane_group.is_none() {
            // No group at all (shouldn't happen after ensure) — make this pane
            // the root so the surface is still reachable.
            self.pane_group = Some(PaneGroup::new(new_pane.clone()));
        }
        self.active_pane = Some(new_pane);
        cx.notify();
    }

    /// The dev pane's tab strip: the surface's own live label + a ⊞ split
    /// control. Unlike [`Self::install_pane_tab_bar`], it does NOT sync the
    /// cockpit's witnessed `active_tab` (a dev surface is not a [`Tab`]); its ⊞
    /// splits this pane (seeding the new pane on the next tab, like elsewhere).
    #[cfg(feature = "dev-surfaces")]
    fn install_dev_pane_tab_bar(pane: &mut Pane, weak: WeakEntity<Cockpit>) {
        pane.set_render_tab_bar(move |pane: &mut Pane, window, cx| {
            let active = pane.active_item_index();
            let mut row = div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .p_2()
                .border_b_1()
                .border_color(theme::border());

            // The ⊞ SPLIT control — graft a fresh tab pane beside this one.
            {
                let weak = weak.clone();
                let this_pane = cx.entity().downgrade();
                row = row.child(
                    div()
                        .id("dev-pane-split")
                        .px_2()
                        .py_1()
                        .rounded_md()
                        .bg(theme::panel())
                        .text_xs()
                        .text_color(theme::accent())
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::border()))
                        .on_mouse_down(MouseButton::Left, move |_ev, window, app| {
                            if let Some(src) = this_pane.upgrade() {
                                let _ = weak.update(app, |cockpit, cx| {
                                    cockpit.split_pane(&src, SplitDirection::Right, window, cx);
                                });
                            }
                        })
                        .child("⊞ split"),
                );
            }

            // One clickable tab per surface (the dev pane holds one, but a later
            // graft could add more) — activating just switches the body; it never
            // stomps the cockpit's witnessed tab.
            for (ix, item) in pane.items().iter().enumerate() {
                let is_active = ix == active;
                let label = item.tab_content(window, cx);
                row = row.child(
                    div()
                        .id(("dev-pane-tab", ix))
                        .px_2()
                        .py_1()
                        .rounded_md()
                        .bg(if is_active {
                            theme::panel_hi()
                        } else {
                            theme::panel()
                        })
                        .text_xs()
                        .text_color(if is_active {
                            theme::accent()
                        } else {
                            theme::muted()
                        })
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::border()))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |pane: &mut Pane, _ev, window, cx| {
                                pane.activate_item(ix, window, cx);
                            }),
                        )
                        .child(label),
                );
            }
            row.into_any_element()
        });
    }

    // === SURFACE MIGRATION — the Local→Surface tear-off ====================
    // A dock pane pops OUT into its own OS window, the surface IDENTITY preserved
    // (`docs/deos/SURFACE-MIGRATION.md`, the first concrete migration). The torn-
    // off window re-renders the SAME tab body over the SAME cell through the SAME
    // `panel_for_tab` re-entry the in-dock `TabSurface` uses — so it is a live
    // MIRROR of the surface in a second window, not a copy of its state. The dock
    // pane is never removed (non-destructive); pop-back just closes the window.

    /// THE UI-EVENT PANIC GUARD (the load-bearing safety net).
    ///
    /// gpui dispatches mouse/key events from an Objective-C callback that is a
    /// `nounwind` FFI boundary: if a Rust panic reaches it, the runtime calls
    /// `panic_cannot_unwind` → `std::process::abort` and the WHOLE app dies (this is
    /// exactly the crash ember hit clicking "↗ pop out" — see the module-tail repro).
    /// So no cockpit event closure may be allowed to unwind to gpui.
    ///
    /// This wraps an action in [`std::panic::catch_unwind`] so a panic is CONTAINED:
    /// it is logged + turned into a no-op (the action simply does not happen), and
    /// the cockpit keeps running. Returns `true` if the action ran to completion,
    /// `false` if it panicked (and was contained). Use it at the seam of any cockpit
    /// `on_click`/`on_mouse_down` closure that could panic — never let one cross the
    /// nounwind boundary.
    ///
    /// `label` names the action in the logged error so a contained panic is
    /// diagnosable (it is NOT silent — fail-soft, but loud in the log).
    pub(crate) fn guard_ui_event<R>(label: &str, action: impl FnOnce() -> R) -> bool {
        // `AssertUnwindSafe`: the cockpit's `&mut self` is not `UnwindSafe`, but a
        // contained panic here only ABORTS the in-flight UI action — it does not
        // resume reading torn cockpit state (gpui drops the frame; the next frame
        // rebuilds from the live `World`). The alternative (the unguarded panic
        // crossing into Obj-C) aborts the process, which is strictly worse.
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(action)) {
            Ok(_) => true,
            Err(_) => {
                eprintln!(
                    "cockpit: UI event '{label}' PANICKED — contained (no-op) instead of \
                     aborting the process (the gpui Obj-C event boundary is nounwind)."
                );
                false
            }
        }
    }

    /// TEAR OFF the cockpit's CURRENTLY-ACTIVE tab into its own OS window — the
    /// Local→Surface migration on the active surface. Driven by the ⌘K command /
    /// the pane "↗ pop out" control. Deferred so it runs with a live `&mut Window`
    /// AFTER the current update unwinds (the same reason the dev-pane opens defer:
    /// `dispatch` holds only a `Context`, and opening a window re-enters the app).
    pub(crate) fn tear_off_active_tab(&mut self, cx: &mut Context<Self>) {
        let tab = self.active_tab();
        self.tear_off_tab_deferred(tab, cx);
    }

    /// Defer the tear-off of `tab` so it opens with the app at rest (a window open
    /// must not run inside the cockpit's own in-flight update). Re-enters the
    /// cockpit on the deferred app pass and calls [`Self::tear_off_tab`].
    pub(crate) fn tear_off_tab_deferred(&mut self, tab: Tab, cx: &mut Context<Self>) {
        let weak = cx.entity().downgrade();
        // Run the actual window-open at the APP level — NOT inside a cockpit lease.
        // THE CRASH FIX: `App::open_window` SYNCHRONOUSLY DRAWS the new window's first
        // frame, and the torn-off window's render re-enters THIS cockpit through its
        // mirror callback (`weak.update(app, |cockpit, …| panel_for_tab)`). If the
        // open ran while the cockpit was leased (as it did when this deferred body was
        // `weak.update(app, |this, cx| this.tear_off_tab(…))`), that synchronous draw
        // re-enters an ALREADY-LEASED cockpit → `cannot update Cockpit while it is
        // already being updated` → in the release build that panic crosses gpui's
        // Obj-C `handle_view_event` nounwind boundary → `process::abort` (ember's
        // crash). Opening with the cockpit UNLEASED lets the first draw's re-entry
        // succeed. (`tear_off_tab` keeps the lease-wrapped form for the ⌘K command
        // path, which already runs outside a lease — but routes through this same
        // unleased open.)
        cx.defer(move |app: &mut App| {
            Self::tear_off_tab_unleased(weak, tab, app);
        });
    }

    /// TEAR OFF `tab` into its own OS window NOW. Defers to the UNLEASED open so the
    /// torn window's synchronous first draw can re-enter the cockpit (the crash fix —
    /// see [`Self::tear_off_tab_deferred`]). Driven by the ⌘K command (which holds a
    /// cockpit lease here), so it must NOT open the window inline; it schedules the
    /// unleased open on the next app pass exactly as the pane control does.
    #[allow(dead_code)] // ⌘K-driven tear-off entry point; kept API alongside the pane control
    pub(crate) fn tear_off_tab(&mut self, tab: Tab, cx: &mut Context<Self>) {
        self.tear_off_tab_deferred(tab, cx);
    }

    /// The window-open itself, run with the cockpit UNLEASED (`&mut App`, no
    /// `Context<Self>` in hand) so the torn window's synchronous first draw — whose
    /// mirror callback re-enters the cockpit — does not nest inside a cockpit lease
    /// (the crash). It briefly leases the cockpit to take the [`WindowRegistry`] out
    /// + build the render seam, opens the window with the cockpit FREE, then briefly
    ///   re-leases to record the result + persist. Mints a window whose root renders
    ///   `tab`'s body via the host re-entry — the SAME body, over the SAME cell, the
    ///   dock pane showed (identity preserved). Idempotent: a second tear-off of an
    ///   already-torn `tab` re-focuses the existing window. A platform refusal is
    ///   surfaced fail-closed in the outcome banner (nothing is recorded).
    fn tear_off_tab_unleased(weak: WeakEntity<Self>, tab: Tab, app: &mut App) {
        let id = DockSurfaceId(tab.index() as u64);
        let label = tab.label();

        // The render callback is the identity-preserving seam: it re-enters THIS
        // cockpit (weak handle) and dispatches the SAME `panel_for_tab(tab)` the
        // in-dock `TabSurface` calls — so the torn-off window paints the live
        // surface, never a snapshot.
        let render = {
            let weak = weak.clone();
            move |_window: &mut Window, app: &mut App| -> gpui::AnyElement {
                // The torn window is the surface's ONE rendering site while torn:
                // force the live body here (the in-dock `panel_for_tab` shows the
                // torn-off placeholder for this tab, so the shared live entity is
                // painted in exactly one window — the beachball fix).
                weak.update(app, |cockpit, cx| cockpit.panel_for_tab_forced(tab, cx))
                    .unwrap_or_else(|_| {
                        div()
                            .flex()
                            .items_center()
                            .justify_center()
                            .size_full()
                            .text_color(theme::muted())
                            .child(SharedString::from(label))
                            .into_any_element()
                    })
            }
        };

        // STEP 1 (brief lease): prune dead windows, compute the surface's
        // identity/cap-badge (who/what authority it runs under — the same operator
        // principal + c-list count the top bar shows), and TAKE the registry out of
        // the cockpit, so the open below runs without holding the cockpit borrowed.
        let Some((mut registry, badge)) = weak
            .update(app, |this, cx| {
                this.window_registry.prune_closed(cx);
                let badge = this.torn_off_badge();
                (std::mem::take(&mut this.window_registry), badge)
            })
            .ok()
        else {
            return; // cockpit gone — nothing to do.
        };

        // STEP 2 (cockpit UNLEASED): open the window. Its synchronous first draw
        // re-enters the cockpit via `render` above — which now succeeds, because we
        // are NOT inside a cockpit lease here. This is the line that previously
        // aborted the process.
        let outcome = match registry.tear_off(id, label, badge, render, app) {
            Ok(_handle) => {
                let torn = registry.len();
                Ok(format!(
                    "↗ tore off {label} into its own window — surface identity preserved \
                     (Local→Surface migration; {torn} torn-off window{}; pop-out persisted)",
                    if torn == 1 { "" } else { "s" }
                ))
            }
            Err(e) => Err(format!("could not tear off {label}: {e}")),
        };

        // STEP 3 (brief lease): put the registry back, persist the pop-out, set the
        // banner, notify. (The registry was `mem::take`n, so the cockpit held a
        // Default empty one in the interim — no other code touches it between the two
        // leases, both of which run on this single app pass with no draw between.)
        let _ = weak.update(app, |this, cx| {
            this.window_registry = registry;
            if outcome.is_ok() {
                // PERSIST the pop-out: mark this tab torn off in the WorkspaceCell and
                // land the witnessed commit, so a crash-relaunch re-opens this window.
                // A commit failure leaves the in-memory bit set (the window IS open);
                // the witness catches up on the next commit.
                this.workspace_cell.set_torn(tab.index(), true);
                let _ = this.workspace_cell.commit(&mut this.world.borrow_mut());
            }
            this.last_outcome = Some(match &outcome {
                Ok(s) | Err(s) => s.clone(),
            });
            cx.notify();
        });
    }

    /// POP BACK the active tab's torn-off window (the inverse Surface-window →
    /// Surface-in-dock migration): close the OS window, the surface lives only in
    /// the dock again. A no-op (with an honest banner) if it is not torn off.
    pub(crate) fn pop_back_active_tab(&mut self, cx: &mut Context<Self>) {
        let tab = self.active_tab();
        self.pop_back_tab(tab, cx);
    }

    /// POP BACK `tab`'s torn-off window if open. Returns whether one was closed.
    pub(crate) fn pop_back_tab(&mut self, tab: Tab, cx: &mut Context<Self>) {
        let id = DockSurfaceId(tab.index() as u64);
        let label = tab.label();
        if self.window_registry.pop_back(id, cx) {
            // PERSIST the pop-back: clear this tab's torn-off bit + witness it, so a
            // relaunch no longer re-pops a window the operator has docked again.
            self.workspace_cell.set_torn(tab.index(), false);
            let _ = self.workspace_cell.commit(&mut self.world.borrow_mut());
            self.last_outcome = Some(format!("↩ popped {label} back into the dock"));
        } else {
            self.last_outcome = Some(format!("{label} is not torn off (nothing to pop back)"));
        }
        cx.notify();
    }

    /// RESTORE the torn-off windows the durable image records (the crash-relaunch
    /// seam). Reads the [`WorkspaceCell`]'s committed torn-off-tabs bitset and
    /// re-opens an OS window for each tab that was popped out, re-establishing the
    /// pop-out layout a reopened image had — the restoration half of the migration's
    /// durability. Idempotent: a tab already torn off (its window already open) is
    /// skipped (`tear_off` re-activates rather than duplicating). Bounds default to
    /// the migration's `Bounds::centered` (WHICH tabs were popped out is the durable
    /// state; per-window geometry is not yet packed — a reopen re-centers each).
    ///
    /// Driven once on first render (after the pane group is seeded), so the reopened
    /// image's pop-out windows come back with the cockpit. A no-op when nothing was
    /// torn off (the common single-window case).
    pub(crate) fn restore_torn_windows(&mut self, cx: &mut Context<Self>) {
        let want = self
            .workspace_cell
            .committed_torn_indices(&self.world.borrow());
        if want.is_empty() {
            return;
        }
        for idx in want {
            let tab = Tab::from_index(idx);
            // Mirror the in-memory draft to the committed set so a later witness does
            // not clear the bit we are restoring.
            self.workspace_cell.set_torn(idx, true);
            if self.window_registry.is_torn_off(DockSurfaceId(idx as u64)) {
                continue;
            }
            // DEFER the open: opening an OS window re-enters the app, so it must run
            // with the cockpit at rest AFTER this render unwinds (the same reason
            // `tear_off_active_tab` defers). `tear_off_tab_deferred` re-enters the
            // cockpit on a later app pass.
            self.tear_off_tab_deferred(tab, cx);
        }
    }

    /// Whether `tab` is currently torn off into its own window (drives the pane
    /// control's ↗/↩ label so it toggles pop-out ⇄ pop-back).
    pub(crate) fn tab_is_torn_off(&self, tab: Tab) -> bool {
        self.window_registry
            .is_torn_off(DockSurfaceId(tab.index() as u64))
    }

    /// The operator IDENTITY / cap-badge a torn-off window's chrome shows — the
    /// same `you · {id} · 🔑 {n} caps` the persistent top bar carries, so a popped
    /// pane names WHICH authority it runs under (identifiable, not anonymous). The
    /// firmament "one cap across distance" made visible at the second window.
    pub(crate) fn torn_off_badge(&self) -> SharedString {
        let w = self.world.borrow();
        let user = self.anchors[2];
        let id_short = reflect::short_hex(user.as_bytes());
        let cap_count = w
            .ledger()
            .get(&user)
            .map(|c| c.capabilities.len())
            .unwrap_or(0);
        SharedString::from(format!("you · {id_short} · 🔑 {cap_count} caps"))
    }

    /// THE HOME panel — the warm LANDING portal (the boot view). Renders the
    /// [`LandingPortal`](starbridge_v2::landing::LandingPortal) text model
    /// (built fresh from the live [`World`], so its numbers are the running
    /// image's actual numbers) as native gpui text: a big greeting, then a stack
    /// of titled cards that name the running system reflectively — where you are,
    /// the image right now, the verified heart, the receipt nervous system, the
    /// organs, and how to begin. This is the alive front door: real, abundant
    /// text inviting you in (the anti-blank surface).
    pub(crate) fn home_panel(&self) -> impl IntoElement {
        let portal = starbridge_v2::landing::LandingPortal::build(&self.world.borrow());

        // The greeting masthead — the big "you have arrived" headline + subtitle,
        // with a live liveness pill so the portal visibly breathes.
        let w = self.world.borrow();
        let masthead = div()
            .flex()
            .flex_col()
            .gap_1()
            .p_4()
            .rounded_md()
            .border_1()
            .border_color(theme::accent())
            .bg(theme::panel())
            .child(
                div()
                    .text_2xl()
                    .text_color(theme::text())
                    .child(portal.headline.clone()),
            )
            .child(
                div()
                    .text_sm()
                    .text_color(theme::muted())
                    .child(portal.subtitle.clone()),
            )
            .child(
                div()
                    .flex()
                    .flex_wrap()
                    .gap_1()
                    .mt_1()
                    .child(pill("● live", theme::good()))
                    .child(pill("embedded verified executor", theme::good()))
                    .child(pill(format!("h{}", w.height()), theme::accent()))
                    .child(pill(format!("{} cells", w.cell_count()), theme::accent()))
                    .child(pill(
                        format!("{} receipts", w.receipts().len()),
                        theme::accent(),
                    )),
            );
        drop(w);

        // Each portal section becomes a card; each line is real text, colored by
        // its semantic tone.
        let mut col = div()
            .id("cockpit-scroll-home")
            .flex()
            .flex_col()
            .gap_3()
            .p_4()
            .size_full()
            .overflow_y_scroll()
            .child(masthead);

        for section in &portal.sections {
            let mut card = div()
                .flex()
                .flex_col()
                .gap_1()
                .p_3()
                .rounded_md()
                .border_1()
                .border_color(theme::border())
                .bg(theme::panel())
                .child(section_title(section.title.clone()).mb_1());
            for line in &section.lines {
                let color = portal_tone_color(line.tone);
                let text_div = match line.tone {
                    // Headings render a touch larger; everything else is xs body.
                    starbridge_v2::landing::Tone::Heading => {
                        div().text_sm().text_color(color).child(line.text.clone())
                    }
                    _ => div().text_xs().text_color(color).child(line.text.clone()),
                };
                card = card.child(text_div);
            }
            col = col.child(card);
        }

        // The closing call-to-action.
        col = col.child(
            div()
                .text_sm()
                .text_color(theme::accent())
                .child(portal.invitation.clone()),
        );
        col
    }

    /// THE SHELL panel — the cap-first window manager / compositor. Composes the
    /// live [`Scene`] (surfaces over real cells, z-ordered) and renders each
    /// surface as a window with: a SHELL-DRAWN trusted-path identity header
    /// (anti-spoof — the owning cell id + lifecycle, read from the live ledger),
    /// the surface's own title, cap-gated window controls, and a body of the
    /// real cell's state. The whole compositor reacts to real turns (it re-reads
    /// the world each frame).
    pub(crate) fn shell_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let scene: Scene = self.shell.compose(&w);
        let layout = scene.layout;
        let focused = scene.focused;

        let mut col = div()
            .id("cockpit-scroll-body-8")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title("SHELL · cap-first compositor over real cells").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Each dregg CELL is a cap-confined SURFACE. Every window op (focus · close · \
             minimize) is GATED by the surface's capability — there is no ambient authority. \
             The identity badge on each surface is drawn by the SHELL from the live ledger \
             (anti-spoof), so a surface cannot impersonate another cell.",
        ));

        // The compositor toolbar: layout + the cap-gated ops.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(format!("layout: {}", layout.label()), theme::accent()))
                .child(pill(
                    format!("{} surfaces", self.shell.surface_count()),
                    theme::good(),
                ))
                .child(pill(
                    format!("console s{}", self.console_surface.as_u64()),
                    theme::warn(),
                ))
                .child(shell_button(
                    cx,
                    "open selected as surface",
                    theme::good(),
                    Cockpit::shell_open_selected,
                ))
                .child(shell_button(
                    cx,
                    "focus front",
                    theme::accent(),
                    Cockpit::shell_focus_front,
                ))
                .child(shell_button(
                    cx,
                    "minimize focused",
                    theme::accent(),
                    Cockpit::shell_minimize_focused,
                ))
                .child(shell_button(
                    cx,
                    "present focused (commits)",
                    theme::good(),
                    Cockpit::shell_present_focused,
                ))
                .child(shell_button(
                    cx,
                    "⚠ overpaint (T1 REJECT)",
                    theme::warn(),
                    Cockpit::shell_overpaint_focused,
                ))
                .child(shell_button(
                    cx,
                    "⚠ input-steal (T3 REJECT)",
                    theme::warn(),
                    Cockpit::shell_input_steal,
                ))
                .child(shell_button(
                    cx,
                    "share (read-only mirror)",
                    theme::good(),
                    Cockpit::shell_share_focused,
                ))
                .child(shell_button(
                    cx,
                    "⚠ over-share (watch it REJECT)",
                    theme::warn(),
                    Cockpit::shell_overshare_focused,
                ))
                .child(shell_button(
                    cx,
                    "close focused",
                    theme::warn(),
                    Cockpit::shell_close_focused,
                ))
                .child(shell_button(
                    cx,
                    "cycle layout",
                    theme::accent(),
                    Cockpit::shell_cycle_layout,
                )),
        );
        col = col.child(self.outcome_banner());
        // The verified-scene legend: the three teeth the compositor enforces.
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Verified scene (the Lean Compositor AppSpec, on glass): T1 NON-OVERLAP — a surface \
             paints only its own cap-authorized region (overpaint REFUSED); T2 LABEL-BINDING — the \
             identity badge is a function of the owner + state-root the SHELL reads (spoof REFUSED); \
             T3 FOCUS-EXCLUSIVITY — input routes only to the one focused surface (steal REFUSED).",
        ));
        // The frame log: how many genuine presents have committed (provenance).
        col = col.child(
            div()
                .flex()
                .gap_1()
                .items_center()
                .child(pill(format!("{} frames committed", self.shell.frame_log().len()), theme::accent()))
                .child(div().text_xs().text_color(theme::muted()).child(
                    "each frame is a present that passed T1∧T2∧T3 (a refused present logs none — fail-closed)",
                )),
        );

        // The composed scene: surfaces front-to-back (front first, so the most
        // recently focused window reads at the top of the list).
        let mut stack = div().flex().flex_col().gap_2().mt_1();
        for item in scene.items.iter().rev() {
            let id = item.surface.id();
            let is_focused = focused == Some(id);
            let is_console = item.surface.is_console();
            let held_cap = self.surface_caps.contains_key(&id);

            // The trusted-path identity header — SHELL-drawn, from the ledger.
            let (badge_label, badge_color) = identity_badge(item.identity.lifecycle);
            let owner = if is_console {
                "SYSTEM (trusted root)".to_string()
            } else {
                format!("owner cell {}", item.identity.short)
            };

            // The window body: the real cell's live state (balance/nonce/caps/
            // lifecycle), read fresh from the ledger — never a mock.
            let body = self.surface_body(&item.surface.cell(), &w, is_console);

            let border = if is_focused {
                theme::accent()
            } else {
                theme::border()
            };
            stack = stack.child(
                div()
                    .id(SharedString::from(format!("surface-{}", id.as_u64())))
                    .flex()
                    .flex_col()
                    .rounded_md()
                    .border_1()
                    .border_color(border)
                    .bg(theme::panel())
                    .cursor_pointer()
                    // Clicking the surface is a HINT; the cap-gated focus is the
                    // authority (routed through `shell_click_surface`).
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.shell_click_surface(id, cx);
                        }),
                    )
                    // The title bar: identity badge (shell-drawn) + title + chrome.
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .items_center()
                            .px_2()
                            .py_1()
                            .rounded_md()
                            .bg(if is_focused {
                                theme::panel_hi()
                            } else {
                                theme::panel()
                            })
                            .border_b_1()
                            .border_color(theme::border())
                            .child(
                                div()
                                    .flex()
                                    .gap_2()
                                    .items_center()
                                    .child(
                                        div()
                                            .text_xs()
                                            .text_color(if is_console {
                                                theme::warn()
                                            } else {
                                                theme::accent()
                                            })
                                            .child(if is_console { "◆" } else { "⬡" }),
                                    )
                                    .child(
                                        div()
                                            .text_color(theme::text())
                                            .child(item.surface.title().to_string()),
                                    )
                                    .child(pill(badge_label, badge_color)),
                            )
                            .child(
                                div()
                                    .flex()
                                    .gap_1()
                                    .items_center()
                                    .child(
                                        div()
                                            .text_xs()
                                            .text_color(theme::muted())
                                            .child(format!("z{}", item.surface.z())),
                                    )
                                    .when(is_focused, |d| d.child(pill("focused", theme::good())))
                                    .when(item.surface.is_minimized(), |d| {
                                        d.child(pill("min", theme::muted()))
                                    })
                                    .when(!held_cap, |d| d.child(pill("no cap", theme::bad()))),
                            ),
                    )
                    // The trusted-path provenance line (anti-spoof): the owner the
                    // SHELL attests, plus whether the cell is backed in the ledger.
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .px_2()
                            .py_0p5()
                            .child(div().text_xs().text_color(theme::muted()).child(owner))
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(if item.identity.backed || is_console {
                                        theme::muted()
                                    } else {
                                        theme::bad()
                                    })
                                    .child(if is_console {
                                        "trusted-path: system console".to_string()
                                    } else if item.identity.backed {
                                        "trusted-path: shell-attested ✓".to_string()
                                    } else {
                                        "trusted-path: UNBACKED (cell missing)".to_string()
                                    }),
                            ),
                    )
                    // The body (the real cell's live state) — hidden when minimized.
                    .when(!item.surface.is_minimized(), |d| d.child(body)),
            );
        }
        col = col.child(stack);
        col
    }

    /// The body of a surface: the backing cell's LIVE state, read from the
    /// ledger. For the console it shows the image summary instead (it is the
    /// system's own root, not a single cell's view). Never a mock — this is the
    /// surface "reacting to real turns".
    pub(crate) fn surface_body(
        &self,
        cell: &CellId,
        w: &World,
        is_console: bool,
    ) -> gpui::AnyElement {
        let mut body = div().flex().flex_col().gap_0p5().px_2().py_1();
        if is_console {
            body = body
                .child(div().text_xs().text_color(theme::muted()).child(format!(
                    "image · {} cells · h{} · {} receipts",
                    w.cell_count(),
                    w.height(),
                    w.receipts().len()
                )))
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::accent())
                        .child(format!("root {}", reflect::short_hex(&w.state_root()))),
                );
            return body.into_any_element();
        }
        match w.ledger().get(cell) {
            Some(c) => {
                let bal = c.state.balance();
                let bal_color = if bal < 0 {
                    theme::warn()
                } else {
                    theme::text()
                };
                body = body
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("balance"))
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(bal_color)
                                    .child(format!("{bal}")),
                            ),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("nonce"))
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(theme::text())
                                    .child(format!("{}", c.state.nonce())),
                            ),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(theme::muted())
                                    .child("capabilities"),
                            )
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(theme::text())
                                    .child(format!("{}", c.capabilities.len())),
                            ),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(theme::muted())
                                    .child("lifecycle"),
                            )
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(theme::text())
                                    .child(format!("{:?}", c.lifecycle)),
                            ),
                    );
            }
            None => {
                body = body.child(
                    div()
                        .text_xs()
                        .text_color(theme::bad())
                        .child("(backing cell is not in the ledger — a dangling surface)"),
                );
            }
        }
        body.into_any_element()
    }

    /// THE AGENT-ACTIVITY panel — the ADOS keystone. Renders an agent loop's
    /// PROVABLE activity as a cap-gated surface cell: its held mandate (the
    /// attenuated authority it runs under), its recent cap-gated turns + their
    /// receipts (the grounded seam, read from the embedded World's receipt log +
    /// dynamics stream), and the legible boundary of what it is authorized to do.
    /// Maps `agent::AgentActivity` (gpui-free) onto gpui — you watch the
    /// executor's receipts, not the agent's self-report.
    pub(crate) fn agent_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let act = self.agent_surface.activity(&w, 24);
        let live_slot0 = w
            .ledger()
            .get(&self.agent_surface.agent)
            .and_then(|c| c.state.get_field(AGENT_MEM_SLOT))
            .map(|fe| {
                let mut b = [0u8; 8];
                b.copy_from_slice(&fe[..8]);
                u64::from_le_bytes(b)
            })
            .unwrap_or(0);
        drop(w);

        let mut col = div()
            .id("cockpit-scroll-body-9")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(
            section_title("AGENT · the grounded loop (provable activity as a surface)").mb_1(),
        );
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "An agent is an intricate LOOP; dregg grounds the ONE seam that matters — its ACTIONS, \
             at the tool-call/turn boundary — by making every action a cap-gated, RECEIPTED, \
             conservation-checked turn. This surface renders that seam: the mandate it holds, the \
             turns it committed (with receipts), and the boundary of what it may do. You watch the \
             executor's truth, never the agent's self-report.",
        ));

        // The agent header: who it is + its live resources + grounded step count.
        let backed_color = if act.backed {
            theme::good()
        } else {
            theme::bad()
        };
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(format!("agent {}", act.short), theme::accent()))
                .child(pill(
                    if act.backed { "live" } else { "UNBACKED" }.to_string(),
                    backed_color,
                ))
                .child(pill(format!("balance {}", act.balance), theme::text()))
                .child(pill(
                    format!("{} committed turns", act.committed_action_count()),
                    theme::good(),
                ))
                .child(pill(
                    format!("reach {} cell(s)", act.reach()),
                    theme::accent(),
                ))
                .child(pill(format!("nonce {}", act.nonce), theme::muted())),
        );

        // --- THE HELD MANDATE (the attenuated authority the loop runs under) ---
        col = col.child(section_title("held mandate (adoption = attenuation)").mt_2());
        if act.mandate.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "holds NO outbound capability — this agent is confined to itself (the narrowest mandate).",
            ));
        } else {
            let mut edges = div().flex().flex_col().gap_0p5();
            for m in &act.mandate {
                let rights_color = match m.rights_label() {
                    "open" => theme::warn(),
                    "locked" => theme::bad(),
                    _ => theme::good(),
                };
                edges = edges.child(
                    div()
                        .flex()
                        .justify_between()
                        .items_center()
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel())
                        .child(
                            div()
                                .flex()
                                .gap_2()
                                .items_center()
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(theme::muted())
                                        .child(format!("slot {}", m.slot)),
                                )
                                .child(div().text_xs().text_color(theme::text()).child(format!(
                                    "→ {}",
                                    reflect::short_hex(m.target.as_bytes())
                                )))
                                .child(pill(m.rights_label(), rights_color)),
                        )
                        .child(
                            div()
                                .flex()
                                .gap_1()
                                .items_center()
                                .when(m.faceted, |d| d.child(pill("faceted", theme::accent())))
                                .when(m.expires_at.is_some(), |d| {
                                    d.child(pill(
                                        format!("expires @{}", m.expires_at.unwrap()),
                                        theme::warn(),
                                    ))
                                }),
                        ),
                );
            }
            col = col.child(edges);
        }

        // --- THE CAP-GATED ACTIONS (turns) + their RECEIPTS (the grounded seam) ---
        col = col.child(section_title("recent cap-gated actions (turns + receipts)").mt_2());
        if act.actions.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "no actions yet — this agent's loop has not committed (or attempted) a turn.",
            ));
        } else {
            let mut rows = div().flex().flex_col().gap_0p5();
            for a in &act.actions {
                let (mark, mark_color) = if a.committed {
                    ("✓", theme::good())
                } else {
                    ("✗", theme::bad())
                };
                let height_label = a
                    .height
                    .map(|h| format!("h{h}"))
                    .unwrap_or_else(|| "—".to_string());
                rows = rows.child(
                    div()
                        .flex()
                        .justify_between()
                        .items_center()
                        .px_2()
                        .py_0p5()
                        .child(
                            div()
                                .flex()
                                .gap_2()
                                .items_center()
                                .child(div().text_xs().text_color(mark_color).child(mark))
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(theme::muted())
                                        .child(height_label),
                                )
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(if a.committed {
                                            theme::text()
                                        } else {
                                            theme::bad()
                                        })
                                        .child(a.summary.clone()),
                                ),
                        )
                        .child(
                            div()
                                .flex()
                                .gap_1()
                                .items_center()
                                .when(a.committed, |d| {
                                    d.child(div().text_xs().text_color(theme::muted()).child(
                                        format!("{} act · {} ⚙", a.action_count, a.computrons),
                                    ))
                                })
                                .when(a.receipt_hash.is_some(), |d| {
                                    d.child(pill(
                                        reflect::short_hex(&a.receipt_hash.unwrap()),
                                        theme::good(),
                                    ))
                                }),
                        ),
                );
            }
            col = col.child(rows);
        }

        // --- WHAT IT IS AUTHORIZED TO DO (the boundary of the loop's reach) ---
        col = col.child(section_title("what it is authorized to do (the boundary)").mt_2());
        let mut auths = div().flex().flex_col().gap_0p5();
        for a in &act.authorizations {
            let (mark, mark_color) = if a.permitted {
                ("CAN", theme::good())
            } else {
                ("CANNOT", theme::bad())
            };
            auths = auths.child(
                div()
                    .flex()
                    .justify_between()
                    .items_center()
                    .px_2()
                    .py_0p5()
                    .child(
                        div()
                            .flex()
                            .gap_2()
                            .items_center()
                            .child(pill(mark, mark_color))
                            .child(div().text_xs().text_color(theme::text()).child(a.verb)),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(a.note.clone()),
                    ),
            );
        }
        col = col.child(auths);

        // --- AGENT MEMORY as a umem (checkpoint · handoff · resume) ----------
        // The agent-memory revolution made a clickable affordance: the LIVE agent's
        // whole working-set projected to the universal address space (a witnessed,
        // portable umem-ref), CHECKPOINTED on a click and RESUMED into a fresh
        // verified context that CONTINUES from exactly where it left off. The sibling
        // of the TIME tab's verified reconstruction — fail-closed under the SAME
        // anti-substitution root tooth.
        col = col.child(section_title("agent memory · umem checkpoint · handoff · resume").mt_2());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "A confined agent's working-set IS its cell's state. Project it into the universal \
             address space and it becomes a umem-ref: a witnessed, portable, comparable object. \
             ⛂ CHECKPOINT captures the live working-set; ↺ RESUME reconstitutes a FRESH verified \
             context from it that CONTINUES from the checkpoint — fail-closed under the root tooth.",
        ));
        // The control row.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(small_button(
                    cx,
                    "agent-mem-advance",
                    "⊕ advance working-set (+1)",
                    theme::accent(),
                    Cockpit::agent_memory_advance,
                ))
                .child(small_button(
                    cx,
                    "agent-mem-checkpoint",
                    "⛂ checkpoint working-set",
                    theme::good(),
                    Cockpit::agent_memory_checkpoint,
                ))
                .child(small_button(
                    cx,
                    "agent-mem-resume",
                    "↺ resume into fresh context",
                    if self.agent_memory.is_some() {
                        theme::warn()
                    } else {
                        theme::muted()
                    },
                    Cockpit::agent_memory_resume,
                )),
        );
        // The live working-set readout + the held checkpoint (and any drift since).
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .mt_1()
                .child(pill(
                    format!("live working-slot[{AGENT_MEM_SLOT}] = {live_slot0}"),
                    theme::text(),
                ))
                .when(self.agent_memory.is_some(), |d| {
                    let cp = self.agent_memory.as_ref().unwrap();
                    let cp_slot = cp.working_slot(AGENT_MEM_SLOT);
                    d.child(pill(
                        format!("⛂ checkpoint slot[{AGENT_MEM_SLOT}] = {cp_slot}"),
                        theme::good(),
                    ))
                    .child(pill(
                        format!("root {}", reflect::short_hex(&cp.root)),
                        theme::muted(),
                    ))
                    .when(cp_slot != live_slot0, |d| {
                        d.child(pill(
                            format!(
                                "Δ live moved {} past the checkpoint",
                                live_slot0 as i64 - cp_slot as i64
                            ),
                            theme::warn(),
                        ))
                    })
                })
                .when(self.agent_memory.is_none(), |d| {
                    d.child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child("(no checkpoint yet — ⛂ to capture the working-set)"),
                    )
                }),
        );
        // The resumed-context witness (the fresh verified context's continued
        // working-set + the fail-closed teeth verdict).
        if let Some((resumed_slot, teeth)) = self.agent_memory_resumed {
            col = col.child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .mt_1()
                    .p_2()
                    .rounded_md()
                    .border_1()
                    .border_color(if teeth { theme::good() } else { theme::bad() })
                    .bg(theme::panel())
                    .child(pill(
                        if teeth {
                            "↺ RESUMED ✓"
                        } else {
                            "↺ REFUSED"
                        }
                        .to_string(),
                        if teeth { theme::good() } else { theme::bad() },
                    ))
                    .child(div().text_xs().text_color(theme::text()).child(format!(
                        "fresh context continues from working-slot[0] = {resumed_slot}",
                    )))
                    .child(div().text_xs().text_color(theme::muted()).child(if teeth {
                        "root re-derived · umem byte-identical · identity preserved"
                    } else {
                        "the round-trip teeth did not pass"
                    })),
            );
        }
        // The last action verdict.
        if let Some(msg) = &self.agent_memory_status {
            col = col.child(
                div()
                    .mt_1()
                    .p_2()
                    .rounded_md()
                    .bg(theme::panel())
                    .text_xs()
                    .text_color(theme::muted())
                    .child(msg.clone()),
            );
        }

        col
    }

    /// ⊕ ADVANCE — commit ONE real verified turn on the LIVE agent that moves its
    /// working-set: a `tick` METHOD invocation (the agent publishes `{ping,
    /// set_status, tick}`; a confined agent only commits its OWN published methods —
    /// the `Cases` program default-denies anything else) carrying a `SetField` on the
    /// working slot + an `IncrementNonce`. So the operator can watch the live
    /// working-set move PAST a checkpoint — then ↺ resume recovers the checkpointed
    /// past. The method symbol is what lets a confined agent's turn through the gate.
    pub(crate) fn agent_memory_advance(&mut self, cx: &mut Context<Self>) {
        use dregg_turn::action::{symbol, Action, Authorization, CommitmentMode, DelegationMode};
        let agent = self.agent_surface.agent;
        let outcome = {
            let mut w = self.world.borrow_mut();
            let cur = w
                .ledger()
                .get(&agent)
                .and_then(|c| c.state.get_field(AGENT_MEM_SLOT))
                .map(|fe| {
                    let mut b = [0u8; 8];
                    b.copy_from_slice(&fe[..8]);
                    u64::from_le_bytes(b)
                })
                .unwrap_or(0);
            let mut next = [0u8; 32];
            next[..8].copy_from_slice(&(cur + 1).to_le_bytes());
            // Desugar to a `tick` method Action — the cell program's `MethodIs { tick }`
            // case admits it (NO new Effect variant; the kernel sees only effects it
            // already knows). A bare `World::turn` would carry the zero method symbol and
            // the agent's default-deny program would refuse it.
            let action = Action {
                target: agent,
                method: symbol("tick"),
                args: vec![],
                authorization: Authorization::Unchecked,
                preconditions: Default::default(),
                effects: vec![
                    world::set_field(agent, AGENT_MEM_SLOT, next),
                    world::increment_nonce(agent),
                ],
                may_delegate: DelegationMode::None,
                commitment_mode: CommitmentMode::default(),
                balance_change: None,
                witness_blobs: vec![],
            };
            let t = w.wrap_action_turn(agent, action);
            w.commit_turn(t)
        };
        self.agent_memory_status = Some(match outcome {
            CommitOutcome::Committed { .. } => {
                "⊕ advanced · the live working-set moved +1 (a real verified turn)".to_string()
            }
            CommitOutcome::Rejected { reason, .. } => format!("advance refused — {reason}"),
            CommitOutcome::Queued { .. } => {
                "⊕ advance staged into the frozen continuation (the loop is suspended)".to_string()
            }
        });
        cx.notify();
    }

    /// ⛂ CHECKPOINT — capture the LIVE agent's working-set to a umem-ref
    /// ([`agent_memory::AgentMemoryCheckpoint::capture`]). PURE: never mutates the
    /// live World — it projects state the agent already owns into a witnessed,
    /// portable object held in the cockpit (the umem-ref on the wire).
    pub(crate) fn agent_memory_checkpoint(&mut self, cx: &mut Context<Self>) {
        let agent = self.agent_surface.agent;
        let captured = {
            let w = self.world.borrow();
            starbridge_v2::agent_memory::AgentMemoryCheckpoint::capture(&w, agent)
        };
        match captured {
            Ok(cp) => {
                let bytes = cp.to_bytes().map(|b| b.len()).unwrap_or(0);
                self.agent_memory_status = Some(format!(
                    "⛂ checkpointed · working-set → umem ({} planes · {} carrier bytes · slot[{}]={} · root {})",
                    cp.umem.len(),
                    bytes,
                    AGENT_MEM_SLOT,
                    cp.working_slot(AGENT_MEM_SLOT),
                    reflect::short_hex(&cp.root),
                ));
                self.agent_memory_resumed = None;
                self.agent_memory = Some(cp);
            }
            Err(e) => {
                self.agent_memory_status = Some(format!("checkpoint refused — {e}"));
            }
        }
        cx.notify();
    }

    /// ↺ RESUME — reconstitute a FRESH verified context from the held checkpoint
    /// ([`agent_memory::AgentMemoryCheckpoint::resume_into_fresh_world`]) and witness
    /// the handoff: the resumed agent continues from exactly the checkpointed
    /// working-set, the fail-closed teeth (root tooth · byte-identical re-projection ·
    /// identity) all pass or the resume REFUSES. The sibling of the TIME tab's verified
    /// reconstruction — it builds a fresh context (the live World is untouched).
    pub(crate) fn agent_memory_resume(&mut self, cx: &mut Context<Self>) {
        let Some(cp) = self.agent_memory.clone() else {
            self.agent_memory_status =
                Some("resume: no checkpoint yet — ⛂ checkpoint the working-set first".to_string());
            cx.notify();
            return;
        };
        match cp.resume_into_fresh_world() {
            Ok(resumed) => {
                // RE-CAPTURE the resumed fresh context and witness the round-trip teeth
                // against the held checkpoint (byte-identical umem + the re-derived root +
                // preserved identity). The resume's own teeth already gate this; the
                // re-capture is the operator-visible state-agreement square.
                let re =
                    starbridge_v2::agent_memory::AgentMemoryCheckpoint::capture(&resumed, cp.agent);
                let teeth = re
                    .as_ref()
                    .map(|r| r.umem == cp.umem && r.root == cp.root && r.agent == cp.agent)
                    .unwrap_or(false);
                let slot0 = re
                    .as_ref()
                    .map(|r| r.working_slot(AGENT_MEM_SLOT))
                    .unwrap_or_else(|_| cp.working_slot(AGENT_MEM_SLOT));
                self.agent_memory_resumed = Some((slot0, teeth));
                self.agent_memory_status = Some(format!(
                    "↺ resumed into a FRESH verified context · continues from slot[{AGENT_MEM_SLOT}]={slot0} · {}",
                    if teeth {
                        "teeth ✓ (root re-derived · umem byte-identical · identity preserved)"
                    } else {
                        "teeth ✗ DRIFT"
                    },
                ));
            }
            Err(e) => {
                self.agent_memory_resumed = Some((0, false));
                self.agent_memory_status = Some(format!("↺ resume REFUSED (fail-closed) — {e}"));
            }
        }
        cx.notify();
    }

    /// THE A2 SWARM PANEL — multi-agent cap-coordination surface.
    ///
    /// Renders the [`SwarmView`]: each member's mandate + action count + inbox,
    /// the inter-member notify-edge activity feed, and the demo action row
    /// (emit a wake / drain the inbox / transfer-and-wake in one turn).
    ///
    /// The point: you watch the EXECUTOR's receipts for each member's committed
    /// turns, and the INBOX accumulates pending wakes from peers' emits — all
    /// on-ledger truth, never a self-report. The async model (send ≠ receive)
    /// is visible: the coordinator's emit receipt and worker-a's drain receipt
    /// are DIFFERENT turns with DIFFERENT heights.
    pub(crate) fn swarm_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let view = SwarmView::build(&self.swarm, &w);
        drop(w);

        let mut col = div()
            .id("cockpit-scroll-body-10")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(
            section_title("SWARM (A2) · multi-agent cap-coordination · notify-edge inbox").mb_1(),
        );
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "N agent cells coordinating as confined Surface cells. Every action is a cap-gated, \
             receipted turn at the ONE seam. An EmitEvent deposits a NotifyEdge in the \
             recipient's inbox; the recipient drains it in its OWN separate future turn \
             (async — not a joint turn). You watch the executor's truth, never a self-report.",
        ));

        // Header: swarm stats.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(
                    format!("{} members", view.members.len()),
                    theme::accent(),
                ))
                .child(pill(
                    format!("{} total actions", view.total_actions),
                    theme::good(),
                ))
                .child(pill(
                    format!("{} pending wakes", view.total_pending),
                    if view.total_pending > 0 {
                        theme::warn()
                    } else {
                        theme::muted()
                    },
                )),
        );

        // Members: one row per member.
        col = col.child(section_title("members (cap-confined, mandate-gated)").mt_2());
        let mut members_col = div().flex().flex_col().gap_1();
        for m in &view.members {
            let backed_color = if m.backed {
                theme::good()
            } else {
                theme::bad()
            };
            let inbox_color = if m.pending_notify > 0 {
                theme::warn()
            } else {
                theme::muted()
            };
            members_col = members_col.child(
                div()
                    .flex()
                    .flex_col()
                    .gap_0p5()
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .bg(theme::panel())
                    .child(
                        div()
                            .flex()
                            .gap_1()
                            .items_center()
                            .child(pill(m.name.clone(), theme::accent()))
                            .child(pill(m.short.clone(), theme::muted()))
                            .child(pill(
                                if m.backed { "live" } else { "UNBACKED" },
                                backed_color,
                            ))
                            .child(pill(format!("bal {}", m.balance), theme::text()))
                            .child(pill(format!("{} actions", m.action_count), theme::good()))
                            .child(pill(format!("{} pending", m.pending_notify), inbox_color)),
                    )
                    .when(!m.inbox.is_empty(), |d| {
                        let mut inbox_div = div().flex().flex_col().gap_0p5().mt_1();
                        for n in &m.inbox {
                            let (mark, color) = if n.drained {
                                ("✓", theme::muted())
                            } else {
                                ("⚡", theme::warn())
                            };
                            inbox_div = inbox_div.child(
                                div()
                                    .flex()
                                    .gap_1()
                                    .items_center()
                                    .text_xs()
                                    .px_2()
                                    .child(div().text_color(color).child(mark))
                                    .child(
                                        div()
                                            .text_color(if n.drained {
                                                theme::muted()
                                            } else {
                                                theme::text()
                                            })
                                            .child(n.label()),
                                    ),
                            );
                        }
                        d.child(inbox_div)
                    }),
            );
        }
        col = col.child(members_col);

        // Action row: the demo verbs.
        col = col.child(section_title("demo actions (the A2 seam)").mt_2());
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(verb_button(
                    cx,
                    "coordinator emit task/go → worker-a",
                    theme::accent(),
                    Cockpit::swarm_coordinator_emit_a,
                ))
                .child(verb_button(
                    cx,
                    "worker-a DRAIN inbox (own ack turn)",
                    theme::good(),
                    Cockpit::swarm_worker_a_drain,
                ))
                .child(verb_button(
                    cx,
                    "coordinator: transfer + wake (one seam)",
                    theme::warn(),
                    Cockpit::swarm_coordinator_transfer_and_wake,
                )),
        );

        // ── THE FOUR-SURFACE KILLER DEMO (N5) — the pug-handoff artifact ──────
        col = col.child(
            section_title("⚑ the killer demo (N5) · the pug-handoff evaluation artifact").mt_3(),
        );
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "ONE end-to-end story, every step a real receipted turn: (1) MINT a token \
             cell via factory-birth · (2) AGENT A acts in-mandate (a budget spend) · \
             (3) A NOTIFIES B who drains it in its OWN turn (two distinct receipts) · \
             (4) the DUAL REFUSAL — an over-grant AND an over-spend, BOTH fail-closed \
             through the real executor. (pg step 5 deferred.)",
        ));
        // Demo state header: where the script is + the verified budget meter.
        // `set_tab(Swarm)` boots the demo before this renders, so it is normally
        // `Some`; the `None` arm is a graceful "booting" fallback only.
        {
            let mut hdr = div().flex().flex_wrap().gap_1().items_center().mt_1();
            if let Some(demo) = self.killer_demo.as_ref() {
                let cursor = demo.cursor();
                let total = HeadlineDemo::TOTAL_STEPS;
                let next = demo.next_step_label();
                hdr = hdr.child(pill(format!("frame {cursor}/{total}"), theme::accent()));
                if let Some(label) = next {
                    hdr = hdr.child(pill(format!("next: {label}"), theme::warn()));
                } else {
                    hdr = hdr.child(pill("script complete", theme::good()));
                }
                if let Some(v) = demo.swarm().stingray_view() {
                    hdr = hdr.child(pill(
                        format!("budget {}/{} computrons", v.total_drawn, v.ceiling),
                        if v.exhausted {
                            theme::bad()
                        } else {
                            theme::good()
                        },
                    ));
                }
            } else {
                hdr = hdr.child(pill("booting the demo…", theme::muted()));
            }
            col = col.child(hdr);
        }
        // The driver buttons.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .mt_1()
                .child(verb_button(
                    cx,
                    "▶ next frame",
                    theme::accent(),
                    Cockpit::killer_demo_advance,
                ))
                .child(verb_button(
                    cx,
                    "⏩ run all (the self-check)",
                    theme::good(),
                    Cockpit::killer_demo_run_all,
                ))
                .child(verb_button(
                    cx,
                    "⚠ over-share at the glass (pixel-layer refusal)",
                    theme::warn(),
                    Cockpit::killer_demo_over_share,
                ))
                .child(verb_button(
                    cx,
                    "↺ reset demo",
                    theme::muted(),
                    Cockpit::killer_demo_reset,
                )),
        );
        // The captured frame strip (the four frames + both refusals, as run).
        if self.killer_demo_lines.is_empty() {
            col =
                col.child(div().text_xs().text_color(theme::muted()).mt_1().child(
                    "press ▶ to run the first frame, or ⏩ to drive the whole script at once.",
                ));
        } else {
            let mut strip = div().flex().flex_col().gap_0p5().mt_1();
            for line in &self.killer_demo_lines {
                // A refusal line (carries "REFUSED") is colored as the teaching
                // moment; a commit line is neutral. The executor's reason (the
                // second line, indented) is muted.
                let is_refusal = line.contains("REFUSED");
                let color = if is_refusal {
                    theme::warn()
                } else {
                    theme::text()
                };
                for (i, sub) in line.lines().enumerate() {
                    let c = if i == 0 { color } else { theme::muted() };
                    strip = strip.child(
                        div()
                            .text_xs()
                            .px_2()
                            .text_color(c)
                            .child(sub.trim_end().to_string()),
                    );
                }
            }
            col = col.child(strip);
        }

        // Activity feed: recent swarm actions (newest-first).
        col = col.child(section_title("activity feed (executor receipts · notify edges)").mt_2());
        if view.activity.is_empty() {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("no swarm actions yet — use the buttons above to run the first turns."),
            );
        } else {
            let mut feed = div().flex().flex_col().gap_0p5();
            for entry in &view.activity {
                let (mark, mark_color) = if entry.committed {
                    ("✓", theme::good())
                } else {
                    ("✗", theme::bad())
                };
                let height_label = entry
                    .height
                    .map(|h| format!("h{h}"))
                    .unwrap_or_else(|| "—".to_string());
                let receipt_label = entry.receipt_short.as_deref().unwrap_or("—");
                feed = feed.child(
                    div()
                        .flex()
                        .flex_col()
                        .gap_0p5()
                        .px_2()
                        .py_0p5()
                        .rounded_sm()
                        .bg(theme::panel())
                        .child(
                            div()
                                .flex()
                                .gap_2()
                                .items_center()
                                .child(div().text_xs().text_color(mark_color).child(mark))
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(theme::muted())
                                        .child(height_label),
                                )
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(theme::accent())
                                        .child(entry.member_short.clone()),
                                )
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(if entry.committed {
                                            theme::text()
                                        } else {
                                            theme::bad()
                                        })
                                        .child(entry.summary.clone()),
                                )
                                .when(entry.committed, |d| {
                                    d.child(pill(receipt_label.to_string(), theme::good()))
                                }),
                        )
                        .when(!entry.notify_edges.is_empty(), |d| {
                            let mut edges_div = div().flex().flex_col().gap_0p5().px_2();
                            for edge_label in &entry.notify_edges {
                                edges_div = edges_div.child(
                                    div()
                                        .text_xs()
                                        .text_color(theme::warn())
                                        .child(format!("  ⚡ {edge_label}")),
                                );
                            }
                            d.child(edges_div)
                        }),
                );
            }
            col = col.child(feed);
        }

        col
    }

    /// THE TURN DEBUGGER panel — maps `debug::render`'s gpui-free model onto
    /// gpui elements (step list, conservation Σδ, the refusal explanation).
    pub(crate) fn debugger_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let panel = debug::render(&w, &self.debug_turn, &self.breakpoints);

        let mut col = div()
            .id("cockpit-scroll-body-11")
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title("DEBUGGER · step · inspect · explain").mb_1());
        col = col.child(div().text_color(theme::text()).child(panel.title.clone()));
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mb_2()
                .child(panel.subtitle.clone()),
        );

        // The step list.
        let mut steps = div().flex().flex_col().gap_0p5();
        for s in &panel.steps {
            let color = if !s.committed {
                theme::bad()
            } else if s.is_break {
                theme::warn()
            } else {
                theme::text()
            };
            steps = steps.child(
                div()
                    .flex()
                    .justify_between()
                    .px_2()
                    .child(div().text_xs().text_color(color).child(format!(
                        "{} k{} {}",
                        if s.is_break { "◆" } else { "·" },
                        s.index,
                        s.label
                    )))
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(format!("Σδ={}", s.conservation_delta)),
                    ),
            );
        }
        col = col.child(steps);

        // The refusal explanation (the prize) or the conserving commit line.
        col = col.child(match &panel.refusal {
            Some(r) => div()
                .mt_2()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .flex()
                .flex_col()
                .gap_0p5()
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::bad())
                        .child(format!("REFUSED · guard: {}", r.guard)),
                )
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::text())
                        .child(r.headline.clone()),
                )
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(r.detail.clone()),
                ),
            None => div()
                .mt_2()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .text_xs()
                .text_color(theme::good())
                .child(format!(
                    "COMMITS · final Σδ = {} (conserves)",
                    panel.final_conservation_delta
                )),
        });
        col
    }

    /// THE REPLAY / TIME-TRAVEL panel — `replay::replay_panel` returns gpui
    /// directly; the cockpit owns the cursor + any pinned fork and rebuilds the
    /// model each frame from the live world's REAL history.
    pub(crate) fn replay_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let history = w.recorded_turns();
        let cursor = self.replay_cursor.min(history.len());
        let model = replay::ReplayPanelModel::build(history, cursor, self.replay_fork.as_ref());
        div()
            .flex()
            .flex_col()
            .size_full()
            .child(replay::replay_panel(&model))
    }

    /// THE CIPHERCLERK panel — maps `cipherclerk::render`'s reflective lists
    /// onto the cockpit's shared inspector rows.
    pub(crate) fn cipherclerk_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let panel = cipherclerk::render(&self.clerk);
        let mut col = div()
            .id("cockpit-scroll-body-12")
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title("CIPHERCLERK · identities · tokens · delegations").mb_1());

        // The REAL macaroon action loop (mint → attenuate → delegate → discharge),
        // each driving `AgentCipherclerk`. Acts on alice (the holder) + bob (the
        // delegatee) over the "dns" service.
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .child("ACTIONS (alice · service 'dns')"),
        );
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(clerk_button(
                    cx,
                    "mint root",
                    theme::good(),
                    Cockpit::run_clerk_mint,
                ))
                .child(clerk_button(
                    cx,
                    "attenuate → r",
                    theme::accent(),
                    Cockpit::run_clerk_attenuate,
                ))
                .child(clerk_button(
                    cx,
                    "delegate → bob",
                    theme::accent(),
                    Cockpit::run_clerk_delegate,
                ))
                .child(clerk_button(
                    cx,
                    "discharge (verify)",
                    theme::warn(),
                    Cockpit::run_clerk_discharge,
                )),
        );
        // The real action result banner.
        col = col.child(self.clerk_banner());

        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mt_1()
                .child("IDENTITIES"),
        );
        for ins in &panel.identities {
            col = col.child(inspectable_row(ins));
        }
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mt_2()
                .child("HELD TOKENS"),
        );
        if panel.tokens.is_empty() {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .px_2()
                    .child("(none minted yet)"),
            );
        }
        for ins in &panel.tokens {
            col = col.child(inspectable_row(ins));
        }
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mt_2()
                .child("DELEGATIONS"),
        );
        if panel.delegations.is_empty() {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .px_2()
                    .child("(none recorded)"),
            );
        }
        for ins in &panel.delegations {
            col = col.child(inspectable_row(ins));
        }
        col
    }

    /// The cipherclerk action result banner (the real mint/attenuate/delegate/
    /// discharge outcome). Colors a denied discharge or a failure red.
    pub(crate) fn clerk_banner(&self) -> impl IntoElement {
        let (txt, color) = match &self.clerk_outcome {
            None => ("(run a clerk action above)".to_string(), theme::muted()),
            Some(o) => {
                let denied = matches!(
                    o,
                    cipherclerk::ClerkOutcome::Discharged {
                        authorized: false,
                        ..
                    }
                );
                let color = if !o.is_ok() || denied {
                    theme::bad()
                } else {
                    theme::good()
                };
                (o.banner(), color)
            }
        };
        div()
            .mt_1()
            .mb_1()
            .p_2()
            .rounded_md()
            .bg(theme::panel())
            .text_xs()
            .text_color(color)
            .child(txt)
    }

    /// THE OBJECTS panel — the reflective object views over the protocol
    /// surface beyond cells/receipts: each committed turn's PROOF / STARK status,
    /// the NULLIFIERS (consumed one-time authorities) it spent, and the
    /// lifecycle of every cell (live / sealed / destroyed). All projected through
    /// `reflect` from the live world — never a parallel schema.
    pub(crate) fn objects_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div()
            .id("cockpit-scroll-body-13")
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title("OBJECTS · proofs · nullifiers · lifecycle").mb_1());

        // Lifecycle column: every cell's lifecycle state (the seal/destroy axis).
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mt_1()
                .child("CELL LIFECYCLE"),
        );
        for id in &self.cells {
            if let Some(cell) = w.ledger().get(id) {
                let (label, color) = lifecycle_badge(&cell.lifecycle);
                col = col.child(
                    div()
                        .flex()
                        .justify_between()
                        .px_2()
                        .py_0p5()
                        .child(
                            div()
                                .text_xs()
                                .text_color(theme::text())
                                .child(format!("⬡ {}", reflect::short_hex(id.as_bytes()))),
                        )
                        .child(div().text_xs().text_color(color).child(label)),
                );
            }
        }

        // Proof status + nullifiers for the most recent receipts.
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mt_2()
                .child("TURN PROOFS (most recent)"),
        );
        if w.receipts().is_empty() {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .px_2()
                    .child("(no turns yet)"),
            );
        }
        for r in w.receipts().iter().rev().take(6) {
            let proof = reflect::reflect_proof_status(r);
            col = col.child(inspectable_row(&proof));
            for null in reflect::reflect_nullifiers(r) {
                col = col.child(inspectable_row(&null));
            }
        }
        col
    }

    /// THE GRAPH panel — the whole-graph ocap delegation layout. Renders the
    /// capability graph as nodes (cells, with in/out degree) + edges (grants,
    /// with rights), and — rooted on the first source cell — the LAYERED
    /// multi-hop delegation depth (root at depth 0, its grantees at depth 1, …)
    /// plus each source's transitive blast radius. The View tree IS the ocap
    /// graph (`starbridge_v2::graph`).
    pub(crate) fn graph_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let g = starbridge_v2::graph::OcapGraph::build(&w);
        let mut col = div()
            .id("cockpit-scroll-body-14")
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title("GRAPH · ocap delegation (multi-hop)").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(format!(
            "{} cells · {} capability edges",
            g.node_count(),
            g.edge_count()
        )));

        // The EDGES — the literal ocap graph (holder ──rights──▶ target).
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mt_2()
                .child("CAPABILITY EDGES"),
        );
        if g.edge_count() == 0 {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .px_2()
                    .child("(no capability edges yet)"),
            );
        }
        for e in g.edges().iter().take(24) {
            let deleg = if e.is_delegated() {
                " · delegated"
            } else {
                ""
            };
            let facet = if e.faceted { " · faceted" } else { "" };
            col = col.child(
                div()
                    .flex()
                    .justify_between()
                    .px_2()
                    .py_0p5()
                    .child(div().text_xs().text_color(theme::text()).child(format!(
                        "⬡ {} ──▶ {}",
                        reflect::short_hex(e.holder.as_bytes()),
                        reflect::short_hex(e.target.as_bytes()),
                    )))
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::accent())
                            .child(format!("[{}]{deleg}{facet}", e.rights_label())),
                    ),
            );
        }

        // The LAYERED multi-hop layout, rooted on each source cell (no inbound
        // edge — the authority origins), with the transitive blast radius.
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mt_2()
                .child("MULTI-HOP LAYOUT (by delegation depth)"),
        );
        let roots = g.source_roots();
        if roots.is_empty() {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .px_2()
                    .child("(no source root — the graph may be cyclic)"),
            );
        }
        for root in roots.iter().take(4) {
            let reach = g.reach_count(root);
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::good())
                    .px_2()
                    .mt_1()
                    .child(format!(
                        "root {} · reaches {} cell(s) transitively{}",
                        reflect::short_hex(root.as_bytes()),
                        reach,
                        if g.has_cycle_from(root) {
                            " · ⟳ cyclic"
                        } else {
                            ""
                        },
                    )),
            );
            for layer in g.layered_from(root) {
                if layer.cells.is_empty() {
                    continue;
                }
                let cells: Vec<String> = layer
                    .cells
                    .iter()
                    .map(|c| reflect::short_hex(c.as_bytes()))
                    .collect();
                col = col.child(
                    div()
                        .text_xs()
                        .text_color(theme::text())
                        .px_3()
                        .child(format!("depth {}: {}", layer.depth, cells.join(", "))),
                );
            }
        }
        col
    }

    /// THE ORGANS panel — reflects each dregg organ's live cell-state. Trustline
    /// and flash-well organs are LIVE (embed-core: their enforcement is the cell's
    /// executor-installed program, fully readable from the embedded ledger);
    /// channel / mailbox / court are surfaced HONESTLY as remote-path (behind
    /// captp). See [`starbridge_v2::organs`].
    pub(crate) fn organs_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let survey = starbridge_v2::organs::OrganSurvey::build(&w);
        let mut col = div()
            .id("cockpit-scroll-body-15")
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title("ORGANS · live organ cell-state").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(format!(
            "{} live organ(s) (embed-core) · {} remote-path",
            survey.live_count(),
            survey.remote.len()
        )));

        // LIVE trustline organs.
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mt_2()
                .child("TRUSTLINES (live)"),
        );
        if survey.trustlines.is_empty() {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .px_2()
                    .child("(no trustline organ in the world)"),
            );
        }
        for t in &survey.trustlines {
            col = col.child(
                div()
                    .flex()
                    .flex_col()
                    .px_2()
                    .py_0p5()
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::text())
                            .child(format!("⬡ {} (trustline)", t.short)),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::accent())
                            .child(t.summary()),
                    ),
            );
        }

        // LIVE flash-well organs.
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mt_2()
                .child("FLASH WELLS (live)"),
        );
        if survey.flash_wells.is_empty() {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .px_2()
                    .child("(no flash-well organ in the world)"),
            );
        }
        for f in &survey.flash_wells {
            col = col.child(
                div()
                    .flex()
                    .flex_col()
                    .px_2()
                    .py_0p5()
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::text())
                            .child(format!("⬡ {} (flash well)", f.short)),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::accent())
                            .child(f.summary()),
                    ),
            );
        }

        // REMOTE-PATH organs (honest — kind + seam + route, not faked state).
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mt_2()
                .child("REMOTE-PATH ORGANS (need a connected node)"),
        );
        for o in &survey.remote {
            col = col.child(
                div()
                    .flex()
                    .flex_col()
                    .px_2()
                    .py_0p5()
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::warn())
                            .child(format!("⬡ {} — remote-path", o.kind)),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(o.seam.to_string()),
                    ),
            );
        }
        col
    }
}

// === THE POP-OUT (TEAR-OFF) CRASH REPRODUCTION + ITS FIX, PROVEN BY RUNNING ===
//
// ember launched the release binary, clicked the pane's "↗ pop out" control, and
// the WHOLE app aborted (`EXC_BAD_ACCESS`; the crash stack: gpui's Obj-C
// `handle_view_event` → `panic_cannot_unwind` → `process::abort`). The pop-out
// button's mouse-down handler PANICS, and because gpui's Obj-C event callback is a
// `nounwind` FFI boundary, that panic aborts the process instead of unwinding.
//
// THE ROOT: the pop-out button drives `tear_off_tab`, which opened the torn-off
// window through the MIRROR path (`WindowRegistry::tear_off`). The mirror's render
// callback re-enters THIS cockpit (`cockpit.panel_for_tab(tab, cx)`) every frame.
// But the dock pane's own `TabSurface` for that SAME tab ALSO re-enters the cockpit
// to render `panel_for_tab(tab, cx)` the same frame — two live re-entries of the one
// `Cockpit` entity in a single frame is a re-entrant `Entity::update` (and, for an
// entity-bearing tab, a double `track_focus`), which panics gpui.
//
// THE FIX: the pop-out now routes through the MOVE path. `tear_off_tab` switches the
// dock pane OFF the torn tab (so the dock stops rendering that tab's body) and opens
// the window OWNING a surface that renders the tab body in EXACTLY ONE place. Plus,
// the click handler is wrapped in `catch_unwind` (the load-bearing safety net) so a
// UI panic can NEVER cross the gpui nounwind boundary and abort the cockpit again.
//
// These tests DRIVE THE REAL CLICK→TEAR-OFF RENDER PATH (the prior headless test
// exercised only registry bookkeeping, never a same-frame double render of the live
// host), then drive both windows to an actual draw — reproducing ember's path.
#[cfg(all(test, feature = "render-capture"))]
mod popout_crash_repro {
    use super::*;
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::borrow::Cow;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    /// Stand up the same headless gpui app the cockpit bake uses (fonts registered,
    /// kit + theme inited), so the cockpit's gpui-component widgets + dock chrome
    /// render without panicking on a missing theme/font.
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
        cx.update(gpui_component::init);
        cx
    }

    /// Open a real cockpit window over the demo world, render it once (so the pane
    /// group is seeded + the dock pane shows the active tab), and return the cockpit
    /// entity + its window handle.
    fn boot_cockpit(cx: &mut HeadlessAppContext) -> (Entity<Cockpit>, gpui::WindowHandle<Cockpit>) {
        let (world, anchors) = world::demo_world();
        let shared = Rc::new(RefCell::new(world));
        let window = cx
            .open_window(size(px(1280.), px(832.)), |window, cx| {
                let view = cx.new(|cx| {
                    let focus = cx.focus_handle();
                    Cockpit::with_node(shared.clone(), anchors, focus, None, None)
                });
                view.update(cx, |c, cx| c.focus_on_open(window, cx));
                view
            })
            .expect("open the cockpit window");
        let entity = window.root(cx).expect("cockpit root entity");
        // FIRST DRAW — seeds the pane group; the dock pane now shows `active_tab`
        // (Home) via a `TabSurface` re-entering the cockpit.
        cx.run_until_parked();
        cx.update_window(window.into(), |_, w, _| w.refresh())
            .expect("refresh the cockpit window");
        cx.run_until_parked();
        (entity, window)
    }

    /// THE FAITHFUL REPRO + FIX, PROVEN BY DRAWING: drive the EXACT path the pane's
    /// "↗ pop out" button invokes — `tear_off_tab(active)` — then drive BOTH the
    /// cockpit window and the torn-off window to a real draw the SAME frame. Before
    /// the fix this is a re-entrant `Cockpit::update` (the dock `TabSurface` and the
    /// torn body both re-enter the host) → panic → (in the real app) a nounwind
    /// abort. With the move-not-mirror fix the torn tab is rendered in exactly one
    /// place, so the same-frame double draw is CLEAN.
    #[test]
    fn pop_out_active_tab_then_double_draw_does_not_panic() {
        let mut cx = headless();
        let (entity, window) = boot_cockpit(&mut cx);

        // Click the pop-out: this is exactly what the pane tab-bar's "↗ pop out"
        // `on_mouse_down` does (it calls `tear_off_tab_deferred(tab)`; we call the
        // live `tear_off_tab` directly — the body of that deferred re-entry — over
        // the active tab, which is what the standalone default view tears off).
        let torn_tab = entity.update(&mut cx, |c, _cx| c.active_tab());
        entity.update(&mut cx, |c, cx| c.tear_off_tab(torn_tab, cx));

        // Drive BOTH windows to an actual draw the same frame — this is where the
        // re-entrant render panics if the torn body and the dock body both re-enter
        // the host. `run_until_parked` flushes the deferred opens; the refreshes
        // force a real paint of each window.
        cx.run_until_parked();
        cx.update_window(window.into(), |_, w, _| w.refresh())
            .expect("refresh the cockpit window after tear-off");
        cx.run_until_parked();

        // The tab is recorded torn off (the move happened) and the cockpit is still
        // alive (no abort) — we can still read it.
        let torn = entity.update(&mut cx, |c, _cx| c.tab_is_torn_off(torn_tab));
        assert!(
            torn,
            "the active tab is recorded torn off into its own window"
        );
    }

    /// THE SAFETY NET, PROVEN: a deliberately-panicking UI action wrapped in the
    /// cockpit's event-boundary guard ([`Cockpit::guard_ui_event`]) LOGS + no-ops —
    /// it returns `false` and does NOT unwind past the guard, so a real gpui Obj-C
    /// event callback (a nounwind boundary) would never see the panic and never
    /// abort. (We assert the guard contains the panic; the cockpit survives.)
    #[test]
    fn ui_event_guard_turns_a_panicking_action_into_a_logged_no_op() {
        let mut cx = headless();
        let (entity, _window) = boot_cockpit(&mut cx);

        let survived = entity.update(&mut cx, |c, cx| {
            // A click handler that panics (e.g. an unwrap on a missing item). The
            // guard must contain it.
            let ok = Cockpit::guard_ui_event("test-panicking-click", || {
                panic!("deliberate UI panic inside a click handler");
            });
            assert!(!ok, "the guard reports the action panicked (no-op)");
            // The cockpit is still usable AFTER the contained panic — a normal
            // guarded action runs to completion.
            let ran = Cockpit::guard_ui_event("test-ok-click", || {
                c.last_outcome = Some("guarded click ran".into());
            });
            cx.notify();
            ran
        });
        assert!(
            survived,
            "a non-panicking guarded action returns true (ran)"
        );
    }
}

/// **THE AGENT-MEMORY-AS-umem AFFORDANCE, DRIVEN LIVE THROUGH THE COCKPIT.** Not
/// the standalone `agent_memory.rs` round-trip — this boots the REAL cockpit window
/// over the live demo World and clicks the Agent tab's checkpoint/resume controls
/// (the `Cockpit::agent_memory_*` verbs the buttons invoke), proving agent-memory is
/// load-bearing in a user-facing flow (the sibling of the TIME-tab scrub bake).
#[cfg(all(test, feature = "render-capture"))]
mod agent_memory_cockpit_affordance {
    use super::*;
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::borrow::Cow;
    use std::cell::RefCell;
    use std::rc::Rc;
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
        cx.update(gpui_component::init);
        cx
    }

    fn boot_cockpit(cx: &mut HeadlessAppContext) -> (Entity<Cockpit>, gpui::WindowHandle<Cockpit>) {
        let (world, anchors) = world::demo_world();
        let shared = Rc::new(RefCell::new(world));
        let window = cx
            .open_window(size(px(1280.), px(832.)), |window, cx| {
                let view = cx.new(|cx| {
                    let focus = cx.focus_handle();
                    Cockpit::with_node(shared.clone(), anchors, focus, None, None)
                });
                view.update(cx, |c, cx| c.focus_on_open(window, cx));
                view
            })
            .expect("open the cockpit window");
        let entity = window.root(cx).expect("cockpit root entity");
        cx.run_until_parked();
        cx.update_window(window.into(), |_, w, _| w.refresh())
            .expect("refresh the cockpit window");
        cx.run_until_parked();
        (entity, window)
    }

    /// THE LIVE COCKPIT ROUND-TRIP: advance the live agent → ⛂ checkpoint → advance
    /// PAST the checkpoint → ↺ resume into a fresh verified context. The resumed
    /// context continues from the CHECKPOINTED working-set (not the diverged live
    /// one), the fail-closed teeth pass, and the Agent panel renders through it all.
    #[test]
    fn clicking_checkpoint_then_resume_recovers_the_checkpointed_working_set() {
        let mut cx = headless();
        let (entity, window) = boot_cockpit(&mut cx);

        let read_slot = |cx: &HeadlessAppContext| -> u64 {
            entity.read_with(cx, |c, _| {
                let w = c.world.borrow();
                let cell = w.ledger().get(&c.agent_surface.agent).unwrap();
                let fe = cell
                    .state
                    .get_field(AGENT_MEM_SLOT)
                    .copied()
                    .unwrap_or([0u8; 32]);
                let mut b = [0u8; 8];
                b.copy_from_slice(&fe[..8]);
                u64::from_le_bytes(b)
            })
        };

        // The agent's working counter starts clean on the dedicated slot.
        let base = read_slot(&cx);

        // (1) ⊕ ADVANCE the live agent twice — its working-set moves via REAL turns.
        entity.update(&mut cx, |c, cx| c.agent_memory_advance(cx));
        let status1 = entity.read_with(&cx, |c, _| c.agent_memory_status.clone());
        entity.update(&mut cx, |c, cx| c.agent_memory_advance(cx));
        assert_eq!(
            read_slot(&cx),
            base + 2,
            "two advances moved the live working-set +2 (advance status: {status1:?})"
        );

        // (2) ⛂ CHECKPOINT — capture the live working-set to a umem-ref.
        entity.update(&mut cx, |c, cx| c.agent_memory_checkpoint(cx));
        let checkpoint_slot = entity.read_with(&cx, |c, _| {
            c.agent_memory
                .as_ref()
                .expect("the checkpoint is held after the click")
                .working_slot(AGENT_MEM_SLOT)
        });
        assert_eq!(
            checkpoint_slot,
            base + 2,
            "the checkpoint captured the working-set at the advanced point"
        );

        // (3) ⊕ ADVANCE PAST the checkpoint — the live agent diverges.
        entity.update(&mut cx, |c, cx| c.agent_memory_advance(cx));
        entity.update(&mut cx, |c, cx| c.agent_memory_advance(cx));
        assert_eq!(
            read_slot(&cx),
            base + 4,
            "the live agent advanced PAST the checkpoint"
        );

        // (4) ↺ RESUME into a fresh verified context from the held checkpoint.
        entity.update(&mut cx, |c, cx| c.agent_memory_resume(cx));
        let resumed = entity.read_with(&cx, |c, _| c.agent_memory_resumed);
        assert_eq!(
            resumed,
            Some((base + 2, true)),
            "the resumed FRESH context continues from the CHECKPOINT (base+2), not the diverged live (base+4), and the fail-closed teeth all passed"
        );

        // (5) THE PANEL RENDERS through the whole flow (no panic on a real draw).
        cx.update_window(window.into(), |_, w, _| w.refresh())
            .expect("refresh the cockpit after the agent-memory round-trip");
        cx.run_until_parked();
        let status = entity.read_with(&cx, |c, _| c.agent_memory_status.clone());
        assert!(
            status.map(|s| s.contains("resumed")).unwrap_or(false),
            "the Agent panel's memory section reflects the resume verdict"
        );
    }

    /// A TAMPERED carrier REFUSES through the cockpit verb too — fail-closed at the
    /// click. We corrupt the held checkpoint's umem, then ↺ resume: the root tooth
    /// bites and the panel shows the refusal (teeth NOT passed), never a faked resume.
    #[test]
    fn resume_is_fail_closed_through_the_cockpit() {
        let mut cx = headless();
        let (entity, _window) = boot_cockpit(&mut cx);

        entity.update(&mut cx, |c, cx| c.agent_memory_advance(cx));
        entity.update(&mut cx, |c, cx| c.agent_memory_checkpoint(cx));

        // Corrupt the held checkpoint's umem (a tamper to the working slot).
        entity.update(&mut cx, |c, _cx| {
            let agent = c.agent_surface.agent;
            let cp = c.agent_memory.as_mut().expect("a checkpoint is held");
            cp.umem.insert(
                dregg_turn::umem::UKey::Field {
                    cell: agent,
                    slot: 0,
                },
                dregg_turn::umem::UVal::Bytes32({
                    let mut fe = [0u8; 32];
                    fe[..8].copy_from_slice(&999u64.to_le_bytes());
                    fe
                }),
            );
        });

        entity.update(&mut cx, |c, cx| c.agent_memory_resume(cx));
        let resumed = entity.read_with(&cx, |c, _| c.agent_memory_resumed);
        assert_eq!(
            resumed,
            Some((0, false)),
            "the tampered carrier REFUSES to resume (the root tooth bites — fail-closed at the click)"
        );
        let status = entity.read_with(&cx, |c, _| c.agent_memory_status.clone());
        assert!(
            status.map(|s| s.contains("REFUSED")).unwrap_or(false),
            "the panel shows the fail-closed refusal, never a faked resume"
        );
    }
}
