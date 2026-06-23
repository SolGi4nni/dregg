//! Workspace/dock plumbing (tab bar, pane group, splits) + home/shell/agent/swarm/debugger/replay/cipherclerk/objects/graph/organs panels.

use super::*;

impl Cockpit {

    pub(crate) fn dynamics_feed(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_0p5().p_2();
        col = col.child(section_title("DYNAMICS · live").mb_1());
        let tail = w.dynamics().tail(12);
        if tail.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child("(quiet)"));
        }
        for ev in tail.iter().rev() {
            let is_reject = matches!(ev, dynamics::WorldEvent::TurnRejected { .. });
            col = col.child(
                div()
                    .text_xs()
                    .text_color(if is_reject { theme::bad() } else { theme::muted() })
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
        let mut row = div().flex().flex_wrap().gap_1().p_2().border_b_1().border_color(theme::border());
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
                    .bg(if active { theme::panel_hi() } else { theme::panel() })
                    .text_xs()
                    .text_color(if active { theme::accent() } else { theme::muted() })
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
        match tab {
            Tab::Home => self.home_panel().into_any_element(),
            Tab::Shell => self.shell_panel(cx).into_any_element(),
            Tab::Agent => self.agent_panel().into_any_element(),
            Tab::Swarm => self.swarm_panel(cx).into_any_element(),
            Tab::Graph => self.graph_panel().into_any_element(),
            Tab::Organs => self.organs_panel().into_any_element(),
            Tab::Proofs => self.proofs_panel().into_any_element(),
            Tab::WebOfCells => self.web_of_cells_panel(cx).into_any_element(),
            Tab::WebShell => self.webshell_panel(cx).into_any_element(),
            Tab::LinksHere => self.links_here_panel(cx).into_any_element(),
            Tab::Powerbox => self.powerbox_panel(cx).into_any_element(),
            Tab::Moldable => self.moldable_panel(cx).into_any_element(),
            Tab::InspectAct => self.inspect_act_panel(cx).into_any_element(),
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
            Tab::Composer => self.composer(cx).into_any_element(),
            Tab::Simulate => self.simulate_panel(cx).into_any_element(),
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
                        .on_mouse_down(
                            MouseButton::Left,
                            move |_ev, window, app| {
                                if let Some(src) = this_pane.upgrade() {
                                    let _ = weak.update(app, |cockpit, cx| {
                                        cockpit.split_pane(
                                            &src,
                                            SplitDirection::Right,
                                            window,
                                            cx,
                                        );
                                    });
                                }
                            },
                        )
                        .child("⊞ split"),
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
                        .bg(if is_active { theme::panel_hi() } else { theme::panel() })
                        .text_xs()
                        .text_color(if is_active { theme::accent() } else { theme::muted() })
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
        let fs = deos_zed::fs::RealFs::arc();
        let surface: Box<dyn CockpitSurface> =
            Box::new(EditorPane::new(id, fs, root, window, cx));
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
        let surface: Box<dyn CockpitSurface> = Box::new(AgentPane::demo(id, cx));
        self.graft_dev_pane(surface, window, cx);
    }

    /// Mint a dev-surface id in the high range (away from the `0..27` tab ids).
    /// Derived from the live pane count so repeated opens get distinct ids
    /// without a persistent counter field; a dev surface lives alone in its own
    /// pane, so uniqueness only needs to hold across simultaneously-open dev
    /// panes, which a growing pane count provides.
    #[cfg(feature = "dev-surfaces")]
    fn next_dev_surface_id(&self) -> u64 {
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
                        .bg(if is_active { theme::panel_hi() } else { theme::panel() })
                        .text_xs()
                        .text_color(if is_active { theme::accent() } else { theme::muted() })
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
            .child(div().text_2xl().text_color(theme::text()).child(portal.headline.clone()))
            .child(div().text_sm().text_color(theme::muted()).child(portal.subtitle.clone()))
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
                    .child(pill(format!("{} receipts", w.receipts().len()), theme::accent())),
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

        let mut col = div().id("cockpit-scroll-body-8").flex().flex_col().gap_2().p_3().size_full().overflow_y_scroll();
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
                .child(pill(format!("{} surfaces", self.shell.surface_count()), theme::good()))
                .child(pill(format!("console s{}", self.console_surface.as_u64()), theme::warn()))
                .child(shell_button(cx, "open selected as surface", theme::good(), Cockpit::shell_open_selected))
                .child(shell_button(cx, "focus front", theme::accent(), Cockpit::shell_focus_front))
                .child(shell_button(cx, "minimize focused", theme::accent(), Cockpit::shell_minimize_focused))
                .child(shell_button(cx, "present focused (commits)", theme::good(), Cockpit::shell_present_focused))
                .child(shell_button(cx, "⚠ overpaint (T1 REJECT)", theme::warn(), Cockpit::shell_overpaint_focused))
                .child(shell_button(cx, "⚠ input-steal (T3 REJECT)", theme::warn(), Cockpit::shell_input_steal))
                .child(shell_button(cx, "share (read-only mirror)", theme::good(), Cockpit::shell_share_focused))
                .child(shell_button(cx, "⚠ over-share (watch it REJECT)", theme::warn(), Cockpit::shell_overshare_focused))
                .child(shell_button(cx, "close focused", theme::warn(), Cockpit::shell_close_focused))
                .child(shell_button(cx, "cycle layout", theme::accent(), Cockpit::shell_cycle_layout)),
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

            let border = if is_focused { theme::accent() } else { theme::border() };
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
                            .bg(if is_focused { theme::panel_hi() } else { theme::panel() })
                            .border_b_1()
                            .border_color(theme::border())
                            .child(
                                div()
                                    .flex()
                                    .gap_2()
                                    .items_center()
                                    .child(div().text_xs().text_color(if is_console { theme::warn() } else { theme::accent() }).child(if is_console { "◆" } else { "⬡" }))
                                    .child(div().text_color(theme::text()).child(item.surface.title().to_string()))
                                    .child(pill(badge_label, badge_color)),
                            )
                            .child(
                                div()
                                    .flex()
                                    .gap_1()
                                    .items_center()
                                    .child(div().text_xs().text_color(theme::muted()).child(format!("z{}", item.surface.z())))
                                    .when(is_focused, |d| d.child(pill("focused", theme::good())))
                                    .when(item.surface.is_minimized(), |d| d.child(pill("min", theme::muted())))
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
                                    .text_color(if item.identity.backed || is_console { theme::muted() } else { theme::bad() })
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
    pub(crate) fn surface_body(&self, cell: &CellId, w: &World, is_console: bool) -> gpui::AnyElement {
        let mut body = div().flex().flex_col().gap_0p5().px_2().py_1();
        if is_console {
            body = body
                .child(div().text_xs().text_color(theme::muted()).child(format!(
                    "image · {} cells · h{} · {} receipts",
                    w.cell_count(),
                    w.height(),
                    w.receipts().len()
                )))
                .child(div().text_xs().text_color(theme::accent()).child(format!(
                    "root {}",
                    reflect::short_hex(&w.state_root())
                )));
            return body.into_any_element();
        }
        match w.ledger().get(cell) {
            Some(c) => {
                let bal = c.state.balance();
                let bal_color = if bal < 0 { theme::warn() } else { theme::text() };
                body = body
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("balance"))
                            .child(div().text_xs().text_color(bal_color).child(format!("{bal}"))),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("nonce"))
                            .child(div().text_xs().text_color(theme::text()).child(format!("{}", c.state.nonce()))),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("capabilities"))
                            .child(div().text_xs().text_color(theme::text()).child(format!("{}", c.capabilities.len()))),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("lifecycle"))
                            .child(div().text_xs().text_color(theme::text()).child(format!("{:?}", c.lifecycle))),
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
    pub(crate) fn agent_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let act = self.agent_surface.activity(&w, 24);

        let mut col = div().id("cockpit-scroll-body-9").flex().flex_col().gap_2().p_3().size_full().overflow_y_scroll();
        col = col.child(section_title("AGENT · the grounded loop (provable activity as a surface)").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "An agent is an intricate LOOP; dregg grounds the ONE seam that matters — its ACTIONS, \
             at the tool-call/turn boundary — by making every action a cap-gated, RECEIPTED, \
             conservation-checked turn. This surface renders that seam: the mandate it holds, the \
             turns it committed (with receipts), and the boundary of what it may do. You watch the \
             executor's truth, never the agent's self-report.",
        ));

        // The agent header: who it is + its live resources + grounded step count.
        let backed_color = if act.backed { theme::good() } else { theme::bad() };
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
                .child(pill(format!("{} committed turns", act.committed_action_count()), theme::good()))
                .child(pill(format!("reach {} cell(s)", act.reach()), theme::accent()))
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
                                .child(div().text_xs().text_color(theme::muted()).child(format!("slot {}", m.slot)))
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
                                    d.child(pill(format!("expires @{}", m.expires_at.unwrap()), theme::warn()))
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
                                .child(div().text_xs().text_color(theme::muted()).child(height_label))
                                .child(div().text_xs().text_color(if a.committed { theme::text() } else { theme::bad() }).child(a.summary.clone())),
                        )
                        .child(
                            div()
                                .flex()
                                .gap_1()
                                .items_center()
                                .when(a.committed, |d| {
                                    d.child(div().text_xs().text_color(theme::muted()).child(format!("{} act · {} ⚙", a.action_count, a.computrons)))
                                })
                                .when(a.receipt_hash.is_some(), |d| {
                                    d.child(pill(reflect::short_hex(&a.receipt_hash.unwrap()), theme::good()))
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
                    .child(div().text_xs().text_color(theme::muted()).child(a.note.clone())),
            );
        }
        col = col.child(auths);
        col
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

        let mut col = div().id("cockpit-scroll-body-10").flex().flex_col().gap_2().p_3().size_full().overflow_y_scroll();
        col = col.child(section_title("SWARM (A2) · multi-agent cap-coordination · notify-edge inbox").mb_1());
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
                .child(pill(format!("{} members", view.members.len()), theme::accent()))
                .child(pill(format!("{} total actions", view.total_actions), theme::good()))
                .child(pill(
                    format!("{} pending wakes", view.total_pending),
                    if view.total_pending > 0 { theme::warn() } else { theme::muted() },
                )),
        );

        // Members: one row per member.
        col = col.child(section_title("members (cap-confined, mandate-gated)").mt_2());
        let mut members_col = div().flex().flex_col().gap_1();
        for m in &view.members {
            let backed_color = if m.backed { theme::good() } else { theme::bad() };
            let inbox_color = if m.pending_notify > 0 { theme::warn() } else { theme::muted() };
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
                            .child(pill(if m.backed { "live" } else { "UNBACKED" }, backed_color))
                            .child(pill(format!("bal {}", m.balance), theme::text()))
                            .child(pill(format!("{} actions", m.action_count), theme::good()))
                            .child(pill(
                                format!("{} pending", m.pending_notify),
                                inbox_color,
                            )),
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
                                            .text_color(if n.drained { theme::muted() } else { theme::text() })
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
                .child(verb_button(cx, "coordinator emit task/go → worker-a", theme::accent(), Cockpit::swarm_coordinator_emit_a))
                .child(verb_button(cx, "worker-a DRAIN inbox (own ack turn)", theme::good(), Cockpit::swarm_worker_a_drain))
                .child(verb_button(cx, "coordinator: transfer + wake (one seam)", theme::warn(), Cockpit::swarm_coordinator_transfer_and_wake)),
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
                        if v.exhausted { theme::bad() } else { theme::good() },
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
                .child(verb_button(cx, "▶ next frame", theme::accent(), Cockpit::killer_demo_advance))
                .child(verb_button(cx, "⏩ run all (the self-check)", theme::good(), Cockpit::killer_demo_run_all))
                .child(verb_button(cx, "⚠ over-share at the glass (pixel-layer refusal)", theme::warn(), Cockpit::killer_demo_over_share))
                .child(verb_button(cx, "↺ reset demo", theme::muted(), Cockpit::killer_demo_reset)),
        );
        // The captured frame strip (the four frames + both refusals, as run).
        if self.killer_demo_lines.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child(
                "press ▶ to run the first frame, or ⏩ to drive the whole script at once.",
            ));
        } else {
            let mut strip = div().flex().flex_col().gap_0p5().mt_1();
            for line in &self.killer_demo_lines {
                // A refusal line (carries "REFUSED") is colored as the teaching
                // moment; a commit line is neutral. The executor's reason (the
                // second line, indented) is muted.
                let is_refusal = line.contains("REFUSED");
                let color = if is_refusal { theme::warn() } else { theme::text() };
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
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "no swarm actions yet — use the buttons above to run the first turns.",
            ));
        } else {
            let mut feed = div().flex().flex_col().gap_0p5();
            for entry in &view.activity {
                let (mark, mark_color) = if entry.committed {
                    ("✓", theme::good())
                } else {
                    ("✗", theme::bad())
                };
                let height_label = entry.height.map(|h| format!("h{h}")).unwrap_or_else(|| "—".to_string());
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
                                .child(div().text_xs().text_color(theme::muted()).child(height_label))
                                .child(div().text_xs().text_color(theme::accent()).child(entry.member_short.clone()))
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(if entry.committed { theme::text() } else { theme::bad() })
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

        let mut col = div().id("cockpit-scroll-body-11").flex().flex_col().gap_1().p_3().size_full().overflow_y_scroll();
        col = col.child(section_title("DEBUGGER · step · inspect · explain").mb_1());
        col = col.child(div().text_color(theme::text()).child(panel.title.clone()));
        col = col.child(div().text_xs().text_color(theme::muted()).mb_2().child(panel.subtitle.clone()));

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
                    .child(div().text_xs().text_color(theme::muted()).child(format!("Σδ={}", s.conservation_delta))),
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
                .child(div().text_xs().text_color(theme::bad()).child(format!("REFUSED · guard: {}", r.guard)))
                .child(div().text_xs().text_color(theme::text()).child(r.headline.clone()))
                .child(div().text_xs().text_color(theme::muted()).child(r.detail.clone())),
            None => div()
                .mt_2()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .text_xs()
                .text_color(theme::good())
                .child(format!("COMMITS · final Σδ = {} (conserves)", panel.final_conservation_delta)),
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
        let mut col = div().id("cockpit-scroll-body-12").flex().flex_col().gap_1().p_3().size_full().overflow_y_scroll();
        col = col.child(section_title("CIPHERCLERK · identities · tokens · delegations").mb_1());

        // The REAL macaroon action loop (mint → attenuate → delegate → discharge),
        // each driving `AgentCipherclerk`. Acts on alice (the holder) + bob (the
        // delegatee) over the "dns" service.
        col = col.child(div().text_xs().text_color(theme::muted()).child("ACTIONS (alice · service 'dns')"));
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(clerk_button(cx, "mint root", theme::good(), Cockpit::run_clerk_mint))
                .child(clerk_button(cx, "attenuate → r", theme::accent(), Cockpit::run_clerk_attenuate))
                .child(clerk_button(cx, "delegate → bob", theme::accent(), Cockpit::run_clerk_delegate))
                .child(clerk_button(cx, "discharge (verify)", theme::warn(), Cockpit::run_clerk_discharge)),
        );
        // The real action result banner.
        col = col.child(self.clerk_banner());

        col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child("IDENTITIES"));
        for ins in &panel.identities {
            col = col.child(inspectable_row(ins));
        }
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("HELD TOKENS"));
        if panel.tokens.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(none minted yet)"));
        }
        for ins in &panel.tokens {
            col = col.child(inspectable_row(ins));
        }
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("DELEGATIONS"));
        if panel.delegations.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(none recorded)"));
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
                    cipherclerk::ClerkOutcome::Discharged { authorized: false, .. }
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
        let mut col = div().id("cockpit-scroll-body-13").flex().flex_col().gap_1().p_3().size_full().overflow_y_scroll();
        col = col.child(section_title("OBJECTS · proofs · nullifiers · lifecycle").mb_1());

        // Lifecycle column: every cell's lifecycle state (the seal/destroy axis).
        col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child("CELL LIFECYCLE"));
        for id in &self.cells {
            if let Some(cell) = w.ledger().get(id) {
                let (label, color) = lifecycle_badge(&cell.lifecycle);
                col = col.child(
                    div()
                        .flex()
                        .justify_between()
                        .px_2()
                        .py_0p5()
                        .child(div().text_xs().text_color(theme::text()).child(format!("⬡ {}", reflect::short_hex(id.as_bytes()))))
                        .child(div().text_xs().text_color(color).child(label)),
                );
            }
        }

        // Proof status + nullifiers for the most recent receipts.
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("TURN PROOFS (most recent)"));
        if w.receipts().is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no turns yet)"));
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
        let mut col = div().id("cockpit-scroll-body-14").flex().flex_col().gap_1().p_3().size_full().overflow_y_scroll();
        col = col.child(section_title("GRAPH · ocap delegation (multi-hop)").mb_1());
        col = col.child(
            div().text_xs().text_color(theme::muted()).child(format!(
                "{} cells · {} capability edges",
                g.node_count(),
                g.edge_count()
            )),
        );

        // The EDGES — the literal ocap graph (holder ──rights──▶ target).
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("CAPABILITY EDGES"));
        if g.edge_count() == 0 {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no capability edges yet)"));
        }
        for e in g.edges().iter().take(24) {
            let deleg = if e.is_delegated() { " · delegated" } else { "" };
            let facet = if e.faceted { " · faceted" } else { "" };
            col = col.child(
                div()
                    .flex()
                    .justify_between()
                    .px_2()
                    .py_0p5()
                    .child(
                        div().text_xs().text_color(theme::text()).child(format!(
                            "⬡ {} ──▶ {}",
                            reflect::short_hex(e.holder.as_bytes()),
                            reflect::short_hex(e.target.as_bytes()),
                        )),
                    )
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
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("MULTI-HOP LAYOUT (by delegation depth)"));
        let roots = g.source_roots();
        if roots.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no source root — the graph may be cyclic)"));
        }
        for root in roots.iter().take(4) {
            let reach = g.reach_count(root);
            col = col.child(
                div().text_xs().text_color(theme::good()).px_2().mt_1().child(format!(
                    "root {} · reaches {} cell(s) transitively{}",
                    reflect::short_hex(root.as_bytes()),
                    reach,
                    if g.has_cycle_from(root) { " · ⟳ cyclic" } else { "" },
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
                    div().text_xs().text_color(theme::text()).px_3().child(format!(
                        "depth {}: {}",
                        layer.depth,
                        cells.join(", ")
                    )),
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
        let mut col = div().id("cockpit-scroll-body-15").flex().flex_col().gap_1().p_3().size_full().overflow_y_scroll();
        col = col.child(section_title("ORGANS · live organ cell-state").mb_1());
        col = col.child(
            div().text_xs().text_color(theme::muted()).child(format!(
                "{} live organ(s) (embed-core) · {} remote-path",
                survey.live_count(),
                survey.remote.len()
            )),
        );

        // LIVE trustline organs.
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("TRUSTLINES (live)"));
        if survey.trustlines.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no trustline organ in the world)"));
        }
        for t in &survey.trustlines {
            col = col.child(
                div().flex().flex_col().px_2().py_0p5()
                    .child(div().text_xs().text_color(theme::text()).child(format!("⬡ {} (trustline)", t.short)))
                    .child(div().text_xs().text_color(theme::accent()).child(t.summary())),
            );
        }

        // LIVE flash-well organs.
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("FLASH WELLS (live)"));
        if survey.flash_wells.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no flash-well organ in the world)"));
        }
        for f in &survey.flash_wells {
            col = col.child(
                div().flex().flex_col().px_2().py_0p5()
                    .child(div().text_xs().text_color(theme::text()).child(format!("⬡ {} (flash well)", f.short)))
                    .child(div().text_xs().text_color(theme::accent()).child(f.summary())),
            );
        }

        // REMOTE-PATH organs (honest — kind + seam + route, not faked state).
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("REMOTE-PATH ORGANS (need a connected node)"));
        for o in &survey.remote {
            col = col.child(
                div().flex().flex_col().px_2().py_0p5()
                    .child(div().text_xs().text_color(theme::warn()).child(format!("⬡ {} — remote-path", o.kind)))
                    .child(div().text_xs().text_color(theme::muted()).child(o.seam.to_string())),
            );
        }
        col
    }
}
