//! UI-exploration navigation API + the nav bar (capture/restore/back/forward, pins, macros).

use super::*;

impl Cockpit {
    // === UI-EXPLORATION NAV API ===========================================
    // A programmatic view of the cockpit's pure-navigation controls, so a
    // headless driver can BFS-walk the UI state-space (screenshot each state,
    // record the interaction edges) — the atlas's "UI tree". Navigation only
    // touches view-cell nonces (invisible to the render), so a captured
    // `CockpitNavState` fully restores the renderable state with no world fork.

    /// Capture the navigation-relevant UI state (cheap — scalars + the view
    /// cell's focus/present aim).
    pub fn capture_nav(&self) -> CockpitNavState {
        CockpitNavState {
            tab_idx: Tab::ALL
                .iter()
                .position(|t| *t == self.active_tab())
                .unwrap_or(0),
            selection: self.selection.clone(),
            moldable_lens: self.moldable_lens,
            inspector_reflexive: self.inspector_reflexive,
            iv_focus: self.inspector_view.doc().focus(),
            iv_present: self.inspector_view.doc().present_idx(),
            inspect_act_focus: self.inspect_act_focus,
            service_explorer_focus: self.service_explorer_focus,
            sim_target_idx: self.sim_target_idx,
            sim_effect_idx: self.sim_effect_idx,
            lane_idx: self.lane_idx,
            web_viewer: self.web_cells_viewer_rights.clone(),
            web_opened: self.web_cells_opened,
            links_focus: self.links_here_focus,
            links_depth: self.links_here_depth,
            links_viewer: self.links_here_viewer_rights.clone(),
            powerbox_confer: self.powerbox_confer_rights.clone(),
            share_wide: self.share_preview_wide,
            replay_cursor: self.replay_cursor,
            time_cursor: self.time_cursor,
        }
    }

    /// Restore a captured navigation state (re-commits the witnessed view cells
    /// so the rendered tab/focus/lens match; the nonce drift is invisible).
    pub fn restore_nav(&mut self, s: &CockpitNavState, cx: &mut Context<Self>) {
        self.selection = s.selection.clone();
        self.moldable_lens = s.moldable_lens;
        self.inspector_reflexive = s.inspector_reflexive;
        self.inspect_act_focus = s.inspect_act_focus;
        self.service_explorer_focus = s.service_explorer_focus;
        self.sim_target_idx = s.sim_target_idx;
        self.sim_effect_idx = s.sim_effect_idx;
        self.lane_idx = s.lane_idx;
        self.web_cells_viewer_rights = s.web_viewer.clone();
        self.web_cells_opened = s.web_opened;
        self.links_here_focus = s.links_focus;
        self.links_here_depth = s.links_depth;
        self.links_here_viewer_rights = s.links_viewer.clone();
        self.powerbox_confer_rights = s.powerbox_confer.clone();
        self.share_preview_wide = s.share_wide;
        self.replay_cursor = s.replay_cursor;
        self.time_cursor = s.time_cursor;
        let dbg = std::env::var_os("ATLAS_UI_DEBUG").is_some();
        if dbg {
            eprintln!("    RN: inspector_view.commit");
        }
        self.inspector_view.doc_mut().set_focus(s.iv_focus);
        self.inspector_view.doc_mut().set_present_idx(s.iv_present);
        let _ = self.inspector_view.commit(&mut self.world.borrow_mut());
        if dbg {
            eprintln!("    RN: set_tab {}", Tab::ALL[s.tab_idx].label());
        }
        self.set_tab(Tab::ALL[s.tab_idx], cx);
        if dbg {
            eprintln!("    RN: done");
        }
    }

    /// A compact, dedup-able key for the current UI state — the tab plus the
    /// sub-coordinates that tab actually renders.
    pub fn nav_key(&self) -> String {
        let tab = self.active_tab();
        let sh = |o: Option<CellId>| {
            o.map(|c| reflect::short_hex(c.as_bytes()))
                .unwrap_or_else(|| "-".into())
        };
        let sub = match tab {
            Tab::Moldable => format!(
                "focus={};lens={};refl={};face={}",
                sh(self.inspector_view.doc().focus()),
                self.moldable_lens.label(),
                self.inspector_reflexive,
                self.inspector_view.doc().present_idx()
            ),
            Tab::InspectAct => format!("focus={}", sh(self.inspect_act_focus)),
            Tab::ServiceExplorer => format!("focus={}", sh(self.service_explorer_focus)),
            Tab::Simulate => format!("tgt={};eff={}", self.sim_target_idx, self.sim_effect_idx),
            Tab::Lanes => format!("lane={}", self.lane_idx),
            Tab::WebOfCells => format!(
                "viewer={:?};open={}",
                self.web_cells_viewer_rights,
                sh(self.web_cells_opened)
            ),
            Tab::LinksHere => format!(
                "depth={};viewer={:?};focus={}",
                self.links_here_depth,
                self.links_here_viewer_rights,
                sh(self.links_here_focus)
            ),
            Tab::Powerbox => format!("confer={:?}", self.powerbox_confer_rights),
            Tab::Share => format!("wide={}", self.share_preview_wide),
            Tab::Replay => format!("cursor={}", self.replay_cursor),
            Tab::Time => format!("cursor={}", self.time_cursor),
            _ => String::new(),
        };
        format!("{}|{}", tab.label(), sub)
    }

    /// The navigation actions available from the current state. Rooted at HOME
    /// (which offers the 28 tab-spokes); inside a tab, only that tab's internal
    /// navigations (so the UI tree is a clean rooted DAG, not a mesh).
    pub fn available_nav(&self) -> Vec<(String, NavAction)> {
        let tab = self.active_tab();
        if tab == Tab::Home {
            // Skip the live-animated / perpetual-task tabs (their self-rescheduling
            // render work stalls headless stepping; they live in the UI-atlas
            // screenshots instead): Wonder (glow animation), Swarm (boots the
            // killer-demo), Agent (live activity feed).
            let skip = |t: Tab| {
                matches!(
                    t,
                    Tab::Home | Tab::Wonder | Tab::Swarm | Tab::Agent | Tab::Time
                )
            };
            return Tab::ALL
                .iter()
                .enumerate()
                .filter(|(_, t)| !skip(**t))
                .map(|(i, t)| (format!("open {}", t.label()), NavAction::Tab(i)))
                .collect();
        }
        let mut v: Vec<(String, NavAction)> = Vec::new();
        match tab {
            Tab::Moldable => {
                v.push(("cycle focus".into(), NavAction::CycleFocus));
                v.push(("cycle lens".into(), NavAction::CycleLens));
                v.push(("toggle reflexive".into(), NavAction::ToggleReflexive));
                v.push(("next face".into(), NavAction::CyclePresent));
            }
            Tab::InspectAct => v.push(("cycle focus".into(), NavAction::CycleInspectFocus)),
            Tab::ServiceExplorer => v.push(("cycle focus".into(), NavAction::CycleServiceFocus)),
            Tab::Simulate => {
                v.push(("cycle target".into(), NavAction::CycleSimTarget));
                v.push(("cycle effect".into(), NavAction::CycleSimEffect));
            }
            Tab::Lanes => {
                for i in 0..4 {
                    v.push((format!("lane {i}"), NavAction::SetLane(i)));
                }
            }
            Tab::WebOfCells => {
                v.push(("toggle viewer".into(), NavAction::ToggleWebViewer));
                v.push(("open next cell".into(), NavAction::OpenWebCell));
            }
            Tab::LinksHere => {
                v.push(("cycle depth".into(), NavAction::CycleLinksDepth));
                v.push(("toggle viewer".into(), NavAction::ToggleLinksViewer));
                v.push(("cycle focus".into(), NavAction::CycleLinksFocus));
            }
            Tab::Powerbox => v.push(("cycle confer".into(), NavAction::CyclePowerboxConfer)),
            Tab::Share => v.push(("toggle preview".into(), NavAction::ToggleSharePreview)),
            Tab::Replay => {
                v.push(("scrub +1".into(), NavAction::ReplayNext));
                v.push(("scrub -1".into(), NavAction::ReplayPrev));
            }
            Tab::Time => {
                v.push(("scrub +1".into(), NavAction::TimeNext));
                v.push(("scrub -1".into(), NavAction::TimePrev));
            }
            _ => {}
        }
        v
    }

    /// Apply a navigation action — drives the REAL interaction handlers (so the
    /// explorer exercises the genuine UI paths).
    pub fn apply_nav(&mut self, a: &NavAction, cx: &mut Context<Self>) {
        let cells = self.cells.clone();
        let cycle = |cur: Option<CellId>| -> Option<CellId> {
            if cells.is_empty() {
                return None;
            }
            let i = cur
                .and_then(|c| cells.iter().position(|x| *x == c))
                .map(|p| (p + 1) % cells.len())
                .unwrap_or(0);
            Some(cells[i])
        };
        match a {
            NavAction::Tab(i) => self.set_tab(Tab::ALL[*i], cx),
            NavAction::CycleFocus => self.moldable_cycle_focus(cx),
            NavAction::CycleLens => self.moldable_cycle_lens(cx),
            NavAction::ToggleReflexive => self.moldable_toggle_reflexive(cx),
            NavAction::CyclePresent => {
                let n = self.inspector_view.doc().present_idx();
                self.moldable_set_present_idx((n + 1) % 7, cx);
            }
            NavAction::CycleInspectFocus => {
                self.inspect_act_focus = cycle(self.inspect_act_focus);
                self.inspect_act_outcome = None;
                cx.notify();
            }
            NavAction::CycleServiceFocus => {
                self.service_explorer_focus = cycle(self.service_explorer_focus);
                self.service_explorer_selected = None;
                self.service_explorer_outcome = None;
                cx.notify();
            }
            NavAction::CycleSimTarget => self.sim_cycle_target(cx),
            NavAction::CycleSimEffect => self.sim_cycle_effect(cx),
            NavAction::SetLane(i) => {
                self.lane_idx = *i;
                self.lane_outcome = None;
                cx.notify();
            }
            NavAction::ToggleWebViewer => {
                self.web_cells_viewer_rights = match self.web_cells_viewer_rights {
                    dregg_cell::AuthRequired::None => dregg_cell::AuthRequired::Either,
                    _ => dregg_cell::AuthRequired::None,
                };
                cx.notify();
            }
            NavAction::OpenWebCell => {
                self.web_cells_opened = cycle(self.web_cells_opened);
                cx.notify();
            }
            NavAction::CycleLinksDepth => {
                self.links_here_depth = match self.links_here_depth {
                    0 | 1 => 2,
                    2 => 3,
                    _ => 1,
                };
                cx.notify();
            }
            NavAction::ToggleLinksViewer => {
                self.links_here_viewer_rights = match self.links_here_viewer_rights {
                    dregg_cell::AuthRequired::None => dregg_cell::AuthRequired::Signature,
                    _ => dregg_cell::AuthRequired::None,
                };
                cx.notify();
            }
            NavAction::CycleLinksFocus => {
                self.links_here_focus = cycle(self.links_here_focus);
                cx.notify();
            }
            NavAction::CyclePowerboxConfer => {
                self.powerbox_confer_rights = match self.powerbox_confer_rights {
                    dregg_cell::AuthRequired::Signature => dregg_cell::AuthRequired::Either,
                    dregg_cell::AuthRequired::Either => dregg_cell::AuthRequired::None,
                    _ => dregg_cell::AuthRequired::Signature,
                };
                cx.notify();
            }
            NavAction::ToggleSharePreview => {
                self.share_preview_wide = !self.share_preview_wide;
                cx.notify();
            }
            NavAction::ReplayNext => self.replay_step_forward(cx),
            NavAction::ReplayPrev => self.replay_step_back(cx),
            NavAction::TimeNext => self.time_step_forward(cx),
            NavAction::TimePrev => self.time_step_back(cx),
        }
    }

    // === NAVIGATION HISTORY (browser-style back/forward over the UI state) ===

    /// Record the current UI state into the navigation history (called once per
    /// render, after `witness_tab`). Appends only when the `nav_key` changed,
    /// truncating any forward history — exactly like a browser's back-stack.
    pub(crate) fn record_nav(&mut self) {
        if self.nav_jumping {
            return;
        }
        let key = self.nav_key();
        if self.nav_hist.is_empty() {
            self.nav_hist.push((key, self.capture_nav()));
            self.nav_cursor = 0;
            return;
        }
        if self.nav_hist[self.nav_cursor].0 != key {
            self.nav_hist.truncate(self.nav_cursor + 1);
            self.nav_hist.push((key, self.capture_nav()));
            self.nav_cursor = self.nav_hist.len() - 1;
            if self.nav_hist.len() > 128 {
                self.nav_hist.remove(0);
                self.nav_cursor = self.nav_cursor.saturating_sub(1);
            }
        }
    }

    pub(crate) fn can_nav_back(&self) -> bool {
        self.nav_cursor > 0
    }
    pub(crate) fn can_nav_forward(&self) -> bool {
        self.nav_cursor + 1 < self.nav_hist.len()
    }

    /// Step back to the previous UI state (← / ⌘[). Restores the captured nav
    /// state; the `nav_jumping` guard keeps the restore out of the history.
    pub(crate) fn nav_back(&mut self, cx: &mut Context<Self>) {
        if !self.can_nav_back() {
            return;
        }
        self.nav_cursor -= 1;
        let st = self.nav_hist[self.nav_cursor].1.clone();
        self.nav_jumping = true;
        self.restore_nav(&st, cx);
        self.nav_jumping = false;
        cx.notify();
    }

    /// Step forward to the next UI state (→ / ⌘]).
    pub(crate) fn nav_forward(&mut self, cx: &mut Context<Self>) {
        if !self.can_nav_forward() {
            return;
        }
        self.nav_cursor += 1;
        let st = self.nav_hist[self.nav_cursor].1.clone();
        self.nav_jumping = true;
        self.restore_nav(&st, cx);
        self.nav_jumping = false;
        cx.notify();
    }

    /// A compact label for a nav_key (the tab plus its first sub-coordinate) —
    /// used on the pinned-view chips.
    pub(crate) fn nav_short_label(key: &str) -> String {
        let (tab, sub) = key.split_once('|').unwrap_or((key, ""));
        let first = sub.split(';').next().unwrap_or("");
        if first.is_empty() {
            tab.to_string()
        } else {
            format!("{tab}/{}", first.split('=').next_back().unwrap_or(first))
        }
    }

    /// Pin (bookmark) the current view, or unpin it if already pinned (the ☆
    /// toggle). Session-scoped, capped.
    pub(crate) fn pin_current(&mut self, cx: &mut Context<Self>) {
        let key = self.nav_key();
        if self.nav_pins.iter().any(|p| p.0 == key) {
            self.nav_pins.retain(|p| p.0 != key);
        } else {
            let cap = self.capture_nav();
            self.nav_pins.push((key, cap));
            if self.nav_pins.len() > 12 {
                self.nav_pins.remove(0);
            }
        }
        cx.notify();
    }

    // === MACRO RECORD / REPLAY (⏺▶) ========================================
    // A macro = a recorded replayable turn-sequence (a `Script` over the proven
    // Pipeline carrier). ⏺ snapshots the world; you act (committing real turns);
    // ⏹ captures the turns since as a Script; ▶ replays it on a FORK of the start
    // state — a verified preview, the live world untouched.

    /// ⏺ — begin recording: snapshot the world + mark the history cursor.
    pub(crate) fn macro_record(&mut self, cx: &mut Context<Self>) {
        let w = self.world.borrow();
        self.macro_recording = Some((w.recorded_turns().len(), w.fork()));
        drop(w);
        self.macro_outcome = Some("● recording — act, then ⏹ to capture the turn-sequence".into());
        cx.notify();
    }

    /// ⏹ — stop + capture the committed turns since ⏺ as a `Script`.
    pub(crate) fn macro_stop(&mut self, cx: &mut Context<Self>) {
        if let Some((start, start_fork)) = self.macro_recording.take() {
            let turns: Vec<_> = {
                let w = self.world.borrow();
                w.recorded_turns().steps()[start.min(w.recorded_turns().len())..]
                    .iter()
                    .filter_map(|s| match s {
                        starbridge_v2::replay::RecordedStep::Committed { turn, .. } => {
                            Some(turn.clone())
                        }
                        _ => None,
                    })
                    .collect()
            };
            let script = dregg_turn::script::Script::record("cockpit-macro", turns);
            let id = reflect::short_hex(&script.id());
            self.macro_outcome = Some(if script.is_empty() {
                "⏹ nothing recorded (no turns committed while recording)".into()
            } else {
                format!(
                    "⏹ captured {} turns as script {} — ▶ to replay",
                    script.len(),
                    id
                )
            });
            self.last_macro = Some((script, start_fork));
            cx.notify();
        }
    }

    /// ▶ — replay the last macro on a FORK of its start state (live world untouched).
    pub(crate) fn macro_replay(&mut self, cx: &mut Context<Self>) {
        if let Some((script, start_fork)) = &self.last_macro {
            let mut w = start_fork.fork();
            let (mut committed, mut refused) = (0u32, 0u32);
            for t in &script.pipeline.turns {
                match w.commit_turn(t.clone()) {
                    CommitOutcome::Committed { .. } => committed += 1,
                    _ => refused += 1,
                }
            }
            self.macro_outcome = Some(format!(
                "▶ replayed script {} on a fork: {committed} committed, {refused} refused (live world untouched)",
                reflect::short_hex(&script.id())
            ));
        } else {
            self.macro_outcome = Some("no macro recorded yet — ⏺ to start".into());
        }
        cx.notify();
    }

    /// THE NAVIGATION BAR — browser-style back/forward + a "you are here"
    /// breadcrumb + a ☆ pin + a live "what can I do here" quick-nav strip + the
    /// pinned views. The programmatic nav API, surfaced as delight.
    pub(crate) fn nav_bar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let back_color = if self.can_nav_back() {
            theme::accent()
        } else {
            theme::muted()
        };
        let fwd_color = if self.can_nav_forward() {
            theme::accent()
        } else {
            theme::muted()
        };
        // the current location as a legible breadcrumb (tab · sub-coords)
        let here = self.nav_key();
        let (tab, sub) = here.split_once('|').unwrap_or((here.as_str(), ""));
        let crumb = if sub.is_empty() {
            tab.to_string()
        } else {
            format!("{tab} · {}", sub.replace(';', " · "))
        };
        // the within-surface navigations available right now, as one-click chips
        let actions = self.available_nav();
        let show_chips = self.active_tab() != Tab::Home && !actions.is_empty();
        let is_pinned = self.nav_pins.iter().any(|p| p.0 == here);
        let pin_glyph = if is_pinned { "★" } else { "☆" };
        let pin_color = if is_pinned {
            theme::accent()
        } else {
            theme::muted()
        };

        let mut bar = div()
            .flex()
            .items_center()
            .gap_1()
            .px_2()
            .py_1()
            .border_b_1()
            .border_color(theme::border())
            .bg(theme::panel())
            .child(small_button(
                cx,
                "nav-back",
                "←",
                back_color,
                Cockpit::nav_back,
            ))
            .child(small_button(
                cx,
                "nav-fwd",
                "→",
                fwd_color,
                Cockpit::nav_forward,
            ))
            .child(small_button(
                cx,
                "nav-pin",
                pin_glyph,
                pin_color,
                Cockpit::pin_current,
            ))
            // MACRO record/replay (⏺▶) — record a turn-sequence as a Script, replay on a fork.
            .child(small_button(
                cx,
                "macro-rec",
                if self.macro_recording.is_some() {
                    "●rec"
                } else {
                    "⏺"
                },
                if self.macro_recording.is_some() {
                    theme::bad()
                } else {
                    theme::muted()
                },
                Cockpit::macro_record,
            ))
            .child(small_button(
                cx,
                "macro-stop",
                "⏹",
                theme::muted(),
                Cockpit::macro_stop,
            ))
            .child(small_button(
                cx,
                "macro-play",
                "▶",
                if self.last_macro.is_some() {
                    theme::accent()
                } else {
                    theme::muted()
                },
                Cockpit::macro_replay,
            ))
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .px_2()
                    .child(format!("⌖ {crumb}")),
            );

        if let Some(o) = &self.macro_outcome {
            bar = bar.child(
                div()
                    .text_xs()
                    .text_color(theme::accent())
                    .px_2()
                    .child(o.clone()),
            );
        }

        if show_chips {
            let mut strip = div().flex().items_center().gap_1().flex_1();
            strip = strip.child(div().text_xs().text_color(theme::muted()).child("·"));
            for (i, (label, action)) in actions.into_iter().enumerate() {
                let act = action;
                strip = strip.child(
                    div()
                        .id(("nav-here", i))
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel_hi())
                        .border_1()
                        .border_color(theme::border())
                        .text_xs()
                        .text_color(theme::text())
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::border()))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev, _w, cx| {
                                this.apply_nav(&act, cx);
                                cx.notify();
                            }),
                        )
                        .child(label),
                );
            }
            bar = bar.child(strip);
        }

        // PINNED VIEWS — one-click jump-back bookmarks (right-aligned).
        if !self.nav_pins.is_empty() {
            let mut pins = div().flex().items_center().gap_1().ml_auto();
            pins = pins.child(div().text_xs().text_color(theme::muted()).child("★"));
            for (i, (key, _)) in self.nav_pins.iter().enumerate() {
                let st = self.nav_pins[i].1.clone();
                pins = pins.child(
                    div()
                        .id(("nav-pin-chip", i))
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel_hi())
                        .border_1()
                        .border_color(theme::border())
                        .text_xs()
                        .text_color(theme::accent())
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::border()))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev, _w, cx| {
                                this.restore_nav(&st, cx);
                                cx.notify();
                            }),
                        )
                        .child(Self::nav_short_label(key)),
                );
            }
            bar = bar.child(pins);
        }
        bar
    }
}
