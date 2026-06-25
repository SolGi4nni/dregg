//! The ⏳ TEMPORAL COCKPIT (the TIME tab): rewind scrubber, the M5 suspend gate, the MetaStack navigator + its render.

use super::*;

// ===========================================================================
// ⏳ THE TEMPORAL COCKPIT — the headline livability surface (the "⏳ TIME" tab):
// time-travel + suspend + fractal meta-debug as ONE clickable control panel.
//
// This block holds the TIME tab's verbs (the rewind scrubber, the M5 suspend
// gate, the MetaStack navigator) + its render, all over the REAL models
// (`time_travel::TimeCockpitModel` over `World::recorded_turns` / the suspend gate /
// `meta_debug::MetaStack`). Appended as its own `impl Cockpit` so it stays out of
// the way of the densely-co-edited Tab/dispatch/state regions above.
// ===========================================================================
impl Cockpit {
    /// The head step of the live history (the live present — where `Liveness::Live`).
    pub(crate) fn time_head(&self) -> usize {
        self.world.borrow().recorded_turns().len()
    }

    /// Drag the REWIND SCRUBBER to history step `k` (clamped to the head). The TIME
    /// tab re-derives the focused views at that point (root-verified replay); the
    /// image rewinds, the `Liveness` badge flips to `ReplayedDeterministic`.
    pub(crate) fn time_scrub_to(&mut self, k: usize, cx: &mut Context<Self>) {
        self.time_cursor = k.min(self.time_head());
        cx.notify();
    }

    /// Rewind the scrubber one turn (one history step back).
    pub(crate) fn time_step_back(&mut self, cx: &mut Context<Self>) {
        self.time_cursor = self.time_cursor.saturating_sub(1);
        cx.notify();
    }

    /// Advance the scrubber one turn (toward the live head).
    pub(crate) fn time_step_forward(&mut self, cx: &mut Context<Self>) {
        self.time_cursor = (self.time_cursor + 1).min(self.time_head());
        cx.notify();
    }

    /// Jump the scrubber to genesis (the empty pre-history image).
    pub(crate) fn time_to_genesis(&mut self, cx: &mut Context<Self>) {
        self.time_cursor = 0;
        cx.notify();
    }

    /// Jump the scrubber back to the live head (the present — `Liveness::Live`).
    pub(crate) fn time_to_head(&mut self, cx: &mut Context<Self>) {
        self.time_cursor = self.time_head();
        cx.notify();
    }

    /// ⏸ SUSPEND — halt the live loop via the M5 gate ([`World::suspend`]). The head
    /// FREEZES; a turn submitted while suspended STAGES in the pending queue (the
    /// continuation) instead of committing. Distinct from the scrubber being in the
    /// past: this stops the REAL loop.
    pub(crate) fn time_suspend(&mut self, cx: &mut Context<Self>) {
        self.world.borrow_mut().suspend();
        cx.notify();
    }

    /// ▶ RESUME (drain) — drain the staged continuation through the executor gate
    /// ([`ResumeMode::Drain`]): the queued turns commit in arrival order and the
    /// loop runs again. The scrubber follows the head forward; the tower grounds.
    pub(crate) fn time_resume(&mut self, cx: &mut Context<Self>) {
        let outcomes = self.world.borrow_mut().resume(ResumeMode::Drain);
        let committed = outcomes.iter().filter(|o| o.is_committed()).count();
        self.time_cursor = self.time_head();
        self.last_outcome = Some(format!(
            "▶ resumed · {committed} staged turn(s) drained through the gate"
        ));
        self.meta_stack = MetaStack::new();
        cx.notify();
    }

    /// STAGE a demo continuation turn while suspended — a small transfer the operator
    /// can watch QUEUE (it does not commit; the head stays frozen). Proves the
    /// suspend gate live: the pending queue grows, the image is untouched.
    pub(crate) fn time_stage_demo_turn(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, user] = self.anchors;
        let turn = {
            let w = self.world.borrow();
            w.turn(treasury, vec![world::transfer(treasury, user, 1)])
        };
        let outcome = self.world.borrow_mut().commit_turn(turn);
        self.last_outcome = Some(match outcome {
            CommitOutcome::Queued { .. } => {
                "⏸ staged · a turn QUEUED into the frozen continuation".to_string()
            }
            CommitOutcome::Committed { receipt, .. } => {
                self.time_cursor = self.time_head();
                format!(
                    "committed (not suspended) · {}",
                    reflect::short_hex(&receipt.receipt_hash())
                )
            }
            CommitOutcome::Rejected { reason, .. } => format!("refused · {reason}"),
        });
        cx.notify();
    }

    /// SUSPEND & INSPECT — push a meta-level onto the [`MetaStack`] (the fractal
    /// meta-debug). The first push suspends the loop (if not already) + materializes
    /// `BASE`; each subsequent push climbs one level — "debug the debugger". The new
    /// level captures the frozen head as an inspectable object.
    pub(crate) fn time_metastack_push(&mut self, cx: &mut Context<Self>) {
        {
            let mut w = self.world.borrow_mut();
            if !w.is_suspended() {
                w.suspend();
            }
        }
        let focus = {
            let w = self.world.borrow();
            self.meta_stack.push(&w)
        };
        self.last_outcome = Some(format!(
            "⊕ pushed meta-level · debugging {focus:?} (the tower climbed)"
        ));
        cx.notify();
    }

    /// DESCEND — pop the innermost meta-level (close the inner debugger). The floor
    /// (the gpui loop) stops the pop: you cannot descend below the base.
    pub(crate) fn time_metastack_pop(&mut self, cx: &mut Context<Self>) {
        match self.meta_stack.pop() {
            Some(view) => {
                self.last_outcome = Some(format!(
                    "⊖ popped meta-level {} (descended)",
                    view.level.depth()
                ));
            }
            None => {
                self.last_outcome =
                    Some("(at the floor — the gpui loop is not a level to pop)".to_string());
            }
        }
        cx.notify();
    }

    /// THE ⏳ TIME PANEL — the temporal cockpit, painted from the pure
    /// [`TimeCockpitModel`] (built fresh from the live world + the scrubber cursor +
    /// the MetaStack). Three clickable powers stacked: (1) the REWIND SCRUBBER with
    /// the live `Liveness` badge + the verified reconstruction at the cursor; (2) the
    /// ⏸ SUSPEND / ▶ RESUME gate + the staged continuation; (3) the METASTACK
    /// breadcrumb navigator (push to climb / pop to descend — debug the debugger).
    pub(crate) fn time_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let model = {
            let w = self.world.borrow();
            TimeCockpitModel::build(&w, self.time_cursor, &self.meta_stack)
        };

        let mut col = div()
            .id("cockpit-scroll-body-23")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title(
            "⏳ TEMPORAL COCKPIT · time-travel · suspend · fractal meta-debug",
        ));

        // --- the LIVENESS badge — am I at the live present, or a re-derived past? --
        let (badge_color, badge_bg) = match model.liveness {
            Liveness::Live => (theme::good(), theme::panel()),
            Liveness::ReplayedDeterministic => (theme::warn(), theme::panel_hi()),
            Liveness::ReconstructedApproximate => (theme::bad(), theme::panel_hi()),
        };
        col = col.child(
            div()
                .flex()
                .items_center()
                .gap_2()
                .p_2()
                .rounded_md()
                .border_1()
                .border_color(badge_color)
                .bg(badge_bg)
                .child(
                    div()
                        .text_sm()
                        .text_color(badge_color)
                        .child(model.liveness_badge()),
                )
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(format!("k{} / head k{}", model.cursor, model.head)),
                )
                .child(if model.cursor_verified {
                    pill(
                        format!("✓ root {}", short_root(&model.cursor_root)),
                        theme::good(),
                    )
                } else {
                    pill("✗ root UNVERIFIED".to_string(), theme::bad())
                })
                .child(if model.cursor_via_umem {
                    pill("⟲ umem boundary".to_string(), theme::accent())
                } else {
                    pill("↺ genesis replay".to_string(), theme::muted())
                }),
        );

        // ====================================================================
        // (2) THE ⏸ SUSPEND GATE — halt the real loop; the staged continuation.
        // ====================================================================
        col = col.child(section_title("⏸ SUSPEND GATE · halt the live loop (M5)").mt_1());
        if model.suspended {
            // SUSPENDED banner — the head is FROZEN.
            col = col.child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .p_2()
                    .rounded_md()
                    .border_1()
                    .border_color(theme::warn())
                    .bg(theme::panel_hi())
                    .child(
                        div()
                            .text_sm()
                            .text_color(theme::warn())
                            .child("⏸ SUSPENDED"),
                    )
                    .child(div().text_xs().text_color(theme::muted()).child(format!(
                        "head FROZEN @h{} · the loop is halted",
                        model.live_height
                    ))),
            );
            col = col.child(
                div()
                    .flex()
                    .flex_wrap()
                    .gap_1()
                    .child(time_button(
                        cx,
                        "time-resume",
                        "▶ RESUME (drain)",
                        theme::good(),
                        Cockpit::time_resume,
                    ))
                    .child(time_button(
                        cx,
                        "time-stage",
                        "⊕ stage a turn",
                        theme::accent(),
                        Cockpit::time_stage_demo_turn,
                    )),
            );
            // The staged continuation (the pending queue) — the real partial turn.
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .mt_1()
                    .child(format!(
                        "STAGED CONTINUATION · {} pending turn(s)",
                        model.pending.len()
                    )),
            );
            if model.pending.is_empty() {
                col = col.child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .px_2()
                        .child("(empty — stage a turn to fill the continuation)"),
                );
            }
            for line in &model.pending {
                col = col.child(
                    div()
                        .text_xs()
                        .text_color(theme::accent())
                        .px_2()
                        .child(format!("· {line}")),
                );
            }
        } else {
            // RUNNING — the loop is live; offer the suspend button.
            col = col.child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::good())
                            .child(format!("● running @h{}", model.live_height)),
                    )
                    .child(time_button(
                        cx,
                        "time-suspend",
                        "⏸ SUSPEND",
                        theme::warn(),
                        Cockpit::time_suspend,
                    )),
            );
        }

        // ====================================================================
        // (1) THE REWIND SCRUBBER — drag over the verified witness history.
        // ====================================================================
        col = col.child(section_title("⟲ REWIND SCRUBBER · the verified witness history").mt_2());
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(time_button(
                    cx,
                    "time-genesis",
                    "⏮ genesis",
                    theme::muted(),
                    Cockpit::time_to_genesis,
                ))
                .child(time_button(
                    cx,
                    "time-back",
                    "◀ −1 turn",
                    theme::accent(),
                    Cockpit::time_step_back,
                ))
                .child(time_button(
                    cx,
                    "time-fwd",
                    "+1 turn ▶",
                    theme::accent(),
                    Cockpit::time_step_forward,
                ))
                .child(time_button(
                    cx,
                    "time-head",
                    "live head ⏭",
                    theme::good(),
                    Cockpit::time_to_head,
                )),
        );
        // THE UN-TURN FRONTIER — where the rewind can reach, in reversibility terms
        // (the reversibility organ classifies each step; the floor is the latest
        // committed boundary). The headline livability readout above the scrubber.
        {
            let floor = model.undo_floor();
            col = col.child(
                div()
                    .text_xs()
                    .mt_1()
                    .text_color(if floor == 0 {
                        theme::good()
                    } else {
                        theme::warn()
                    })
                    .child(model.undo_floor_badge()),
            );
        }
        // The ticks — every landing (genesis → head). Each is CLICKABLE: drag the
        // scrubber to that step. The cursor tick glows; turns vs genesis are distinct;
        // a ⊘ tick is a committed boundary the rewind cannot un-turn past.
        let mut ticks = div().flex().flex_col().gap_0p5().mt_1();
        for tick in &model.ticks {
            let at_cursor = tick.step == model.cursor;
            let is_head = tick.step == model.head;
            let step = tick.step;
            // The marker carries the reversibility verdict: ⊘ = a committed boundary
            // the rewind cannot un-turn past; • = a reversible turn; · = genesis/empty.
            let marker = if at_cursor {
                "▸"
            } else if tick.reversible == Some(false) {
                "⊘"
            } else if tick.is_turn {
                "•"
            } else {
                "·"
            };
            let rev_note = match tick.reversible {
                Some(true) => "  ↺ reversible",
                Some(false) => "  ⊘ committed (no un-turn past here)",
                None => "",
            };
            let label_color = if at_cursor {
                theme::accent()
            } else if tick.reversible == Some(false) {
                theme::warn()
            } else if tick.is_turn {
                theme::text()
            } else {
                theme::muted()
            };
            ticks = ticks.child(
                div()
                    .id(SharedString::from(format!("time-tick-{step}")))
                    .flex()
                    .justify_between()
                    .items_center()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if at_cursor {
                        theme::panel_hi()
                    } else {
                        theme::panel()
                    })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.time_scrub_to(step, cx);
                        }),
                    )
                    .child(div().text_xs().text_color(label_color).child(format!(
                        "{marker} k{step}  {}{}{}",
                        tick.label,
                        rev_note,
                        if is_head { "  ⟵ head (live)" } else { "" }
                    )))
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(short_root(&tick.root)),
                    ),
            );
        }
        col = col.child(ticks);

        // The VERIFIED reconstruction at the cursor — the image, rewound. Re-derived
        // by root-verified replay (`time_travel` → `History::replay_to`).
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mt_1()
                .child(format!(
                    "IMAGE @k{} ({} cells, verified replay)",
                    model.cursor,
                    model.cursor_cells.len()
                )),
        );
        if model.cursor_cells.is_empty() && !model.cursor_verified {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::bad())
                    .px_2()
                    .child("(replay refused — the witnessed log does not support this point)"),
            );
        }
        for (id, bal, caps) in &model.cursor_cells {
            col = col.child(
                div()
                    .flex()
                    .justify_between()
                    .px_2()
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::text())
                            .child(format!("⬡ {}", reflect::short_hex(id.as_bytes()))),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(if *bal < 0 {
                                theme::warn()
                            } else {
                                theme::text()
                            })
                            .child(format!("{bal} · {caps} caps")),
                    ),
            );
        }
        // The diff from the previous step — what the cursor's turn DID (the receipt).
        if let Some(diff) = &model.diff_from_prev {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .mt_1()
                    .child(format!(
                        "Δ this turn (k{}→k{}) · {} cell(s) changed",
                        model.cursor.saturating_sub(1),
                        model.cursor,
                        diff.len()
                    )),
            );
            for (id, change) in &diff.changes {
                col = col.child(
                    div()
                        .text_xs()
                        .text_color(theme::accent())
                        .px_2()
                        .child(format!(
                            "{} {}",
                            reflect::short_hex(id.as_bytes()),
                            change.label()
                        )),
                );
            }
        }

        // ====================================================================
        // (3) THE METASTACK NAVIGATOR — the fractal meta-debug tower.
        // ====================================================================
        col = col
            .child(section_title("⊞ METASTACK · debug the debugger (the reflective tower)").mt_2());
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(time_button(
                    cx,
                    "meta-push",
                    "⊕ suspend & inspect (climb)",
                    theme::accent(),
                    Cockpit::time_metastack_push,
                ))
                .child(time_button(
                    cx,
                    "meta-pop",
                    "⊖ descend (pop)",
                    theme::muted(),
                    Cockpit::time_metastack_pop,
                )),
        );
        // The breadcrumb: BASE → meta¹ → meta² … (the top is the current debugger).
        let mut crumbs = div().flex().flex_wrap().items_center().gap_1().mt_1();
        crumbs = crumbs.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .child("BASE (the live image)"),
        );
        if model.metastack.is_empty() {
            crumbs = crumbs.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("— un-reflected (push to suspend & climb)"),
            );
        }
        for crumb in &model.metastack {
            let color = if crumb.is_top {
                theme::accent()
            } else {
                theme::text()
            };
            crumbs = crumbs.child(div().text_xs().text_color(theme::muted()).child("→"));
            crumbs = crumbs.child(
                div()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if crumb.is_top {
                        theme::panel_hi()
                    } else {
                        theme::panel()
                    })
                    .border_1()
                    .border_color(if crumb.is_top {
                        theme::accent()
                    } else {
                        theme::border()
                    })
                    .text_xs()
                    .text_color(color)
                    .child(format!(
                        "meta{} · frozen@h{}{}",
                        crumb.level,
                        crumb.frozen_height,
                        if crumb.is_top { " ◀ debugging" } else { "" }
                    )),
            );
        }
        col = col.child(crumbs);

        // The action banner (the last suspend/resume/stage/meta verdict).
        if let Some(msg) = &self.last_outcome {
            col = col.child(
                div()
                    .mt_2()
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
}

/// A ⏳ TIME-tab action button — an explicit-id clickable verb (so two buttons
/// that share a label don't collide), driving a `&mut Cockpit` verb. Mirrors
/// `small_button`, kept local to the temporal cockpit block.
fn time_button(
    cx: &mut Context<Cockpit>,
    id: &'static str,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    div()
        .id(id)
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_xs()
        .text_color(color)
        .cursor_pointer()
        .hover(|s| s.bg(theme::border()))
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev, _window, cx| {
                handler(this, cx);
            }),
        )
        .child(label.to_string())
}

/// First 6 bytes of a 32-byte canonical root, hex — the scrubber-tick root tooth.
fn short_root(root: &[u8; 32]) -> String {
    reflect::short_hex(root)
}
