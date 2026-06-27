//! Core panels: rail header/cell world, inspector, blocklace, composer, the SIMULATE panel + presentation-body rendering.

use super::*;

impl Cockpit {
    /// The old left-rail header (identity + image root + the live-node strip).
    /// SUPERSEDED by the coherent frame's TOP BAR ([`Self::top_bar`]), which now
    /// carries the identity + cap-badge + ledger clock; the live-node strip moved
    /// to the left context rail (see [`Self::live_node_strip`]). Kept as the
    /// styling reference (like [`Self::tab_bar`]).
    #[allow(dead_code)]
    pub(crate) fn rail_header(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let root = reflect::short_hex(&w.state_root());
        div()
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .border_b_1()
            .border_color(theme::border())
            .child(
                div()
                    .text_lg()
                    .text_color(theme::text())
                    .child("Starbridge v2"),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("the live, verified, ocap image"),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::accent())
                    .child("⌘K · command palette (every action)"),
            )
            .child(
                div()
                    .flex()
                    .gap_2()
                    .mt_2()
                    .child(pill("embedded executor", theme::good()))
                    .child(pill(format!("h{}", w.height()), theme::accent())),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(format!("image root: {root}")),
            )
            .child(div().text_xs().text_color(theme::muted()).child(format!(
                "{} cells · {} receipts",
                w.cell_count(),
                w.receipts().len()
            )))
            .children(self.live_node_strip())
    }

    /// The LIVE NODE strip in the rail header (only when `--node <url>` connected):
    /// the remote node's liveness/producer/height + the LIVE receipt feed head
    /// (the SSE stream filling per receipt) + the resume cursor. This is the
    /// distribution axis's REMOTE half — the master interface watching a running
    /// federation alongside its own embedded image.
    pub(crate) fn live_node_strip(&self) -> Option<gpui::AnyElement> {
        let ln = self.live_node.as_ref()?;
        let mut strip = div()
            .flex()
            .flex_col()
            .gap_1()
            .mt_2()
            .pt_2()
            .border_t_1()
            .border_color(theme::border())
            .child(section_title("LIVE NODE · remote federation"));
        // The connection target + (from the last snapshot) the producer/liveness.
        let desc = ln.client().describe();
        strip = strip.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(desc, theme::accent()))
                .children(self.live_snapshot.as_ref().map(|s| {
                    pill(
                        format!(
                            "{} · producer {}",
                            if s.status.healthy { "healthy" } else { "DOWN" },
                            s.status.state_producer
                        ),
                        if s.status.healthy {
                            theme::good()
                        } else {
                            theme::warn()
                        },
                    )
                }))
                .children(
                    self.live_snapshot
                        .as_ref()
                        .map(|s| pill(format!("h{}", s.status.latest_height), theme::accent())),
                ),
        );
        // The LIVE receipt feed: head index + count + resume cursor (the SSE drain).
        let feed = &self.live_feed;
        let head = feed
            .latest()
            .map(|e| format!("#{} · {}", e.chain_index, e.finality))
            .unwrap_or_else(|| "(awaiting first receipt)".to_string());
        strip = strip.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(
                    format!("{} streamed", feed.receipts().len()),
                    theme::good(),
                ))
                .child(pill(format!("head {head}"), theme::accent()))
                .children(
                    feed.resume_cursor()
                        .map(|c| pill(format!("cursor {c}"), theme::muted())),
                ),
        );
        strip = strip.child(div().text_xs().text_color(theme::muted()).child(
            "the SSE receipt stream (/api/events/stream) advances this PER RECEIPT \
             (cx.notify), not on reload — the live receipt nervous system",
        ));
        Some(strip.into_any_element())
    }

    pub(crate) fn cell_world(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1().p_2();
        col = col.child(section_title("CELL WORLD · ocap").mb_1());
        // The image object itself, selectable.
        col = col.child(self.image_row(cx));
        for id in &self.cells {
            if let Some(cell) = w.ledger().get(id) {
                col = col.child(self.cell_row(*id, cell, cx));
            }
        }
        col
    }

    pub(crate) fn image_row(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let selected = matches!(self.selection, Selection::Image);
        div()
            .id("image-row")
            .flex()
            .justify_between()
            .px_2()
            .py_1()
            .rounded_md()
            .bg(if selected {
                theme::panel_hi()
            } else {
                theme::panel()
            })
            .cursor_pointer()
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(|this, _ev, _w, cx| {
                    this.selection = Selection::Image;
                    cx.notify();
                }),
            )
            .child(div().text_color(theme::accent()).child("◆ this image"))
    }

    pub(crate) fn cell_row(
        &self,
        id: CellId,
        cell: &dregg_cell::Cell,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        let selected = matches!(self.selection, Selection::Cell(s) if s == id);
        let bal = cell.state.balance();
        let caps = cell.capabilities.len();
        let bal_color = if bal < 0 {
            theme::warn()
        } else {
            theme::text()
        };
        div()
            .id(SharedString::from(format!(
                "cell-{}",
                reflect::short_hex(id.as_bytes())
            )))
            .flex()
            .flex_col()
            .gap_0p5()
            .px_2()
            .py_1()
            .rounded_md()
            .bg(if selected {
                theme::panel_hi()
            } else {
                theme::panel()
            })
            .cursor_pointer()
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev, _w, cx| {
                    this.selection = Selection::Cell(id);
                    cx.notify();
                }),
            )
            .child(
                div()
                    .flex()
                    .justify_between()
                    .child(
                        div()
                            .text_color(theme::text())
                            .child(format!("⬡ {}", reflect::short_hex(id.as_bytes()))),
                    )
                    .child(div().text_color(bal_color).child(format!("{bal}"))),
            )
            .child(
                div()
                    .flex()
                    .gap_2()
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(format!("{caps} caps")),
                    )
                    .when(cell.delegate.is_some(), |d| {
                        d.child(div().text_xs().text_color(theme::muted()).child("delegate"))
                    })
                    .when(
                        !matches!(cell.program, dregg_cell::CellProgram::None),
                        |d| d.child(div().text_xs().text_color(theme::accent()).child("program")),
                    ),
            )
    }

    pub(crate) fn inspector(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let obj: Option<Inspectable> = match &self.selection {
            Selection::Image => Some(reflect::reflect_image(&w)),
            Selection::Cell(id) => w.ledger().get(id).map(|c| reflect::reflect_cell(id, c)),
            Selection::Receipt(i) => w.receipts().get(*i).map(reflect::reflect_receipt),
        };
        let mut panel = div().flex().flex_col().gap_1().p_3().size_full();
        panel = panel.child(section_title("INSPECTOR · reflective").mb_1());
        match obj {
            Some(obj) => {
                panel = panel.child(div().text_color(theme::text()).child(obj.title.clone()));
                panel = panel.child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .mb_2()
                        .child(obj.subtitle.clone()),
                );
                panel = panel.child(kind_badge(obj.kind));
                for f in &obj.fields {
                    panel = panel.child(field_row(f));
                }
            }
            None => {
                panel = panel.child(div().text_color(theme::muted()).child("(nothing selected)"));
            }
        }
        panel
    }

    pub(crate) fn blocklace(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1().p_2();
        col = col.child(section_title("BLOCKLACE · provenance").mb_1());
        let total = w.receipts().len();
        if total == 0 {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("(no receipts yet — run a verb)"),
            );
        }
        // CAP the rendered rows: the receipt tape is unbounded (every receipt ever),
        // and `blocklace` rebuilds raw every frame, so rendering the whole tape is
        // `O(receipts)` `format!`-heavy work per paint. Show only the most-recent
        // `BLOCKLACE_CAP` rows (true indices preserved via `enumerate().rev().take`),
        // with an "older" footer when truncated — bounding paint cost regardless of
        // history depth. (A scroll-virtualized list is the fuller answer; this is the
        // cheap, correct bound.)
        const BLOCKLACE_CAP: usize = 200;
        if total > BLOCKLACE_CAP {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(format!("(+{} older receipts)", total - BLOCKLACE_CAP)),
            );
        }
        // Most-recent first, capped.
        for (i, r) in w.receipts().iter().enumerate().rev().take(BLOCKLACE_CAP) {
            let selected = matches!(self.selection, Selection::Receipt(s) if s == i);
            let hash = reflect::short_hex(&r.receipt_hash());
            col = col.child(
                div()
                    .id(SharedString::from(format!("rcpt-{i}")))
                    .flex()
                    .justify_between()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if selected {
                        theme::panel_hi()
                    } else {
                        theme::panel()
                    })
                    .cursor_pointer()
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.selection = Selection::Receipt(i);
                            cx.notify();
                        }),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::accent())
                            .child(format!("●─ {hash}")),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(format!("{} eff", r.action_count)),
                    ),
            );
        }
        col
    }

    pub(crate) fn composer(&self, cx: &mut Context<Self>) -> impl IntoElement {
        div()
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .child(section_title("COMPOSER · drive the executor"))
            .child(div().text_xs().text_color(theme::muted()).child(
                "Each verb composes a turn and runs it through the EMBEDDED VERIFIED executor. \
                 Watch the image, receipts, and dynamics update live.",
            ))
            .child(verb_button(
                cx,
                "transfer 1,000 → user",
                theme::good(),
                Cockpit::run_demo_transfer,
            ))
            .child(verb_button(
                cx,
                "compose multi-action (pay service + user)",
                theme::good(),
                Cockpit::run_compose_multi,
            ))
            .child(verb_button(
                cx,
                "grant capability (service→user)",
                theme::accent(),
                Cockpit::run_demo_grant,
            ))
            .child(verb_button(
                cx,
                "create cell (conserves value)",
                theme::accent(),
                Cockpit::run_demo_create,
            ))
            .child(verb_button(
                cx,
                "seal a fresh cell (lifecycle)",
                theme::accent(),
                Cockpit::run_seal,
            ))
            .child(verb_button(
                cx,
                "burn 1,000 (supply reduced)",
                theme::warn(),
                Cockpit::run_burn,
            ))
            .child(verb_button(
                cx,
                "⚠ over-grant (watch it REJECT)",
                theme::warn(),
                Cockpit::run_over_grant,
            ))
            .child(self.outcome_banner())
    }

    /// The WHAT-IF / SIMULATE panel: compose any intent over any cell across the
    /// effect palette, PREDICT its consequences in a forked throwaway world (the
    /// real executor, live world untouched), then COMMIT the identical turn.
    pub(crate) fn simulate_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        use starbridge_v2::simulate::SimOutcome;
        let cells = &self.cells;
        let target = cells
            .get(self.sim_target_idx)
            .copied()
            .unwrap_or(self.sim_draft.agent);
        let palette = self.sim_effect_palette();
        let effect = palette.get(self.sim_effect_idx).cloned();
        let effect_label = effect.as_ref().map(|e| e.label()).unwrap_or_default();
        let agent_short = reflect::short_hex(&self.sim_draft.agent.0);
        let target_short = reflect::short_hex(&target.0);
        let n_actions = self.sim_draft.actions.len();
        let n_effects = self.sim_draft.effect_count();
        let predicted_ok = matches!(self.sim_outcome, Some(SimOutcome::Predicted { .. }));

        let mut col = div()
            .id("cockpit-scroll-body-1")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title(
            "SIMULATE · compose any intent · PREDICT before committing",
        ));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Build a turn over any cell(s) across the effect palette, run it through a \
             FORKED throwaway world (the real executor over a deep copy of the live image) \
             to see the predicted post-state + receipt or refusal — the LIVE world is \
             untouched — then COMMIT the identical turn for real.",
        ));

        // --- the pickers (agent · target · effect) ---
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).child("agent:"))
                .child(cycle_chip(
                    cx,
                    "sim-agent",
                    format!("{agent_short} (cycle)"),
                    theme::accent(),
                    Cockpit::sim_cycle_agent,
                ))
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child("· target:"),
                )
                .child(cycle_chip(
                    cx,
                    "sim-target",
                    format!("{target_short} (cycle)"),
                    theme::good(),
                    Cockpit::sim_cycle_target,
                ))
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child("· effect:"),
                )
                .child(cycle_chip(
                    cx,
                    "sim-effect",
                    format!("{effect_label} (cycle)"),
                    theme::warn(),
                    Cockpit::sim_cycle_effect,
                )),
        );
        // --- the build verbs ---
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(small_button(
                    cx,
                    "sim-add",
                    "+ add effect",
                    theme::good(),
                    Cockpit::sim_add_effect,
                ))
                .child(small_button(
                    cx,
                    "sim-pop",
                    "− last action",
                    theme::muted(),
                    Cockpit::sim_pop_action,
                ))
                .child(small_button(
                    cx,
                    "sim-clear",
                    "clear draft",
                    theme::muted(),
                    Cockpit::sim_clear,
                )),
        );

        // --- the draft forest ---
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(pill(format!("{n_actions} action(s)"), theme::accent()))
                .child(pill(format!("{n_effects} effect(s)"), theme::accent())),
        );
        let mut forest_box = div()
            .flex()
            .flex_col()
            .gap_0p5()
            .p_2()
            .rounded_md()
            .bg(theme::panel())
            .max_h(px(150.))
            .overflow_hidden();
        if self.sim_draft.actions.is_empty() {
            forest_box = forest_box.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("(empty forest — pick a target + effect and press + add)"),
            );
        } else {
            for (i, a) in self.sim_draft.actions.iter().enumerate() {
                let tgt = reflect::short_hex(&a.target.0);
                let effs = a
                    .effects
                    .iter()
                    .map(|e| e.label())
                    .collect::<Vec<_>>()
                    .join(" · ");
                forest_box = forest_box.child(
                    div()
                        .text_xs()
                        .text_color(theme::text())
                        .child(format!("[{i}] on {tgt}: {effs}")),
                );
            }
        }
        col = col.child(forest_box);

        // --- the SIMULATE + COMMIT verbs ---
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(small_button(
                    cx,
                    "sim-run",
                    "▶ SIMULATE (predict)",
                    theme::accent(),
                    Cockpit::sim_run,
                ))
                .child({
                    // The commit button is enabled (and colored go) only after a
                    // predicted-commit; otherwise it is dimmed + explains itself.
                    let (label, color) = if predicted_ok {
                        ("✓ COMMIT for real", theme::good())
                    } else {
                        ("✓ commit (simulate first)", theme::muted())
                    };
                    small_button(cx, "sim-commit", label, color, Cockpit::sim_commit)
                }),
        );

        // --- the prediction results ---
        col = col.child(self.simulate_results());

        // --- the real-commit banner (distinct from the prediction) ---
        if let Some(b) = &self.sim_commit_banner {
            let color = if b.contains("REJECTED") || b.contains("simulate first") {
                theme::warn()
            } else {
                theme::good()
            };
            col = col.child(
                div()
                    .mt_1()
                    .p_2()
                    .rounded_md()
                    .bg(theme::panel())
                    .text_xs()
                    .text_color(color)
                    .child(b.clone()),
            );
        }
        col
    }

    /// Render the last SIMULATE outcome — the predicted receipt + per-cell deltas +
    /// dynamics, or the refusal (the executor's verdict run one turn ahead).
    pub(crate) fn simulate_results(&self) -> gpui::AnyElement {
        use starbridge_v2::simulate::SimOutcome;
        let mut box_ = div()
            .flex()
            .flex_col()
            .gap_1()
            .mt_1()
            .p_2()
            .rounded_md()
            .border_1()
            .border_color(theme::border())
            .bg(theme::panel());
        match &self.sim_outcome {
            None => box_
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child("(no prediction yet — press ▶ SIMULATE)"),
                )
                .into_any_element(),
            Some(SimOutcome::Predicted {
                receipt,
                deltas,
                events,
                cell_count_delta,
                predicted_root,
                ..
            }) => {
                box_ = box_.child(
                    div()
                        .flex()
                        .flex_wrap()
                        .items_center()
                        .gap_1()
                        .child(pill("PREDICTED: would COMMIT", theme::good()))
                        .child(pill(
                            format!("{} action(s)", receipt.action_count),
                            theme::accent(),
                        ))
                        .child(pill(
                            format!("{} computrons", receipt.computrons_used),
                            theme::accent(),
                        ))
                        .child(pill(
                            format!("receipt {}", reflect::short_hex(&receipt.receipt_hash())),
                            theme::muted(),
                        )),
                );
                box_ = box_.child(
                    div()
                        .flex()
                        .flex_wrap()
                        .items_center()
                        .gap_1()
                        .child(
                            div()
                                .text_xs()
                                .text_color(theme::muted())
                                .child("predicted image root:"),
                        )
                        .child(pill(reflect::short_hex(predicted_root), theme::accent()))
                        .when(*cell_count_delta != 0, |d| {
                            d.child(pill(format!("cells {:+}", cell_count_delta), theme::good()))
                        }),
                );
                box_ = box_.child(section_title("predicted cell deltas"));
                if deltas
                    .iter()
                    .all(|d| !d.balance_changed() && d.before.is_some())
                {
                    box_ = box_.child(div().text_xs().text_color(theme::muted()).child(
                        "(no balance moved — a non-value effect; the receipt above still binds it)",
                    ));
                }
                for d in deltas {
                    let cell = reflect::short_hex(&d.cell.0);
                    let line = match (d.before, d.after) {
                        (None, Some(a)) => format!("· {cell}  BORN → balance {a}"),
                        (Some(_), None) => format!("· {cell}  RETIRED"),
                        (Some(b), Some(a)) if b != a => format!("· {cell}  {b} → {a}"),
                        (Some(b), Some(_)) => format!("· {cell}  unchanged ({b})"),
                        (None, None) => format!("· {cell}  (absent)"),
                    };
                    let color = if d.balance_changed() {
                        theme::text()
                    } else {
                        theme::muted()
                    };
                    box_ = box_.child(div().text_xs().text_color(color).child(line));
                }
                if !events.is_empty() {
                    box_ = box_.child(section_title("predicted dynamics"));
                    for ev in events.iter().take(8) {
                        box_ = box_.child(
                            div()
                                .text_xs()
                                .text_color(theme::muted())
                                .child(format!("· {}", ev.label())),
                        );
                    }
                }
                box_.into_any_element()
            }
            Some(SimOutcome::Refused {
                reason,
                static_refusal,
                at_action,
                ..
            }) => {
                let badge = if *static_refusal {
                    "PREDICTED: REFUSED (static rail — caught before submission)"
                } else {
                    "PREDICTED: REFUSED (the executor's guarantee would fire)"
                };
                box_ = box_.child(
                    div()
                        .flex()
                        .flex_wrap()
                        .items_center()
                        .gap_1()
                        .child(pill(badge, theme::bad()))
                        .when(!at_action.is_empty(), |d| {
                            d.child(pill(format!("@ action {at_action:?}"), theme::warn()))
                        }),
                );
                box_ = box_.child(
                    div()
                        .text_xs()
                        .text_color(theme::bad())
                        .child(reason.clone()),
                );
                box_ = box_.child(div().text_xs().text_color(theme::muted()).child(
                    "this is the live executor's verdict, run one turn ahead — no gas spent, \
                     the live image untouched.",
                ));
                box_.into_any_element()
            }
        }
    }

    pub(crate) fn outcome_banner(&self) -> impl IntoElement {
        let (txt, color) = match &self.last_outcome {
            // A rejected turn OR a refused shell op — the guarantee firing.
            Some(s) if s.contains("REJECTED") || s.contains("REFUSED") => (s.clone(), theme::bad()),
            Some(s) => (s.clone(), theme::good()),
            None => ("(no turn run yet)".to_string(), theme::muted()),
        };
        div()
            .mt_2()
            .p_2()
            .rounded_md()
            .bg(theme::panel())
            .text_xs()
            .text_color(color)
            .child(txt)
    }

    // =======================================================================
    // THE GENERIC PRESENTATION RENDERER — the keystone of the moldable inspector.
    //
    // ONE gpui function per `PresentationBody` variant. Every `Presentable` (cell,
    // receipt chain, held cap, reflected constraint, inspected token, …) renders
    // through this single dispatch — adding a `Presentable` later needs NO new gpui
    // code; adding a genuinely new visual kind adds ONE arm here. The model is pure
    // data (proven by `cargo test`); this is the thin render layer the doc's §1.3
    // promises.
    // =======================================================================

    /// THE dispatch: one `PresentationBody` → one widget. Pure (reads the body data
    /// the model already computed off the live world; touches no `self`).
    pub(crate) fn render_presentation_body(body: &PresentationBody) -> gpui::AnyElement {
        match body {
            PresentationBody::Fields(i) => inspectable_row(i).into_any_element(),
            PresentationBody::Graph(g) => render_graph_body(g).into_any_element(),
            PresentationBody::StateMachine(sm) => render_state_machine(sm).into_any_element(),
            PresentationBody::Gauge(g) => render_gauge(g).into_any_element(),
            PresentationBody::Timeline(t) => render_timeline(t).into_any_element(),
            PresentationBody::MerkleTree(m) => render_merkle(m).into_any_element(),
            PresentationBody::Lattice(l) => render_lattice(l).into_any_element(),
            PresentationBody::Trace(t) => render_trace(t).into_any_element(),
            PresentationBody::Prose(p) => div()
                .p_2()
                .text_xs()
                .text_color(theme::text())
                .child(p.clone())
                .into_any_element(),
        }
    }

    // =======================================================================
    // THE MOLDABLE INSPECTOR panel — the Pharo moldable inspector made visible.
    // =======================================================================

    /// Build the presentation SET for a NON-`Cell` lens family, off the focused
    /// cell / the live world. Each arm constructs the lane's real `Presentable`
    /// and returns its `present(ctx)` set — the SAME `Vec<Presentation>` the
    /// `Cell` lens yields, rendered through the SAME generic body widget. This is
    /// what makes the L4–L10 inspector lanes reachable WITHOUT any new gpui code.
    /// `None` iff the lane has nothing to present over this focus (a held-cap-less
    /// cell, an empty receipt chain) — surfaced honestly, never faked.
    pub(crate) fn lens_present_set(&self, w: &World, focus: CellId) -> Option<Vec<Presentation>> {
        let ctx = PresentCtx::new(w, focus);
        match self.moldable_lens {
            // Already handled by the Registry/memo spine in the caller.
            MoldableLens::Cell => Registry::new(w).present(FocusTarget::Cell(focus), focus),

            // L4 — the focused cell's FIRST held capability (its c-list head).
            MoldableLens::Capability => {
                let held = HeldCapability::all_for(w, focus);
                held.into_iter().next().map(|h| h.present(&ctx))
            }

            // L5 — the focused cell's DEEP reflection.
            MoldableLens::DeepCell => DeepCell::from_world(w, focus).map(|d| d.present(&ctx)),

            // L6 — the live receipt chain + (when present) the latest receipt.
            // The chain is always presentable (empty chain ⟹ an empty timeline,
            // which is still an honest presentation set, so this never `None`s
            // on an empty image).
            MoldableLens::Receipt => {
                let chain = ReflectedReceiptChain::from_world(w);
                let mut set = chain.present(&ctx);
                if let Some(last) = w.receipts().last() {
                    set.extend(ReflectedReceipt::new(last.clone()).present(&ctx));
                }
                Some(set)
            }

            // L7 — a real minted macaroon, decoded. The cockpit's own
            // `lane_token` gadget mints against its service root key; we re-derive
            // a fresh clerk (it is not Clone) and mint the root token, then wrap it
            // as the decoded `InspectedToken`. Real HMAC chain, real caveats.
            MoldableLens::Token => {
                let mut clerk = self.lane_token.fresh_clerk();
                let token = self.lane_token.mint_root(&mut clerk);
                Some(InspectedToken::new(token, MOLDABLE_TOKEN_ROOT_KEY).present(&ctx))
            }

            // L9 — the focused cell's canonical state-commitment binding (the
            // 8-felt commitment + the anti-omission readout + the absorb trace).
            MoldableLens::Circuit => {
                StateCommitmentBinding::from_world(w, focus).map(|s| s.present(&ctx))
            }

            // L10 — a proven settlement family (a sample escrow deal), its
            // deal-terms + real lifecycle state machine + the genuine descriptor's
            // perpetual-constraint invariant. The terms are a concrete legible
            // deal (the lane is reachable; the SIMULATE/LANES tabs author real
            // ones).
            MoldableLens::Settlement => {
                let escrow = SettlementFamily::Escrow(dregg_cell::blueprint::EscrowTerms {
                    amount: 100,
                    depositor: dregg_cell::field_from_u64(2222),
                    beneficiary: dregg_cell::field_from_u64(1111),
                    condition: dregg_cell::field_from_u64(99),
                    timeout_height: 50,
                });
                Some(escrow.present(&ctx))
            }

            // L8 — the federation survey. In the embedded image no consensus node
            // is connected, so the survey is `disconnected()` — but it still
            // surfaces the captp-only remote-path catalog as a real RawFields
            // presentation (honest about the remote-only reach), so the lane is
            // never blank.
            MoldableLens::Federation => {
                let survey = FederationSurvey::disconnected();
                Some(vec![survey.remote_presentation()])
            }

            // ⌖ BLAME (cv) — "why does this cell exist": dial ClusterVision for the
            // agent reasoning that wrote the focused cell's backing source file. A
            // domain cell is content-addressed (no path of its own), so the question
            // resolves to the inspector image's OWN provenance: the swarm reasoning
            // that wrote the cockpit, keyed on the focused cell's identity. The dial
            // degrades HONESTLY inside `CvProvenance::dial` when cv is absent from
            // PATH — never a fabricated provenance edge. Renders through the SAME
            // generic body widget (Timeline / Prose / Fields all already handled).
            MoldableLens::Blame => {
                Some(CvProvenance::dial(focus, CV_BLAME_SOURCE_PATH).present(&ctx))
            }

            // 🔒 READ-CAP / PRIVACY — the read-confidentiality membrane, WELDED onto
            // the landed `dregg_cell_crypto::read_cap` organ (the privacy M0 weld commit):
            // the encrypted-field set read off the live field-visibility, the
            // `granted ⊆ held` read-lattice (the real `ReadCap::attenuate`), and the
            // byte-identical-commitment invariant demonstrated live. The lens is real
            // now; a cell with no committed slots degrades honestly inside `present`.
            MoldableLens::ReadCap => {
                starbridge_v2::read_cap_lens::ReadConfidentiality::from_world(w, focus)
                    .map(|v| v.present(&ctx))
            }

            // ⟲ HISTORY / UNDO — per-cell reversibility, WELDED onto the landed
            // `dregg_turn::reversible` organ (M-REV-0). The reversibility map (each
            // change-kind to this cell classified by the real Effect::invert over the
            // live ledger into clean/contextual/committed) + the cell's lifecycle
            // posture + the un-turn model. The per-cell, lens-shaped view of the same
            // reversibility the REPLAY tab time-travels for the whole image.
            MoldableLens::History => {
                starbridge_v2::history_lens::CellReversibility::from_world(w, focus)
                    .map(|v| v.present(&ctx))
            }
        }
    }
}
