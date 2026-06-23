//! THE ⚙ DEVTOOLS surface — "Firefox/Firebug devtools, but for a verified OS".
//!
//! ONE tab with three inspector SUB-TABS, mirroring the moldable inspector's
//! tab-strip render (one ghost `Button` per sub-tab, the active one `.selected()`).
//! Each sub-tab is a devtools panel over the LIVE embedded `World` the cockpit
//! already holds — no parallel data source, no fabricated traffic:
//!
//!   1. NETWORK — the data plane, live. Like a browser Network tab: each "request"
//!      is a delivery/turn drawn from the dynamics stream + the receipt feed. Turn
//!      commits / queues / refusals / emit-event notify edges (the async A2 seam)
//!      become rows with a status (delivered / pending / refused) + timing
//!      (computrons) + the receipt as the "response". Filterable by a free-text
//!      query over the row text. The live DP-2 data-plane comms API (inbox queue
//!      depth, pub/sub topic fan-out) is the richer source as it lands — noted as
//!      the next wire; today the EVENT-EMITTED notify edges ARE the live queue
//!      traffic the executor receipts.
//!
//!   2. LOG / RECEIPTS — the blocklace + receipt timeline as a filterable,
//!      drill-down console. Every committed turn/receipt is a row (agent · effect
//!      count · status · root); clicking one selects it (the center inspector
//!      drills into the full `reflect_receipt` field tree + provenance chain). The
//!      same data the center-column BLOCKLACE renders, here as a richer filterable
//!      inspector.
//!
//!   3. FEDERATION — the distribution axis. View (and stub-configure) the
//!      federation: committee members, current epoch, threshold, checkpoint height,
//!      latest attested root, cross-fed bridges + the revocation set — read from
//!      the live-node `federations()` snapshot when a node is connected, else the
//!      embedded image's own state-root commitment + the honest captp-only
//!      remote-path catalog (`FederationSurvey`). "Configure" affordances are
//!      cap-gated turn STUBS (noted; the live grants land through the executor).

use super::*;

/// Which DEVTOOLS inspector sub-tab is open (mirrors the moldable lens picker, but
/// a fixed three-element strip). Stored as a `u8` on the cockpit so it survives
/// re-render + nav, like the other panel selectors.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum DevtoolsSub {
    /// The data plane: deliveries / turns / queues / wakes as a browser Network tab.
    Network,
    /// The receipt + blocklace timeline as a filterable drill-down console.
    Log,
    /// The federation: committee · epoch · checkpoint · bridges · revocation.
    Federation,
}

impl DevtoolsSub {
    pub(crate) const ALL: [DevtoolsSub; 3] =
        [DevtoolsSub::Network, DevtoolsSub::Log, DevtoolsSub::Federation];

    fn label(self) -> &'static str {
        match self {
            DevtoolsSub::Network => "⇄ NETWORK",
            DevtoolsSub::Log => "▤ LOG / RECEIPTS",
            DevtoolsSub::Federation => "⬡ FEDERATION",
        }
    }

    /// The `u8` index this sub-tab is stored as on the cockpit.
    fn index(self) -> u8 {
        match self {
            DevtoolsSub::Network => 0,
            DevtoolsSub::Log => 1,
            DevtoolsSub::Federation => 2,
        }
    }

    fn from_index(i: u8) -> DevtoolsSub {
        match i {
            1 => DevtoolsSub::Log,
            2 => DevtoolsSub::Federation,
            _ => DevtoolsSub::Network,
        }
    }
}

impl Cockpit {
    // --- sub-tab + filter handlers (the additive devtools verbs) ------------

    /// Open DEVTOOLS sub-tab `i` (a tab-strip click). Free in-memory selector —
    /// conserves nothing, repaints at once.
    pub(crate) fn devtools_open_sub(&mut self, i: u8, cx: &mut Context<Self>) {
        self.devtools_sub = i;
        cx.notify();
    }

    /// Append a char to the devtools row filter (the Network/Log filter box). A
    /// real `Input`-style affordance over the cockpit's own key path would replace
    /// this; for now the filter is driven by the clickable preset chips below + the
    /// "clear" verb, keeping the panel gpui-free of a focused text input.
    pub(crate) fn devtools_set_filter(&mut self, q: &str, cx: &mut Context<Self>) {
        self.devtools_filter = q.to_string();
        cx.notify();
    }

    pub(crate) fn devtools_clear_filter(&mut self, cx: &mut Context<Self>) {
        self.devtools_filter.clear();
        cx.notify();
    }

    // The preset filter verbs (distinct `fn`-pointer handlers so they ride the
    // `cycle_chip` factory, which takes a non-capturing `fn`). Each sets the row
    // filter to a devtools-typical kind.
    pub(crate) fn devtools_filter_committed(&mut self, cx: &mut Context<Self>) {
        self.devtools_set_filter("committed", cx);
    }
    pub(crate) fn devtools_filter_refused(&mut self, cx: &mut Context<Self>) {
        self.devtools_set_filter("refused", cx);
    }
    pub(crate) fn devtools_filter_queued(&mut self, cx: &mut Context<Self>) {
        self.devtools_set_filter("queued", cx);
    }
    pub(crate) fn devtools_filter_notify(&mut self, cx: &mut Context<Self>) {
        self.devtools_set_filter("notify", cx);
    }

    // --- the panel root ------------------------------------------------------

    /// THE DEVTOOLS panel: the sub-tab strip + the active inspector body.
    pub(crate) fn devtools_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let sub = DevtoolsSub::from_index(self.devtools_sub);
        let mut col = div()
            .id("devtools-scroll-body")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();

        col = col.child(section_title("⚙ DEVTOOLS · Firebug for a verified OS"));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Three inspectors over the LIVE embedded image — the data plane \
             (deliveries · queues · wakes), the receipt console, and the federation. \
             Every row is real executor traffic, not a mock.",
        ));

        // --- the sub-tab strip (mirrors the moldable inspector tab-strip) ---
        let mut strip = div().flex().flex_wrap().gap_1().mt_1();
        for s in DevtoolsSub::ALL {
            let active = s == sub;
            let idx = s.index();
            let id = SharedString::from(format!("devtools-sub-{idx}"));
            strip = strip.child(
                Button::new(id)
                    .label(s.label())
                    .ghost()
                    .small()
                    .selected(active)
                    .on_click(cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
                        this.devtools_open_sub(idx, cx);
                    })),
            );
        }
        col = col.child(strip);

        // --- the active inspector body ---
        let body = match sub {
            DevtoolsSub::Network => self.devtools_network(cx).into_any_element(),
            DevtoolsSub::Log => self.devtools_log(cx).into_any_element(),
            DevtoolsSub::Federation => self.devtools_federation(cx).into_any_element(),
        };
        col = col.child(
            div()
                .flex()
                .flex_col()
                .gap_1()
                .p_2()
                .mt_1()
                .rounded_md()
                .border_1()
                .border_color(theme::border())
                .bg(theme::panel())
                .child(body),
        );
        col
    }

    // --- the FILTER bar (shared by NETWORK + LOG) ---------------------------

    /// A row-filter bar: the live query as a pill + clickable preset chips that set
    /// it + a clear chip. A focused free-text `Input` is the next wire (the cockpit
    /// owns the key path through the ⌘K palette today); the presets cover the
    /// devtools-typical filters (by kind) without a second focus owner.
    fn devtools_filter_bar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let q = self.devtools_filter.clone();
        let active = if q.is_empty() { "all".to_string() } else { q.clone() };
        div()
            .flex()
            .flex_wrap()
            .items_center()
            .gap_1()
            .child(div().text_xs().text_color(theme::muted()).child("filter:"))
            .child(pill(format!("⌕ {active}"), theme::good()))
            .child(cycle_chip(cx, "devtools-flt-commit", "committed".to_string(), theme::accent(), Cockpit::devtools_filter_committed))
            .child(cycle_chip(cx, "devtools-flt-refuse", "refused".to_string(), theme::accent(), Cockpit::devtools_filter_refused))
            .child(cycle_chip(cx, "devtools-flt-queue", "queued".to_string(), theme::accent(), Cockpit::devtools_filter_queued))
            .child(cycle_chip(cx, "devtools-flt-emit", "notify".to_string(), theme::accent(), Cockpit::devtools_filter_notify))
            .child(cycle_chip(cx, "devtools-flt-clear", "✕ clear".to_string(), theme::muted(), Cockpit::devtools_clear_filter))
    }

    /// Does this row text pass the current filter (case-insensitive substring)?
    fn devtools_passes(&self, row: &str) -> bool {
        let q = self.devtools_filter.to_ascii_lowercase();
        q.is_empty() || row.to_ascii_lowercase().contains(&q)
    }

    // =======================================================================
    // 1. NETWORK — the data plane, live (the browser Network tab).
    // =======================================================================

    fn devtools_network(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1();
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .child(
                    "THE DATA PLANE — each row is a delivery/turn the executor receipted: \
                     a turn COMMIT (delivered), a QUEUE under suspension (pending), a \
                     REFUSAL (an ocap/verification gate firing), or an EMIT-EVENT notify \
                     edge (the async A2 inbox seam — the live queue traffic). Timing = \
                     computrons; status = the verdict; the receipt is the response.",
                ),
        );

        // The live-node feed strip (the remote data plane), when connected.
        if let Some(ln) = self.live_node.as_ref() {
            let feed = &self.live_feed;
            col = col.child(
                div()
                    .flex()
                    .flex_wrap()
                    .gap_1()
                    .items_center()
                    .mt_1()
                    .child(pill("remote node", theme::warn()))
                    .child(pill(ln.client().describe(), theme::accent()))
                    .child(pill(format!("{} streamed", feed.receipts().len()), theme::good()))
                    .children(
                        feed.latest()
                            .map(|e| pill(format!("head #{} · {}", e.chain_index, e.finality), theme::accent())),
                    ),
            );
        }

        col = col.child(self.devtools_filter_bar(cx));

        // The protocol summary counters (the "request stats" header).
        let events = w.dynamics().all();
        let (mut delivered, mut pending, mut refused, mut wakes) = (0usize, 0usize, 0usize, 0usize);
        for ev in events {
            match ev {
                starbridge_v2::dynamics::WorldEvent::TurnCommitted { .. } => delivered += 1,
                starbridge_v2::dynamics::WorldEvent::TurnQueued { .. } => pending += 1,
                starbridge_v2::dynamics::WorldEvent::TurnRejected { .. } => refused += 1,
                starbridge_v2::dynamics::WorldEvent::EventEmitted { .. } => wakes += 1,
                _ => {}
            }
        }
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .mt_1()
                .child(pill(format!("{delivered} delivered"), theme::good()))
                .child(pill(format!("{pending} pending"), theme::warn()))
                .child(pill(format!("{refused} refused"), theme::bad()))
                .child(pill(format!("{wakes} notify/wake"), theme::accent())),
        );

        // The column header.
        col = col.child(
            div()
                .flex()
                .justify_between()
                .px_2()
                .pt_1()
                .border_b_1()
                .border_color(theme::border())
                .child(div().text_xs().text_color(theme::muted()).min_w(px(70.)).child("status"))
                .child(div().text_xs().text_color(theme::muted()).flex_1().child("delivery / turn"))
                .child(div().text_xs().text_color(theme::muted()).child("timing · response")),
        );

        // The rows: the dynamics stream as deliveries, most-recent-first. The data-
        // plane traffic the executor receipted, filterable.
        let receipts = w.receipts();
        let mut any = false;
        let mut rcpt_i = receipts.len(); // walk receipts backwards alongside commits
        for (n, ev) in events.iter().enumerate().rev() {
            use starbridge_v2::dynamics::WorldEvent;
            let (status, status_color, line, timing): (&str, Hsla, String, String) = match ev {
                WorldEvent::TurnCommitted { agent, action_count, computrons, height, .. } => {
                    // Pair with the matching receipt (response), walking backwards.
                    rcpt_i = rcpt_i.saturating_sub(1);
                    let resp = receipts
                        .get(rcpt_i)
                        .map(|r| format!("◀ {}", reflect::short_hex(&r.receipt_hash())))
                        .unwrap_or_else(|| "◀ (receipt)".into());
                    (
                        "committed",
                        theme::good(),
                        format!(
                            "turn · {} → @h{height} ({action_count} effect{})",
                            reflect::short_hex(agent.as_bytes()),
                            if *action_count == 1 { "" } else { "s" },
                        ),
                        format!("{computrons} cu · {resp}"),
                    )
                }
                WorldEvent::TurnQueued { agent } => (
                    "pending",
                    theme::warn(),
                    format!("turn QUEUED (suspended) · {}", reflect::short_hex(agent.as_bytes())),
                    "— · awaiting resume".into(),
                ),
                WorldEvent::TurnRejected { agent, reason } => (
                    "refused",
                    theme::bad(),
                    format!("turn REFUSED · {} · {reason}", reflect::short_hex(agent.as_bytes())),
                    "— · ocap gate".into(),
                ),
                WorldEvent::EventEmitted { sender, cell, data_len, .. } => (
                    "notify",
                    theme::accent(),
                    format!(
                        "emit-event {} → {} (inbox +1)",
                        reflect::short_hex(sender.as_bytes()),
                        reflect::short_hex(cell.as_bytes()),
                    ),
                    format!("{data_len}B · notify edge"),
                ),
                // Non-data-plane transitions are out of the Network tab's scope.
                _ => continue,
            };
            let rowtext = format!("{status} {line} {timing}");
            if !self.devtools_passes(&rowtext) {
                continue;
            }
            any = true;
            col = col.child(
                div()
                    .id(SharedString::from(format!("devtools-net-{n}")))
                    .flex()
                    .items_center()
                    .justify_between()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .child(div().min_w(px(70.)).child(pill(status, status_color)))
                    .child(div().text_xs().text_color(theme::text()).flex_1().px_2().child(line))
                    .child(div().text_xs().text_color(theme::muted()).child(timing)),
            );
        }
        if !any {
            col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child(
                "(no data-plane traffic matches — run a verb in the COMPOSER, or clear the filter)",
            ));
        }

        // The honest next-wire seam.
        col = col.child(
            div()
                .mt_2()
                .pt_1()
                .border_t_1()
                .border_color(theme::border())
                .text_xs()
                .text_color(theme::muted())
                .child(
                    "SEAM · the DP-2 data-plane comms API (live inbox queue depth, \
                     dequeue cursors, pub/sub topic fan-out, per-session delivery state) \
                     is the richer Network source as it lands. Today the notify edges \
                     above ARE the live queue traffic — the one receipted seam the \
                     executor records when a sender enqueues into a recipient's inbox.",
                ),
        );
        col
    }

    // =======================================================================
    // 2. LOG / RECEIPTS — the filterable drill-down console.
    // =======================================================================

    fn devtools_log(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1();
        col = col.child(
            div().text_xs().text_color(theme::muted()).child(
                "THE RECEIPT CONSOLE — every committed turn/receipt as a row \
                 (agent · effects · finality · post-root). Click a row to DRILL DOWN: \
                 the center inspector opens its full receipt field tree + the \
                 previous-receipt provenance link. The blocklace, as a filterable log.",
            ),
        );
        col = col.child(self.devtools_filter_bar(cx));

        let receipts = w.receipts();
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .mt_1()
                .child(pill(format!("{} receipt(s)", receipts.len()), theme::good()))
                .child(pill(format!("h{}", w.height()), theme::accent()))
                .child(pill(format!("root {}", reflect::short_hex(&w.state_root())), theme::muted())),
        );

        if receipts.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child(
                "(no receipts yet — run a verb in the COMPOSER)",
            ));
            return col;
        }

        // The column header.
        col = col.child(
            div()
                .flex()
                .justify_between()
                .px_2()
                .pt_1()
                .border_b_1()
                .border_color(theme::border())
                .child(div().text_xs().text_color(theme::muted()).min_w(px(64.)).child("receipt"))
                .child(div().text_xs().text_color(theme::muted()).flex_1().child("agent · effects · finality"))
                .child(div().text_xs().text_color(theme::muted()).child("post-root")),
        );

        let mut any = false;
        for (i, r) in receipts.iter().enumerate().rev() {
            let selected = matches!(self.selection, Selection::Receipt(s) if s == i);
            let hash = reflect::short_hex(&r.receipt_hash());
            let agent = reflect::short_hex(r.agent.as_bytes());
            let fin = format!("{:?}", r.finality);
            let status_color = if r.was_burn { theme::warn() } else { theme::good() };
            let line = format!(
                "{agent} · {} effect{} · {fin}{}",
                r.action_count,
                if r.action_count == 1 { "" } else { "s" },
                if r.was_burn { " · ⚠ burn" } else { "" },
            );
            let rowtext = format!("committed {hash} {line}");
            if !self.devtools_passes(&rowtext) {
                continue;
            }
            any = true;
            col = col.child(
                div()
                    .id(SharedString::from(format!("devtools-log-{i}")))
                    .flex()
                    .items_center()
                    .justify_between()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if selected { theme::panel_hi() } else { theme::panel() })
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
                            .min_w(px(64.))
                            .child(pill(format!("●─ {hash}"), status_color)),
                    )
                    .child(div().text_xs().text_color(theme::text()).flex_1().px_2().child(line))
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::accent())
                            .child(reflect::short_hex(&r.post_state_hash)),
                    ),
            );
        }
        if !any {
            col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child(
                "(no receipts match the filter — clear it to see the whole log)",
            ));
        }

        // The drill-down readout of the SELECTED receipt (the expanded console row).
        if let Selection::Receipt(s) = self.selection {
            if let Some(r) = receipts.get(s) {
                let insp = reflect::reflect_receipt(r);
                let mut detail = div()
                    .flex()
                    .flex_col()
                    .gap_0p5()
                    .mt_2()
                    .p_2()
                    .rounded_md()
                    .border_1()
                    .border_color(theme::accent())
                    .bg(theme::panel_hi())
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::text()).child(insp.title.clone()))
                            .child(kind_badge(insp.kind)),
                    )
                    .child(div().text_xs().text_color(theme::muted()).child(insp.subtitle.clone()));
                for f in &insp.fields {
                    detail = detail.child(field_row(f));
                }
                // The provenance chain hint (the previous-receipt link).
                detail = detail.child(
                    div().text_xs().text_color(theme::muted()).mt_1().child(
                        match r.previous_receipt_hash {
                            Some(p) => format!(
                                "provenance ← previous receipt {} (the agent's chain)",
                                reflect::short_hex(&p)
                            ),
                            None => "provenance: this is the agent's GENESIS receipt (chain root)".into(),
                        },
                    ),
                );
                col = col.child(detail);
            }
        } else {
            col = col.child(
                div().text_xs().text_color(theme::muted()).mt_1().child(
                    "▸ click a receipt row to drill into its full field tree + provenance chain",
                ),
            );
        }
        col
    }

    // =======================================================================
    // 3. FEDERATION — committee · epoch · checkpoint · bridges · revocation.
    // =======================================================================

    fn devtools_federation(&self, _cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1();
        col = col.child(
            div().text_xs().text_color(theme::muted()).child(
                "THE DISTRIBUTION AXIS — this sovereign image among a federation: the \
                 committee roster, the current epoch, the checkpoint height + latest \
                 attested root, the cross-fed bridges, and the revocation set. Read from \
                 the live node when connected, else this image's own commitment + the \
                 honest captp-only remote catalog.",
            ),
        );

        // The LIVE federation snapshot (a connected node), when present.
        let live_feds: Vec<starbridge_v2::model::FederationInfo> = self
            .live_node
            .as_ref()
            .and_then(|ln| ln.client().federations().ok())
            .unwrap_or_default();

        if !live_feds.is_empty() {
            col = col.child(div().text_xs().text_color(theme::good()).mt_1().child("● LIVE federations (wire-backed)"));
            for fed in &live_feds {
                col = col.child(self.devtools_federation_card(fed));
            }
        } else {
            // The embedded image: no consensus node connected. Surface THIS image's
            // own state-root commitment as the local-federation card, plus the honest
            // remote-path catalog from the survey.
            col = col.child(
                div()
                    .flex()
                    .flex_wrap()
                    .gap_1()
                    .mt_1()
                    .child(pill("local · embedded image", theme::accent()))
                    .child(pill("epoch 0 · solo (committee of one)", theme::muted()))
                    .child(pill(format!("checkpoint h{}", w.height()), theme::accent()))
                    .child(pill(format!("root {}", reflect::short_hex(&w.state_root())), theme::good())),
            );
            col = col.child(
                div().text_xs().text_color(theme::muted()).child(
                    "this image is its OWN sovereign federation (a committee of one); \
                     connect a node with --node <url> to survey a multi-member committee.",
                ),
            );

            // The honest captp-only remote-path catalog (the same survey panels_main
            // surfaces): the cross-fed bridges + the objects reachable only over the
            // remote path, rendered as a field tree — never faked.
            let survey = FederationSurvey::disconnected();
            let remote = survey.remote_presentation();
            col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child(
                "cross-fed bridges + remote-path objects (captp-only — honest catalog):",
            ));
            col = col.child(Self::render_presentation_body(&remote.body));
        }

        // The REVOCATION set + the cap-gated configure STUBS (view now; configure
        // lands through the executor as a real grant/revoke turn).
        col = col.child(
            div()
                .mt_2()
                .pt_1()
                .border_t_1()
                .border_color(theme::border())
                .flex()
                .flex_col()
                .gap_0p5()
                .child(div().text_xs().text_color(theme::muted()).child("revocation set"))
                .child(div().text_xs().text_color(theme::text()).child(
                    "no live revocations on this image (the embedded solo federation \
                     has issued none); a revocation is a real `CapabilityRevoked` turn \
                     through the executor — watch it on the NETWORK tab when fired.",
                )),
        );
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .mt_1()
                .child(pill("⊕ add member — cap-gated turn (stub)", theme::muted()))
                .child(pill("⟳ rotate epoch — cap-gated turn (stub)", theme::muted()))
                .child(pill("⊘ revoke cap — cap-gated turn (stub)", theme::muted())),
        );
        col = col.child(
            div().text_xs().text_color(theme::muted()).child(
                "SEAM · the CONFIGURE affordances (add/remove committee member · rotate \
                 epoch · revoke) are cap-gated turn STUBS — each lands as a real \
                 authorized turn through the embedded executor (the federation crate's \
                 epoch/checkpoint/revocation types), gated by the held federation \
                 admin cap. View is live; configure is the next wire.",
            ),
        );
        col
    }

    /// One LIVE federation as a devtools card: committee · epoch · threshold ·
    /// checkpoint height · attested root · the member roster.
    fn devtools_federation_card(&self, fed: &starbridge_v2::model::FederationInfo) -> impl IntoElement {
        let mut card = div()
            .flex()
            .flex_col()
            .gap_0p5()
            .px_2()
            .py_1()
            .rounded_md()
            .bg(theme::panel_hi())
            .child(
                div()
                    .flex()
                    .flex_wrap()
                    .gap_1()
                    .items_center()
                    .child(pill(
                        if fed.is_local { "local" } else { "remote" },
                        if fed.is_local { theme::good() } else { theme::accent() },
                    ))
                    .child(pill(format!("fed {}", reflect::short_hex_hexstr(&fed.federation_id)), theme::accent()))
                    .child(pill(format!("epoch {}", fed.committee_epoch), theme::muted()))
                    .child(pill(format!("{}-of-{}", fed.threshold, fed.member_count), theme::warn()))
                    .child(pill(format!("checkpoint h{}", fed.latest_height), theme::accent())),
            )
            .child(
                div().text_xs().text_color(theme::muted()).child(format!(
                    "{} finalized root(s) · latest {}",
                    fed.num_finalized_roots,
                    fed.latest_root
                        .as_ref()
                        .map(|r| reflect::short_hex_hexstr(r))
                        .unwrap_or_else(|| "none".into()),
                )),
            );
        for (n, m) in fed.members.iter().enumerate() {
            card = card.child(
                div()
                    .flex()
                    .gap_1()
                    .child(div().text_xs().text_color(theme::muted()).child(format!("member[{n}]")))
                    .child(div().text_xs().text_color(theme::text()).child(reflect::short_hex_hexstr(m))),
            );
        }
        card
    }
}
