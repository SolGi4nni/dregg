//! The moldable inspector, trust/inspect-act/workspace/wonder/lanes panels + the ⤳ SHARE surface, with their action verbs.

use super::*;

impl Cockpit {
    /// The cell the Inspect surface is focused on — the inspector's camera-aim read
    /// off its own view cell (the §3.4 selector), falling back to the first cell. The
    /// SAME focus the moldable panel renders and the live inspector card is built over.
    pub(crate) fn inspector_focus_cell(&self) -> Option<CellId> {
        self.inspector_view
            .doc()
            .focus()
            .or_else(|| self.cells.first().copied())
    }

    /// **ENSURE THE LIVE INSPECTOR CARD (rung 2) is built for the current focus.** Called
    /// on the paint path (where a live `&mut Context` is in hand to mint the gpui entity).
    /// Builds the deos-js [`InspectorCard`](deos_js::inspector_card) over the cockpit's
    /// LIVE `World`, focused on [`Self::inspector_focus_cell`] — a [`CardPane`] entity whose
    /// rendered faces re-read the operator's real cell and whose affordance buttons fire
    /// real verified turns on the live ledger. Rebuilt when the focus moves; fail-soft (a
    /// build error keeps the Rust moldable inspector as the surface). Idempotent.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub(crate) fn ensure_inspector_card(&mut self, cx: &mut Context<Self>) {
        use starbridge_v2::dock::card_surface::build_inspector_card_surface;

        let Some(focus) = self.inspector_focus_cell() else {
            return;
        };
        // Already built for this focus → nothing to do (the entity re-reads the live
        // ledger every paint, so it stays current without a rebuild).
        if self
            .inspector_card
            .as_ref()
            .is_some_and(|m| m.focus == focus)
        {
            return;
        }

        let id = self.next_dev_surface_id();
        // The operator's authority the affordance fires mount under — `Signature` (the
        // attenuated operator hand the agent-attach + card-pane paths use), so the cap
        // tooth genuinely refuses the `escalate` over-reach (Proof ⊄ Signature).
        let held = dregg_cell::AuthRequired::Signature;
        match build_inspector_card_surface(id, self.world.clone(), focus, held, cx) {
            Ok(surface) => {
                self.inspector_card = Some(super::InspectorCardMount {
                    entity: surface.entity_handle(),
                    applet: surface.applet(),
                    focus,
                });
            }
            Err(e) => {
                eprintln!(
                    "ensure_inspector_card: could not build the live inspector card \
                     (keeping the Rust moldable inspector): {e:#}"
                );
            }
        }
    }

    /// **ENSURE A LANDED CARD (a [`ModeCard`]) is built as its mode's main surface** for the
    /// current focus. Called on the paint path (where a live `&mut Context` mints the gpui
    /// entity). Builds the deos-js card over the cockpit's LIVE `World`, focused on
    /// [`Self::inspector_focus_cell`] — a [`CardPane`](starbridge_v2::card_pane::CardPane)
    /// entity whose rendered rows re-read the live ledger and whose affordance buttons fire
    /// real verified turns. Rebuilt when the focus moves; fail-soft (a build error keeps the
    /// Rust panel as the surface). Idempotent.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub(crate) fn ensure_mode_card(
        &mut self,
        kind: starbridge_v2::dock::card_surface::ModeCard,
        cx: &mut Context<Self>,
    ) {
        use starbridge_v2::dock::card_surface::{
            build_mode_card_surface_with_state, DebuggerState, ModeCard, ReplayState, SurfaceState,
        };

        let Some(focus) = self.inspector_focus_cell() else {
            return;
        };
        // A STATEFUL card's view-tree is generated from cockpit-side state (the live clerk, the
        // scrubber cursor, the turn under the lens) that is NOT on the ledger — so a digest of
        // that state joins `focus` in the cache key. When the operator mutates it (a mint, a
        // scrubber move), the digest changes and the card is rebuilt — no staleness. A stateless
        // card's digest is 0, so it caches on `focus` exactly as before (byte-identical).
        let state_fp = self.mode_card_state_fp(kind);
        if self
            .mode_cards
            .get(&kind)
            .is_some_and(|m| m.focus == focus && m.state_fp == state_fp)
        {
            return;
        }

        let id = self.next_dev_surface_id();
        // The operator's authority the affordance fires + the view-edits mount under —
        // `Signature` (the attenuated operator hand), satisfying the card's edit_authority
        // so a reshape-from-within is authorized.
        let held = dregg_cell::AuthRequired::Signature;
        // Thread the live cockpit-side state for the stateful cards (empty for the stateless
        // survey cards), so a carded surface renders the SAME live state its gpui panel shows.
        let result = {
            let state = SurfaceState {
                clerk: matches!(kind, ModeCard::Cipherclerk).then_some(&self.clerk),
                debugger: matches!(kind, ModeCard::Debugger).then_some(DebuggerState {
                    turn: &self.debug_turn,
                    breakpoints: &self.breakpoints,
                }),
                replay: matches!(kind, ModeCard::Replay).then_some(ReplayState {
                    cursor: self.replay_cursor,
                    fork: self.replay_fork.as_ref(),
                }),
            };
            build_mode_card_surface_with_state(
                id,
                kind,
                self.world.clone(),
                focus,
                held,
                &state,
                cx,
            )
        };
        match result {
            Ok(surface) => {
                self.mode_cards.insert(
                    kind,
                    super::ModeCardMount {
                        entity: surface.entity_handle(),
                        surface,
                        focus,
                        state_fp,
                    },
                );
            }
            Err(e) => {
                eprintln!(
                    "ensure_mode_card({kind:?}): could not build the live card \
                     (keeping the Rust panel): {e:#}"
                );
            }
        }
    }

    /// A cheap digest of the cockpit-side [`SurfaceState`] a stateful [`ModeCard`] is built
    /// from (0 for a stateless card). [`Self::ensure_mode_card`] keys the card cache on this
    /// (alongside the focus), so a stateful card is rebuilt the moment the operator mutates the
    /// live state it reflects — the carded surface never lags the gpui panel.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub(crate) fn mode_card_state_fp(
        &self,
        kind: starbridge_v2::dock::card_surface::ModeCard,
    ) -> u64 {
        use starbridge_v2::dock::card_surface::ModeCard;
        match kind {
            ModeCard::Replay => {
                let hlen = self.world.borrow().recorded_turns().len() as u64;
                (hlen << 24)
                    ^ (self.replay_cursor as u64)
                    ^ if self.replay_fork.is_some() {
                        0xF0F0
                    } else {
                        0
                    }
            }
            ModeCard::Debugger => {
                let h = self.debug_turn.hash();
                let mut fp = u64::from_le_bytes(h[..8].try_into().unwrap());
                fp ^= self.breakpoints.len() as u64;
                fp
            }
            ModeCard::Cipherclerk => {
                let ids = self.clerk.identities().count() as u64;
                let toks: u64 = self
                    .clerk
                    .identities()
                    .map(|i| i.clerk.tokens().len() as u64)
                    .sum();
                let dels = self.clerk.delegations().len() as u64;
                (ids << 40) ^ (toks << 16) ^ dels
            }
            _ => 0,
        }
    }

    /// Host a mounted [`ModeCard`]'s [`CardPane`] entity as a mode's main-pane surface (the
    /// card-as-surface mount). The card is built (or rebuilt on a focus change) by
    /// [`Self::ensure_mode_card`] on the paint path in `render`; this hosts the prebuilt
    /// entity in a titled frame with a one-line "this surface IS a deos-js card, editable
    /// from within" footer (mirrors the inspector-card host in `moldable_panel`, an `&self`
    /// host over a `&mut Context`). Fail-soft: if the card is not mounted, `fallback` (the
    /// Rust panel) is rendered.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub(crate) fn mode_card_surface(
        &self,
        kind: starbridge_v2::dock::card_surface::ModeCard,
        cx: &mut Context<Self>,
        fallback: impl FnOnce(&Self, &mut Context<Self>) -> gpui::AnyElement,
    ) -> gpui::AnyElement {
        let Some(mount) = self.mode_cards.get(&kind) else {
            return fallback(self, cx);
        };
        // ONE-HOST-PER-FRAME GUARD: a `CardPane` entity may be hosted at most once per
        // frame. Every pane in the L6 PaneGroup holds ALL tabs, so two split panes can both
        // have this card-tab active at once — hosting the SAME entity twice in one frame
        // re-enters its render lease and aborts the process. The first host this frame wins
        // the live entity; a duplicate shows a calm "shown in another pane" placeholder
        // (the within-window analogue of the torn-off placeholder's one-window invariant).
        if !self.frame_hosted_cards.borrow_mut().insert(kind) {
            return mirror_in_another_pane_placeholder(kind.title());
        }
        // Immediate-mode binds re-read the live ledger at render time, so a notify each paint
        // keeps a bound row current after a fire lands (mirrors `CardSurface`).
        mount.entity.update(cx, |_card, cx| cx.notify());
        let entity = mount.entity.clone();
        // The edit-from-within affordance: a `ViewPatch` routed THROUGH the live mount
        // (re-fold → rebuild the CardPane). A demo `AddText` reshape proves the seam is
        // closed; an unauthorized hand would be refused in-band by the cap tooth.
        let edit_btn = gpui_component::button::Button::new(SharedString::from(format!(
            "mode-card-edit-{kind:?}"
        )))
        .label("✎ edit this surface from within")
        .ghost()
        .xsmall()
        .on_click(cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
            // GUARDED at the event boundary: this click reshapes a live card mount (the
            // card-editor patch + entity swap). gpui dispatches it from a `nounwind`
            // Obj-C callback, so any panic here would `process::abort` the whole cockpit;
            // `guard_ui_event` contains it as a logged no-op (the edit-from-within path
            // is Result-typed, but the entity-update/patch machinery must never unwind to
            // gpui — the same discipline as the pop-out control).
            Cockpit::guard_ui_event("mode-card-edit-from-within", || {
                this.mode_card_edit_view(
                    kind,
                    deos_js::card_editor::ViewPatch::AddText {
                        text: "· reshaped from within (a receipted patch)".into(),
                    },
                    cx,
                );
            });
        }));
        div()
            .id("mode-card-surface")
            .flex()
            .flex_col()
            .gap_1()
            .size_full()
            .child(
                // The card region HUGS the card's content (no `flex_1` stretch that
                // left a dead black canvas below a short card), capped at the pane
                // height (a card taller than the pane clips, as before).
                div()
                    .max_h(gpui::relative(1.))
                    .overflow_hidden()
                    .border_1()
                    .border_color(theme::accent())
                    .rounded_md()
                    .bg(theme::panel())
                    .child(entity),
            )
            .child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .p_1()
                    .child(div().text_xs().text_color(theme::muted()).child(
                        "↑ this surface IS a deos-js card over the LIVE World: rows re-read the \
                         operator's real cells, an affordance button fires a real verified turn.",
                    ))
                    .child(edit_btn),
            )
            .into_any_element()
    }

    /// **EDIT A MOUNTED MODE CARD FROM WITHIN — the open seam, now wired through the live
    /// mount.** Route a [`ViewPatch`](deos_js::card_editor::ViewPatch) (deos.editor/edit_view)
    /// through the mounted card's editable view document: the surface's
    /// [`edit_view`](starbridge_v2::dock::card_surface::ModeCardSurface::edit_view) applies it
    /// as a *receipted patch with blame* (refused in-band if the operator's `held` does not
    /// satisfy the card's edit_authority), re-folds the `ViewTree`, and swaps the re-bridged
    /// `ViewNode` into the live [`CardPane`] — so the surface repaints reshaped on the next
    /// frame (the view is data, not compiled code). A no-op if the card is not mounted; the
    /// outcome (or the in-band refusal) is captured into `last_outcome`.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub(crate) fn mode_card_edit_view(
        &mut self,
        kind: starbridge_v2::dock::card_surface::ModeCard,
        patch: deos_js::card_editor::ViewPatch,
        cx: &mut Context<Self>,
    ) {
        let outcome = match self.mode_cards.get(&kind) {
            Some(mount) => match mount.surface.edit_view(patch, cx) {
                Ok(()) => format!("reshaped the {kind:?} card from within (a receipted patch)"),
                Err(e) => format!("REFUSED · {e}"),
            },
            None => format!("the {kind:?} card is not mounted (nothing to reshape)"),
        };
        self.last_outcome = Some(outcome);
        cx.notify();
    }

    /// THE MOLDABLE INSPECTOR — pick a focused object, render its `Registry`-resolved
    /// presentation SET as a tab-strip (one sub-tab per `Presentation`) through the
    /// generic renderer, with the `Halo` ring + a `Spotter` search box that re-focuses.
    pub(crate) fn moldable_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let w = self.world.borrow();
        let cells = &self.cells;
        // M3: the camera-aim is read FROM the inspector's own view cell (the §3.4
        // `render(workspace_subgraph)` selector move — the focus is a cell read, not
        // a Rust field). The free in-memory draft is the live aim.
        let focus = self
            .inspector_view
            .doc()
            .focus()
            .or_else(|| cells.first().copied());
        let mut col = div()
            .id("cockpit-scroll-body-2")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title(
            "INSPECTOR · the moldable presentation set (Registry · Spotter · Halo)",
        ));

        // ── THE LIVE INSPECTOR CARD (rung 2) ───────────────────────────────────────
        // The Inspect surface IS a deos-js card: the focused cell's moldable faces,
        // generated into a view-tree and rendered by `CardPane` over the cockpit's
        // LIVE `World`. The RawFields rows re-read the operator's real cell off the
        // live ledger; an affordance button fires ONE cap-gated verified turn on that
        // World (a receipt on the cockpit's own tape). Built lazily in
        // `ensure_inspector_card` (on the paint path) and hosted here.
        //
        // NOTHING DRAWS TWICE (HIG). When the card mounts it REPLACES the native
        // presentation set in this same pane — the deep native Registry/Spotter/Halo/
        // RawFields below is gated behind the `moldable_show_native` toggle, so by
        // default exactly ONE object (the card) draws in these bounds (no z-fight with
        // the old native inspector). A deliberate "⊕ deep reflection" toggle reveals the
        // native set as a distinct companion face BELOW the card (a scrolled-to region,
        // never an underlay). Fail-soft: if no card mounted (build error / card-pane
        // off / a duplicate-pane host that skips the entity), `card_is_surface` is false
        // and the native set renders as the surface, so the pane is never blank.
        //
        // ONE-HOST-PER-FRAME GUARD: the inspector `CardPane` entity may be hosted at most
        // once per frame. Two split panes both showing the Moldable surface would otherwise
        // host the SAME entity twice in one frame (re-entering its render lease → abort).
        // The first host this frame wins the live entity; a duplicate skips it (and falls
        // through to the native set, which is safe to host twice).
        #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
        if let Some(mount) = self
            .inspector_card
            .as_ref()
            .filter(|_| !self.frame_hosted_inspector.replace(true))
        {
            // The card's `bind` rows re-read the live ledger at render time, so a notify
            // each paint keeps them current after a fire lands (mirrors `CardSurface`).
            mount.entity.update(cx, |_card, cx| cx.notify());
            col = col.child(
                div()
                    .min_h(px(220.))
                    // Hug the card's content (the card is content-sized) instead of
                    // stretching; cap at the pane height (a tall card clips).
                    .max_h(gpui::relative(1.))
                    .overflow_hidden()
                    .border_1()
                    .border_color(theme::accent())
                    .rounded_md()
                    .bg(theme::panel())
                    .child(mount.entity.clone()),
            );
            // The deep-reflection toggle: reveal/hide the native presentation set as a
            // distinct companion BELOW (never stacked in the card's bounds).
            let show_native = self.moldable_show_native;
            col = col.child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .child(div().text_xs().text_color(theme::muted()).child(
                        "↑ the Inspect surface, reborn as a deos-js card: the focused cell's \
                         faces over the LIVE World. An affordance button fires a real verified \
                         turn; a bound row re-reads the advanced value. Editable from within.",
                    ))
                    .child(cycle_chip(
                        cx,
                        "mold-deep",
                        if show_native {
                            "⊖ hide deep reflection".to_string()
                        } else {
                            "⊕ deep reflection (native presentation set)".to_string()
                        },
                        if show_native {
                            theme::accent()
                        } else {
                            theme::good()
                        },
                        Cockpit::moldable_toggle_native,
                    )),
            );
            // The card is the surface; the native set draws ONLY when deliberately
            // revealed — and then below, as a divided companion region, not an underlay.
            if !show_native {
                return col.into_any_element();
            }
            col = col.child(
                div()
                    .mt_2()
                    .pt_2()
                    .border_t_1()
                    .border_color(theme::border())
                    .text_xs()
                    .text_color(theme::muted())
                    .child(
                        "── deep reflection · the native moldable presentation set (a distinct \
                         companion view below the card, not an overlay) ──",
                    ),
            );
        }

        // The reflexive toggle — turn the inspector ON ITSELF (inspect the inspector).
        {
            let reflexive = self.inspector_reflexive;
            let backing_short = reflect::short_hex(self.inspector_view.backing().as_bytes());
            let rev = self.inspector_view.revision(&w);
            col = col.child(
                div()
                    .flex()
                    .items_center()
                    .gap_1()
                    .child(div().text_xs().text_color(theme::muted()).child(
                        "self-host: the inspector's (focus, present-idx) IS a witnessed cell — ",
                    ))
                    .child(cycle_chip(
                        cx,
                        "mold-reflexive",
                        if reflexive {
                            format!("⟲ inspecting ITSELF (view cell {backing_short} · rev {rev})")
                        } else {
                            "⟲ inspect the inspector".to_string()
                        },
                        if reflexive {
                            theme::accent()
                        } else {
                            theme::good()
                        },
                        Cockpit::moldable_toggle_reflexive,
                    )),
            );
        }
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Every protocol object offers a SET of named presentations (the 7 kinds; \
             RawFields is the universal floor). Pick an object, browse its lenses across \
             the tab-strip — each rendered by the ONE generic widget per body. Search \
             every object's every presentation with the spotter; a hit re-focuses here.",
        ));

        // --- the ⌘K-style Spotter search box + its ranked hits ---
        col = col.child(
            div()
                .flex()
                .items_center()
                .gap_1()
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child("🔍 spotter:"),
                )
                .child(
                    div()
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel())
                        .border_1()
                        .border_color(theme::border())
                        .text_xs()
                        .text_color(theme::text())
                        .min_w(px(220.))
                        .child(if self.moldable_query.is_empty() {
                            "(type to search every object's every presentation)".to_string()
                        } else {
                            self.moldable_query.clone()
                        }),
                )
                .child(small_button(
                    cx,
                    "mold-clear",
                    "clear",
                    theme::muted(),
                    Cockpit::moldable_clear_query,
                )),
        );
        // A small fixed set of example queries the operator can fire (a click drives
        // the REAL `Spotter::search` — gpui has no text input here; the box mirrors it).
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(div().text_xs().text_color(theme::muted()).child("try:"))
                .child(cycle_chip(
                    cx,
                    "mold-q-life",
                    "lifecycle".into(),
                    theme::accent(),
                    |this, cx| {
                        this.moldable_query = "lifecycle".into();
                        cx.notify();
                    },
                ))
                .child(cycle_chip(
                    cx,
                    "mold-q-graph",
                    "ocap Graph".into(),
                    theme::accent(),
                    |this, cx| {
                        this.moldable_query = "ocap Graph".into();
                        cx.notify();
                    },
                ))
                .child(cycle_chip(
                    cx,
                    "mold-q-bal",
                    "balance".into(),
                    theme::accent(),
                    |this, cx| {
                        this.moldable_query = "balance".into();
                        cx.notify();
                    },
                )),
        );
        if let Some(viewer) = focus {
            let spotter = Spotter::new(&w, viewer);
            let hits: Vec<SpotterHit> = spotter.search(&self.moldable_query);
            if !self.moldable_query.trim().is_empty() {
                let mut hits_box = div()
                    .flex()
                    .flex_col()
                    .gap_0p5()
                    .p_2()
                    .rounded_md()
                    .bg(theme::panel());
                if hits.is_empty() {
                    hits_box = hits_box.child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child("(no hits)"),
                    );
                }
                for (n, h) in hits.iter().take(8).enumerate() {
                    let hit_cell = h.focus.cell();
                    let id = SharedString::from(format!("mold-hit-{n}"));
                    hits_box = hits_box.child(
                        div()
                            .id(id)
                            .flex()
                            .justify_between()
                            .px_1()
                            .py_0p5()
                            .rounded_md()
                            .cursor_pointer()
                            .hover(|s| s.bg(theme::border()))
                            .on_mouse_down(
                                MouseButton::Left,
                                cx.listener(move |this, _ev, _w, cx| {
                                    this.moldable_refocus(Some(hit_cell), cx);
                                }),
                            )
                            .child(div().text_xs().text_color(theme::text()).child(format!(
                                "⬡ {} · {}",
                                reflect::short_hex(hit_cell.as_bytes()),
                                h.snippet
                            )))
                            .child(pill(
                                format!("{} · {}", h.matched_kind.slug(), h.score),
                                theme::accent(),
                            )),
                    );
                }
                col = col.child(hits_box);
            }
        }

        // --- the object picker (cycle the focused cell) + the Halo ring ---
        let Some(focus) = focus else {
            return col
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child("(no cells in the image yet)"),
                )
                .into_any_element();
        };
        let reg = Registry::new(&w);
        let halo: Halo = reg.halo(FocusTarget::Cell(focus));
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).child("focus:"))
                .child(cycle_chip(
                    cx,
                    "mold-focus",
                    format!("⬡ {} (cycle)", reflect::short_hex(focus.as_bytes())),
                    theme::good(),
                    Cockpit::moldable_cycle_focus,
                ))
                .child(div().text_xs().text_color(theme::muted()).child("· halo:"))
                .children(
                    halo.commands
                        .iter()
                        .map(|c| pill(format!("{} {}", c.glyph(), c.label()), theme::accent())),
                ),
        );

        // --- the LENS-FAMILY picker — makes the newer inspector lanes (L4–L10)
        // reachable. `Cell` rides the Registry/memo spine; each other family
        // builds its real lane `Presentable` off the focused cell / the live
        // world and renders its set through the SAME generic body widget. ---
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).child("lens:"))
                .child(cycle_chip(
                    cx,
                    "mold-lens",
                    format!("⌖ {} (cycle)", self.moldable_lens.label()),
                    theme::accent(),
                    Cockpit::moldable_cycle_lens,
                )),
        );

        // --- the presentation SET as a tab-strip + the rendered body ---
        // M2: the `Cell` lens projects through the memo (valid while the live head
        // is unchanged; the delta fold drops touched cells). Same `Presentation`
        // set as the pure `reg.present`, now cached (EFFICIENCY-WELD-PLAN §2.3).
        // M3: when the reflexive toggle is on, the camera-aim is the inspector's
        // OWN view cell (FocusTarget::ViewCell) — *inspect the inspector* through
        // the SAME memo + Registry dispatch. The non-`Cell` lenses build their
        // lane `Presentable` directly off the focus / the live world (the L4–L10
        // reach), rendered through the SAME generic body widget below.
        let set: Vec<Presentation> = if self.moldable_lens == MoldableLens::Cell {
            let target = if self.inspector_reflexive {
                FocusTarget::ViewCell(self.inspector_view.backing())
            } else {
                FocusTarget::Cell(focus)
            };
            match self.present_memo.present(&w, target, focus) {
                Some(s) => s,
                None => {
                    return col
                        .child(div().text_xs().text_color(theme::bad()).child(
                            "(the focused object is absent from the live image — a dangling focus)",
                        ))
                        .into_any_element();
                }
            }
        } else {
            match self.lens_present_set(&w, focus) {
                Some(s) => s,
                None => {
                    return col
                        .child(div().text_xs().text_color(theme::warn()).child(format!(
                            "(the {} lens has nothing to present over the focused object yet)",
                            self.moldable_lens.label()
                        )))
                        .into_any_element();
                }
            }
        };
        let idx = self
            .inspector_view
            .doc()
            .present_idx()
            .min(set.len().saturating_sub(1));
        // the tab-strip (one sub-tab per Presentation).
        let mut strip = div().flex().flex_wrap().gap_1().mt_1();
        for (i, p) in set.iter().enumerate() {
            let active = i == idx;
            let id = SharedString::from(format!("mold-sub-{i}"));
            strip = strip.child(
                Button::new(id)
                    .label(format!("{} · {}", p.kind.slug(), p.label))
                    .ghost()
                    .xsmall()
                    .selected(active)
                    .on_click(cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
                        this.moldable_set_present_idx(i, cx);
                    })),
            );
        }
        col = col.child(strip);
        if let Some(p) = set.get(idx) {
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
                    .child(Self::render_presentation_body(&p.body)),
            );
        }
        col.into_any_element()
    }

    // =======================================================================
    // THE ⚷ TRUST tab — the human-layer WHO-I-AM + recovery surface.
    // =======================================================================

    /// Render the TRUST tab: the WHO-I-AM identity card, the KEL rotation timeline,
    /// and the "ask your guardians" recovery gauge — the human-layer face of "you
    /// cannot lose your own OS" (human-layer M1). Built off the REAL `trust_panel`
    /// model (a representative identity until a live identity cell is wired —
    /// HORIZONLOG) and rendered through the SAME generic body widget every lens uses,
    /// so it needs no bespoke gpui.
    pub(crate) fn trust_tab(&self, _cx: &mut Context<Self>) -> gpui::AnyElement {
        let panel = starbridge_v2::trust_panel::TrustPanel::demo();
        let mut col = div()
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_hidden()
            .child(section_title(
                "⚷ TRUST · who-i-am — your devices, your guardians, your recovery",
            ))
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(panel.summary()),
            );
        for p in panel.present() {
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
                    .child(div().text_xs().text_color(theme::accent()).child(format!(
                        "{} · {}",
                        p.kind.slug(),
                        p.label
                    )))
                    .child(Self::render_presentation_body(&p.body)),
            );
        }
        col.into_any_element()
    }

    // =======================================================================
    // THE INSPECT→ACT loop panel.
    // =======================================================================

    /// THE INSPECT→ACT loop — the focused object's reflected state + the messages it
    /// understands (cap-badged), sending one as a REAL verified turn + re-inspecting.
    pub(crate) fn inspect_act_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let w = self.world.borrow();
        let cells = &self.cells;
        let focus = self.inspect_act_focus.or_else(|| cells.first().copied());
        let mut col = div()
            .id("cockpit-scroll-body-3")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title(
            "INSPECT-ACT · the messages it understands → send → re-inspect",
        ));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The Smalltalk inspect→act→inspect loop: an inspected object shows the messages \
             it understands inline (cap-badged for the viewer), you send one as a REAL verified \
             turn, and the post-state re-inspects. A refused send is shown in-band, never swallowed.",
        ));
        let Some(focus) = focus else {
            return col
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child("(no cells yet)"),
                )
                .into_any_element();
        };
        col = col.child(
            div()
                .flex()
                .items_center()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).child("focus:"))
                .child(cycle_chip(
                    cx,
                    "ia-focus",
                    format!("⬡ {} (cycle)", reflect::short_hex(focus.as_bytes())),
                    theme::good(),
                    Cockpit::inspect_act_cycle_focus,
                )),
        );

        // Build the genuine inspect→act view for the viewer (the cockpit acts as the
        // focused cell itself — the highest authority over its own window).
        let ia = InspectAct::build(
            &w,
            InspectFocus::Cell(focus),
            focus,
            dregg_cell::AuthRequired::Either,
        );
        if let Some(insp) = &ia.inspectable {
            col = col.child(section_title("inspected state"));
            col = col.child(inspectable_row(insp));
        }
        col = col.child(section_title("messages understood"));
        if ia.messages.is_empty() {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("(no messages)"),
            );
        }
        for m in &ia.messages {
            let name = m.name.clone();
            let (badge, badge_color) = if m.authorized {
                ("you may send", theme::good())
            } else {
                ("refused: insufficient authority", theme::bad())
            };
            let id = SharedString::from(format!("ia-send-{name}"));
            let row = div()
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
                        .flex_col()
                        .child(
                            div()
                                .text_xs()
                                .text_color(theme::text())
                                .child(format!("⟶ {} · {}", m.name, m.effect)),
                        )
                        .child(
                            div()
                                .text_xs()
                                .text_color(theme::muted())
                                .child(format!("requires {:?}", m.required)),
                        ),
                )
                .child(
                    div()
                        .flex()
                        .items_center()
                        .gap_1()
                        .child(pill(badge, badge_color))
                        .when(m.authorized, |d| {
                            let send_name = name.clone();
                            d.child(Button::new(id).label("send").primary().xsmall().on_click(
                                cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
                                    this.inspect_act_send(&send_name, cx);
                                }),
                            ))
                        }),
                );
            col = col.child(row);
        }
        if let Some(b) = &self.inspect_act_outcome {
            let color = if b.contains("REFUSED") {
                theme::bad()
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
        col.into_any_element()
    }

    // =======================================================================
    // THE WORKSPACE panel — doIt / printIt / inspectIt.
    // =======================================================================

    /// THE WORKSPACE — compose an intent, evaluate it in a forked throwaway world
    /// (doIt = predict, never mutate), print the predicted receipt (printIt), inspect
    /// the predicted post-state as live objects (inspectIt), then commit-or-discard.
    pub(crate) fn workspace_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let cells = &self.cells;
        let target = cells
            .get(self.workspace_target_idx)
            .copied()
            .unwrap_or(self.workspace.draft().agent);
        let mut col = div()
            .id("cockpit-scroll-body-4")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title("WORKSPACE · doIt · printIt · inspectIt"));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The live evaluator: compose an expression (a turn), doIt to evaluate it in a \
             FORKED throwaway world (predict, never mutate), printIt to echo the predicted \
             receipt, inspectIt to browse the predicted post-state as live objects, then \
             commit-for-real or discard. The live image is untouched until commit.",
        ));

        // the expression composer.
        let agent_short = reflect::short_hex(&self.workspace.draft().agent.0);
        let n_actions = self.workspace.draft().actions.len();
        let n_effects = self.workspace.draft().effect_count();
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(format!("agent {agent_short} ·")),
                )
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child("transfer 100 →"),
                )
                .child(cycle_chip(
                    cx,
                    "ws-target",
                    format!("⬡ {} (cycle)", reflect::short_hex(&target.0)),
                    theme::good(),
                    Cockpit::workspace_cycle_target,
                ))
                .child(small_button(
                    cx,
                    "ws-add",
                    "+ add transfer",
                    theme::good(),
                    Cockpit::workspace_add_transfer,
                ))
                .child(small_button(
                    cx,
                    "ws-clear",
                    "clear",
                    theme::muted(),
                    Cockpit::workspace_clear,
                )),
        );
        col = col.child(
            div()
                .flex()
                .gap_1()
                .child(pill(format!("{n_actions} action(s)"), theme::accent()))
                .child(pill(format!("{n_effects} effect(s)"), theme::accent())),
        );

        // the doIt / commit / discard verbs.
        let can_commit = self.workspace.can_commit();
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(small_button(
                    cx,
                    "ws-doit",
                    "▶ doIt (evaluate)",
                    theme::accent(),
                    Cockpit::workspace_do_it,
                ))
                .child({
                    let (label, color) = if can_commit {
                        ("✓ commit for real", theme::good())
                    } else {
                        ("✓ commit (doIt first)", theme::muted())
                    };
                    small_button(cx, "ws-commit", label, color, Cockpit::workspace_commit)
                })
                .child(small_button(
                    cx,
                    "ws-discard",
                    "discard",
                    theme::muted(),
                    Cockpit::workspace_discard,
                )),
        );

        // printIt + inspectIt.
        if let Some(eval) = self.workspace.last() {
            let printed = eval.print_it();
            let color = if printed.contains("REFUSED") {
                theme::bad()
            } else {
                theme::good()
            };
            col = col.child(section_title("printIt"));
            col = col.child(
                div()
                    .p_2()
                    .rounded_md()
                    .bg(theme::panel())
                    .text_xs()
                    .text_color(color)
                    .child(printed),
            );
            let inspected = eval.inspect_it();
            if !inspected.is_empty() {
                col = col.child(section_title("inspectIt · predicted post-state"));
                let mut ibox = div().flex().flex_col().gap_1();
                for ins in inspected.iter().take(8) {
                    ibox = ibox.child(inspectable_row(ins));
                }
                col = col.child(ibox);
            }
        } else {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("(no evaluation yet — press ▶ doIt)"),
            );
        }
        if let Some(b) = &self.lane_outcome {
            // shared commit banner reuse is avoided; the workspace uses its own echo above.
            let _ = b;
        }
        col.into_any_element()
    }

    // =======================================================================
    // THE WONDER ROOM panel — the AOL glowing-cell room.
    // =======================================================================

    /// THE WONDER ROOM — the AOL-wonder front door: every cell a pokeable glowing
    /// object (glow = real recent activity), with the direct-manipulation halo ring.
    pub(crate) fn wonder_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let w = self.world.borrow();
        let room = WonderRoom::build(&w);
        let mut col = div()
            .id("cockpit-scroll-body-5")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title(
            "WONDER · every cell a glowing pokeable object",
        ));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The AOL-wonder front door: click around, absorb, no comprehension needed. Every \
             cell GLOWS with its real recent activity; each carries the universal halo \
             (inspect · grab · explain). A brighter cell did more, lately.",
        ));

        // the glowing-cell grid.
        let mut grid = div().flex().flex_wrap().gap_2().mt_1();
        for id in &self.cells {
            let Some(gc) = room.cell(id) else { continue };
            let glowing = gc.is_glowing();
            let (border, text) = if glowing {
                (theme::accent(), theme::text())
            } else {
                (theme::border(), theme::muted())
            };
            let cell_id = *id;
            let dom = SharedString::from(format!("wonder-{}", reflect::short_hex(id.as_bytes())));
            grid = grid.child(
                div()
                    .id(dom)
                    .flex()
                    .flex_col()
                    .items_center()
                    .gap_0p5()
                    .px_3()
                    .py_2()
                    .rounded_md()
                    .bg(theme::panel())
                    .border_1()
                    .border_color(border)
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::panel_hi()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            // poke = inspect: re-focus the moldable inspector on it
                            // (a witnessed re-aim of the inspector's own view cell).
                            this.inspector_reflexive = false;
                            this.tab = Tab::Moldable;
                            this.moldable_refocus(Some(cell_id), cx);
                        }),
                    )
                    .child(
                        div()
                            .text_lg()
                            .text_color(if glowing {
                                theme::accent()
                            } else {
                                theme::muted()
                            })
                            .child(if glowing { "✦" } else { "○" }),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(text)
                            .child(reflect::short_hex(id.as_bytes())),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(if glowing { "glowing" } else { "quiet" }),
                    ),
            );
        }
        col = col.child(grid);

        // explain the brightest cell (a plain-sentence "what just happened here").
        if let Some(bright) = room.brightest() {
            if let Some(sentence) = room.explain(&bright.cell) {
                col = col.child(section_title("the brightest cell explains itself"));
                col = col.child(
                    div()
                        .p_2()
                        .rounded_md()
                        .bg(theme::panel())
                        .text_xs()
                        .text_color(theme::text())
                        .child(sentence),
                );
            }
        }
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mt_1()
                .child("(click a cell to inspect it in the moldable INSPECTOR)"),
        );
        col.into_any_element()
    }

    // =======================================================================
    // THE LANES panel — the gadget surfaces (validate→predict→commit / build).
    // =======================================================================

    /// THE LANES — the moldable-inspector gadgets made reachable: the predicate
    /// composer, the turn builder, the attenuation dial, and the macaroon token loop.
    /// Each drives its REAL model methods; a refusal is surfaced as a feature.
    pub(crate) fn lanes_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let mut col = div()
            .id("cockpit-scroll-body-6")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title(
            "LANES · the moldable gadgets (validate → predict → commit)",
        ));
        // the lane selector.
        let names = [
            "predicate composer",
            "turn builder",
            "attenuation dial",
            "token loop",
        ];
        let mut strip = div().flex().flex_wrap().gap_1();
        for (i, name) in names.iter().enumerate() {
            let active = i == self.lane_idx;
            let id = SharedString::from(format!("lane-sel-{i}"));
            strip = strip.child(
                Button::new(id)
                    .label(*name)
                    .ghost()
                    .xsmall()
                    .selected(active)
                    .on_click(cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
                        this.lane_idx = i;
                        this.lane_outcome = None;
                        cx.notify();
                    })),
            );
        }
        col = col.child(strip);

        col = col.child(match self.lane_idx {
            0 => self.lane_predicate(cx),
            1 => self.lane_turn(cx),
            2 => self.lane_cap(cx),
            _ => self.lane_token(cx),
        });

        if let Some(b) = &self.lane_outcome {
            let color = if b.contains("REFUSED") || b.contains("DENIED") || b.contains("incomplete")
            {
                theme::bad()
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
        col.into_any_element()
    }

    /// LANE 0 — the predicate composer (the caveat-language gadget). Drives the REAL
    /// `validate`/`build`, showing the live fail-closed verdict + the source prose +
    /// cost class. A vacuous/strippable caveat is REFUSED (surfaced as a feature).
    pub(crate) fn lane_predicate(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let validation = predicate_composer::validate(&self.lane_composite);
        let mut col = div().flex().flex_col().gap_1().mt_1();
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Compose a predicate caveat from real atoms; validate() runs the genuine \
             non-vacuity / anti-strip / cost check; build() lowers to the protocol \
             StateConstraint. A vacuous or proof-strippable caveat is refused.",
        ));
        // a few pickable atoms — each replaces the composite (a Leaf) and re-validates.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(div().text_xs().text_color(theme::muted()).child("atom:"))
                .child(cycle_chip(
                    cx,
                    "lp-bgte",
                    "balance ≥ 100".into(),
                    theme::accent(),
                    |this, cx| {
                        this.lane_composite = Composite::Leaf(Atom::BalanceGte { min: 100 });
                        this.lane_outcome = None;
                        cx.notify();
                    },
                ))
                .child(cycle_chip(
                    cx,
                    "lp-blte",
                    "balance ≤ 1000".into(),
                    theme::accent(),
                    |this, cx| {
                        this.lane_composite = Composite::Leaf(Atom::BalanceLte { max: 1000 });
                        this.lane_outcome = None;
                        cx.notify();
                    },
                ))
                .child(cycle_chip(
                    cx,
                    "lp-feq",
                    "slot 0 = 7".into(),
                    theme::accent(),
                    |this, cx| {
                        this.lane_composite =
                            Composite::Leaf(Atom::FieldEquals { index: 0, value: 7 });
                        this.lane_outcome = None;
                        cx.notify();
                    },
                ))
                .child(cycle_chip(
                    cx,
                    "lp-empty",
                    "∅ AnyOf (vacuous!)".into(),
                    theme::warn(),
                    |this, cx| {
                        this.lane_composite = Composite::AnyOf(vec![]);
                        this.lane_outcome = None;
                        cx.notify();
                    },
                )),
        );
        // the live verdict.
        let composer = PredicateComposer::new(
            self.anchors[0],
            self.anchors[0],
            self.lane_composite.clone(),
        );
        let (vtext, vcolor) = match composer.build() {
            Ok(c) => (format!("✓ buildable · lowers to {c:?}"), theme::good()),
            Err(e) => (format!("REFUSED · {e:?}"), theme::bad()),
        };
        col = col.child(
            div()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .text_xs()
                .text_color(vcolor)
                .child(vtext),
        );
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .child(format!("validate(): {validation:?}")),
        );
        // the source prose (the "what-is" face).
        if let Ok(c) = composer.build() {
            let refl = predicate_composer::ReflectedConstraint::new(c);
            col = col.child(section_title("source"));
            col = col.child(
                div()
                    .p_2()
                    .rounded_md()
                    .bg(theme::panel())
                    .text_xs()
                    .text_color(theme::text())
                    .child(refl.source_prose()),
            );
            col = col.child(Self::render_presentation_body(&PresentationBody::Trace(
                refl.trace(),
            )));
        }
        col.into_any_element()
    }

    /// LANE 1 — the committing turn builder. Drives the REAL `validate`/`predict`,
    /// showing the live fail-closed verdict + the predicted outcome (no commit here —
    /// the SIMULATE/COMPOSER tabs commit; this lane demonstrates the gadget shape).
    pub(crate) fn lane_turn(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1().mt_1();
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The committing turn gadget: build a call-forest, validate() the well-formedness \
             floor, then predict() its consequences in a fork (the same IntentDraft → simulate \
             spine). An empty/malformed turn cannot build.",
        ));
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(div().text_xs().text_color(theme::muted()).child("agent:"))
                .child(pill(
                    reflect::short_hex(&self.lane_turn.agent_cell().0),
                    theme::accent(),
                ))
                .child(small_button(
                    cx,
                    "lt-add",
                    "+ add transfer action",
                    theme::good(),
                    Cockpit::lane_turn_add,
                ))
                .child(small_button(
                    cx,
                    "lt-clear",
                    "clear",
                    theme::muted(),
                    Cockpit::lane_turn_clear,
                )),
        );
        col = col.child(
            div()
                .flex()
                .gap_1()
                .child(pill(
                    format!("{} action(s)", self.lane_turn.draft().actions.len()),
                    theme::accent(),
                ))
                .child(pill(
                    format!("{} effect(s)", self.lane_turn.effect_count()),
                    theme::accent(),
                )),
        );
        // the live validate() + predict().
        let (vtext, vcolor) = match self.lane_turn.validate() {
            starbridge_v2::GadgetValidation::Ok => ("✓ validate(): Ok".to_string(), theme::good()),
            starbridge_v2::GadgetValidation::Invalid { reason } => {
                (format!("REFUSED · {reason}"), theme::bad())
            }
        };
        col = col.child(
            div()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .text_xs()
                .text_color(vcolor)
                .child(vtext),
        );
        col = col.child(section_title("predict()"));
        let predicted = starbridge_v2::turn_builder::render_prediction(&self.lane_turn, &w);
        col = col.child(
            div()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .text_xs()
                .text_color(theme::text())
                .child(predicted),
        );
        col.into_any_element()
    }

    /// LANE 2 — the attenuation dial (the cap-attenuation value gadget). Drives the
    /// REAL `is_attenuation` check; an amplifying designation is REFUSED.
    pub(crate) fn lane_cap(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let mut col = div().flex().flex_col().gap_1().mt_1();
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The attenuation dial: pick a narrower rights tier; the dial's build() runs the \
             REAL is_attenuation lattice check, refusing any tier that would AMPLIFY the held \
             ceiling. Granting mints a real attenuated cap through the powerbox.",
        ));
        let Some(dial) = &self.lane_dial else {
            return col
                .child(div().text_xs().text_color(theme::warn()).child(
                    "(the cockpit principal holds no firmament cap to attenuate — the lane is honest about the absence)",
                ))
                .into_any_element();
        };
        col = col.child(
            div().flex().flex_wrap().gap_1().items_center().child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(format!("ceiling {:?} · designate:", dial.ceiling())),
            ),
        );
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(cycle_chip(
                    cx,
                    "lc-sig",
                    "Signature".into(),
                    theme::accent(),
                    |this, cx| {
                        this.lane_dial_set("Signature", cx);
                    },
                ))
                .child(cycle_chip(
                    cx,
                    "lc-proof",
                    "Proof".into(),
                    theme::accent(),
                    |this, cx| {
                        this.lane_dial_set("Proof", cx);
                    },
                ))
                .child(cycle_chip(
                    cx,
                    "lc-imposs",
                    "Impossible (narrowest)".into(),
                    theme::accent(),
                    |this, cx| {
                        this.lane_dial_set("Impossible", cx);
                    },
                ))
                .child(cycle_chip(
                    cx,
                    "lc-none",
                    "None (amplify! refused)".into(),
                    theme::warn(),
                    |this, cx| {
                        this.lane_dial_set("None", cx);
                    },
                )),
        );
        let (vtext, vcolor) = match dial.build() {
            Ok(c) => (
                format!("✓ buildable attenuated cap · rights {:?}", c.rights),
                theme::good(),
            ),
            Err(e) => (format!("REFUSED · {e:?}"), theme::bad()),
        };
        col = col.child(
            div()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .text_xs()
                .text_color(vcolor)
                .child(vtext),
        );
        col.into_any_element()
    }

    /// LANE 3 — the macaroon token loop (a verifier gadget). build() runs the REAL
    /// mint → attenuate → delegate → discharge crypto end-to-end + returns the verdict.
    pub(crate) fn lane_token(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let mut col = div().flex().flex_col().gap_1().mt_1();
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The macaroon loop: mint a root token, attenuate (confine to a service/action), \
             delegate, and DISCHARGE service-side — build() runs the REAL cipherclerk crypto \
             (HMAC chain + caveat evaluation) and returns the live verdict.",
        ));
        col = col.child(div().flex().gap_1().child(small_button(
            cx,
            "ltok-run",
            "▶ run the loop (build)",
            theme::accent(),
            Cockpit::lane_token_run,
        )));
        col.into_any_element()
    }

    // =======================================================================
    // THE ⤳ SHARE panel — the FRUSTUM / SNAPSHOT EDITOR (the share-with-attenuation
    // surface): cull the frustum · pare the authority · verify live · share.
    // =======================================================================

    /// THE ⤳ SHARE surface — sculpt a UI-slice snapshot of the focused view, pare
    /// its authority (the REAL [`AttenuationDial`] over `is_attenuation`), watch the
    /// membrane-projected per-viewer preview live, then mint a revocable, attenuated,
    /// rehydratable artifact. The GitHub-org-settings cap UX over the sound substrate
    /// (`docs/desktop-os-research/REHYDRATABLE-SURFACES.md`). gpui-free model below.
    pub(crate) fn share_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let mut col = div()
            .id("cockpit-scroll-body-7")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title(
            "⤳ SHARE · sculpt → pare → verify → extend a revocable attenuated right to re-view",
        ));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "\"Sharing a screenshot\" becomes \"extending a revocable, attenuated, audited \
             right to re-view a witnessed slice.\" CULL the frustum (which lenses / \
             sub-objects are in the slice — visibility) · PARE the authority (the role, \
             on the REAL attenuation lattice — a widening is REFUSED in-band) · VERIFY \
             live (the membrane projects what each recipient would actually see) · SHARE.",
        ));

        let Some(editor) = &self.share_editor else {
            // No editor yet — the call-to-action: capture the focused view.
            let focus = self
                .inspector_view
                .doc()
                .focus()
                .or_else(|| self.cells.first().copied());
            let focus_label = focus
                .map(|c| reflect::short_hex(c.as_bytes()))
                .unwrap_or_else(|| "(no focus)".to_string());
            return col
                .child(
                    div()
                        .mt_2()
                        .text_xs()
                        .text_color(theme::text())
                        .child(format!(
                    "focused object: {focus_label} — capture this view to open the share editor."
                )),
                )
                .child(div().mt_1().child(small_button(
                    cx,
                    "share-capture",
                    "📸 capture this view (open the editor)",
                    theme::accent(),
                    Cockpit::share_capture,
                )))
                .into_any_element();
        };

        // ── the captured snapshot header (focus + lens + the witness cursor) ──
        let snap = editor.snapshot();
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child("captured slice:"),
                )
                .child(pill(
                    format!("focus {}", reflect::short_hex(snap.focus.cell().as_bytes())),
                    theme::accent(),
                ))
                .child(pill(format!("lens {}", snap.kind.slug()), theme::accent()))
                .child(pill(
                    format!("@ height {}", snap.cursor.height),
                    theme::muted(),
                ))
                .child(small_button(
                    cx,
                    "share-recapture",
                    "↺ recapture focus",
                    theme::muted(),
                    Cockpit::share_capture,
                )),
        );

        // ── 1. CULL THE FRUSTUM (visibility) ─────────────────────────────────
        col = col.child(section_title(
            "1 · cull the frustum (visibility — what's in the slice)",
        ));
        // lens toggles.
        let mut lens_row = div()
            .flex()
            .flex_wrap()
            .gap_1()
            .items_center()
            .child(div().text_xs().text_color(theme::muted()).child("lenses:"));
        for lens in starbridge_v2::snapshot_editor::ALL_LENSES {
            let inside = editor.frustum().has_lens(lens);
            let id = SharedString::from(format!("share-lens-{}", lens.slug()));
            let slug = lens.slug().to_string();
            lens_row = lens_row.child(
                div()
                    .id(id)
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if inside {
                        theme::panel_hi()
                    } else {
                        theme::panel()
                    })
                    .text_xs()
                    .text_color(if inside {
                        theme::good()
                    } else {
                        theme::muted()
                    })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| this.share_cull_lens(&slug, cx)),
                    )
                    .child(format!(
                        "{} {}",
                        if inside { "✓" } else { "○" },
                        lens.slug()
                    )),
            );
        }
        col = col.child(lens_row);
        // affordance (sub-object) toggles.
        let mut aff_row = div().flex().flex_wrap().gap_1().items_center().child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .child("sub-objects:"),
        );
        for name in editor.frustum().captured_affordances() {
            let inside = editor.frustum().has_affordance(name);
            let id = SharedString::from(format!("share-aff-{name}"));
            let nm = name.clone();
            aff_row = aff_row.child(
                div()
                    .id(id)
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if inside {
                        theme::panel_hi()
                    } else {
                        theme::panel()
                    })
                    .text_xs()
                    .text_color(if inside {
                        theme::good()
                    } else {
                        theme::muted()
                    })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| this.share_cull_affordance(&nm, cx)),
                    )
                    .child(format!("{} {name}", if inside { "✓" } else { "○" })),
            );
        }
        col = col.child(aff_row);

        // ── 2. PARE THE AUTHORITY (the role, on the lattice) ─────────────────
        col = col.child(section_title(
            "2 · pare the authority (the recipient's role — attenuation-only)",
        ));
        let mut role_row = div().flex().flex_wrap().gap_1().items_center().child(
            div().text_xs().text_color(theme::muted()).child(format!(
                "held ceiling {:?} · grant the recipient:",
                editor.held().rights()
            )),
        );
        for slug in editor.pare_choices() {
            let id = SharedString::from(format!("share-pare-{slug}"));
            let s = slug.clone();
            // A choice that would amplify the held ceiling is colored as a warning
            // (it will be REFUSED in-band when picked — surfaced, never silent).
            role_row = role_row.child(
                div()
                    .id(id)
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel())
                    .text_xs()
                    .text_color(theme::accent())
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| this.share_pare(&s, cx)),
                    )
                    .child(slug),
            );
        }
        col = col.child(role_row);

        // ── 3. LIVE VERIFICATION (the membrane-projected preview) ────────────
        col = col.child(section_title(
            "3 · verify (the membrane projects what each recipient sees)",
        ));
        let v = editor.verify();
        let (vtext, vcolor) = if v.sound {
            (
                format!(
                    "✓ SOUND attenuation · recipient role {:?} ⊆ held (is_attenuation holds)",
                    v.pared_rights
                ),
                theme::good(),
            )
        } else {
            (
                "✗ NOT a sound attenuation yet — pick a role ⊆ the held ceiling (a widening is refused)".to_string(),
                theme::bad(),
            )
        };
        col = col.child(
            div()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .text_xs()
                .text_color(vcolor)
                .child(vtext),
        );
        // the preview-as toggle (which recipient member we preview).
        let preview_wide = self.share_preview_wide;
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child("preview as:"),
                )
                .child(small_button(
                    cx,
                    "share-preview-toggle",
                    if preview_wide {
                        "a WIDE recipient (Either)"
                    } else {
                        "a NARROW recipient (Signature)"
                    },
                    theme::accent(),
                    Cockpit::share_toggle_preview,
                )),
        );
        // the genuine membrane-projected preview for the chosen recipient tier.
        let preview = self.share_recipient_preview(editor);
        let lens_names: Vec<String> = v
            .recipient_lenses
            .iter()
            .map(|l| l.slug().to_string())
            .collect();
        col = col.child(
            div()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .flex()
                .flex_col()
                .gap_0p5()
                .child(div().text_xs().text_color(theme::muted()).child(format!(
                    "this recipient would SEE — lenses: [{}]",
                    lens_names.join(", ")
                )))
                .child(div().text_xs().text_color(theme::text()).child(format!(
                    "affordances (membrane-projected through is_attenuation, frustum-confined): [{}]",
                    if preview.is_empty() { "(nothing)".to_string() } else { preview.join(", ") }
                ))),
        );

        // ── 4. SHARE (mint the revocable artifact) ───────────────────────────
        col = col.child(section_title(
            "4 · share (extend the revocable, attenuated, audited right)",
        ));
        col = col.child(div().child(small_button(
            cx,
            "share-mint",
            "⤳ share this slice (mint the revocable artifact)",
            if v.sound {
                theme::good()
            } else {
                theme::muted()
            },
            Cockpit::share_mint,
        )));

        if let Some(b) = &self.share_outcome {
            let color = if b.contains("REFUSED") || b.contains("amplif") || b.contains("AMPLIFY") {
                theme::bad()
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

        // ── the audit trail of minted artifacts (members of the org) ─────────
        if !self.share_artifacts.is_empty() {
            col = col.child(section_title(
                "shared artifacts (the audit trail — revocable per recipient)",
            ));
            let mut list = div().flex().flex_col().gap_1();
            for (i, art) in self.share_artifacts.iter().enumerate() {
                let live = art.is_live();
                let id = SharedString::from(format!("share-revoke-{i}"));
                let mut row = div()
                    .flex()
                    .flex_wrap()
                    .items_center()
                    .gap_1()
                    .p_1()
                    .rounded_md()
                    .bg(theme::panel())
                    .child(pill(
                        format!(
                            "slice → {} · role {:?}",
                            reflect::short_hex(art.backing.as_bytes()),
                            art.attenuated_rights
                        ),
                        if live {
                            theme::accent()
                        } else {
                            theme::muted()
                        },
                    ))
                    .child(pill(
                        format!(
                            "{} sub-object(s)",
                            art.affordance_scope.affordance_names.len()
                        ),
                        theme::muted(),
                    ))
                    .child(pill(
                        if live { "LIVE" } else { "REVOKED" }.to_string(),
                        if live { theme::good() } else { theme::bad() },
                    ));
                if live {
                    row = row.child(
                        div()
                            .id(id)
                            .px_2()
                            .py_0p5()
                            .rounded_md()
                            .bg(theme::panel_hi())
                            .text_xs()
                            .text_color(theme::bad())
                            .cursor_pointer()
                            .hover(|s| s.bg(theme::border()))
                            .on_mouse_down(
                                MouseButton::Left,
                                cx.listener(move |this, _ev, _w, cx| this.share_revoke(i, cx)),
                            )
                            .child("⊘ revoke"),
                    );
                }
                list = list.child(row);
            }
            col = col.child(list);
        }

        col.into_any_element()
    }

    /// Build a real native [`AffordanceSurface`] over `cell` — the four-tier shape
    /// (view / comment / edit / admin) that genuinely exercises the membrane
    /// (`is_attenuation` divides them per recipient). Each affordance fires a REAL
    /// `dregg_turn::Effect`; the surface is the witness-graph the membrane projects
    /// through. The same htmx-on-crack shape `web_cells` publishes, native here.
    pub(crate) fn share_surface_for(cell: CellId) -> AffordanceSurface {
        use dregg_cell::AuthRequired;
        use dregg_turn::action::{Effect, Event};
        AffordanceSurface::new(cell)
            .declare(CellAffordance::new(
                "view",
                AuthRequired::Signature, // tier-1: any signer
                Effect::EmitEvent {
                    cell,
                    event: Event::new([1u8; 32], vec![]),
                },
            ))
            .declare(CellAffordance::new(
                "comment",
                AuthRequired::Either, // tier-2: the editor tier
                Effect::EmitEvent {
                    cell,
                    event: Event::new([2u8; 32], vec![]),
                },
            ))
            .declare(CellAffordance::new(
                "edit",
                AuthRequired::Either, // tier-2: a real SetField write
                Effect::SetField {
                    cell,
                    index: 1,
                    value: [7u8; 32],
                },
            ))
            .declare(CellAffordance::new(
                "admin",
                AuthRequired::None, // tier-3: only the root holder clears it
                Effect::IncrementNonce { cell },
            ))
    }

    /// The membrane-projected preview for the chosen recipient tier — the REAL
    /// per-viewer slice (`AffordanceSnapshot::rehydrate_for` through `is_attenuation`,
    /// frustum-confined). The preview-as toggle picks WIDE (Either) vs NARROW
    /// (Signature) — the two members the org-settings page lets you "view as".
    pub(crate) fn share_recipient_preview(&self, editor: &SnapshotEditor) -> Vec<String> {
        let backing = editor.snapshot().focus.cell();
        let rights = if self.share_preview_wide {
            dregg_cell::AuthRequired::Either
        } else {
            dregg_cell::AuthRequired::Signature
        };
        let recipient = recipient_window_cap(SurfaceId(0xA1), backing, rights);
        editor.preview_for(&recipient)
    }

    // =======================================================================
    // THE HANDLERS — the `&mut Cockpit` verbs the new panels' buttons call. Each
    // drives a REAL model method; a refusal is captured into the panel's banner.
    // =======================================================================

    /// ⤳ CAPTURE — pause the camera on the focused view and OPEN the share editor.
    /// Takes a REAL [`UiSnapshot`] of the focused cell at the live head, builds the
    /// native four-tier affordance surface, and mints a held window cap over it (the
    /// attenuation ceiling). Re-captures fresh so the editor tracks the live focus.
    pub(crate) fn share_capture(&mut self, cx: &mut Context<Self>) {
        let world = self.world.borrow();
        let Some(focus) = self
            .inspector_view
            .doc()
            .focus()
            .or_else(|| self.cells.first().copied())
        else {
            self.share_outcome = Some("REFUSED · no focused cell to capture".to_string());
            drop(world);
            cx.notify();
            return;
        };
        // The captured snapshot — the inspector's own paused camera (we carry it).
        let snap = UiSnapshot::capture(
            &world,
            FocusTarget::Cell(focus),
            PresentationKind::Affordances,
        );
        drop(world);
        let surface = Self::share_surface_for(focus);
        // The held window cap = the ceiling. The cockpit principal holds the broad
        // root tier over the focused surface (it is the operator); the pare narrows
        // from there. (A narrower honest ceiling would only restrict the dial more.)
        let held = recipient_window_cap(SurfaceId(0xA1), focus, dregg_cell::AuthRequired::None);
        let n_aff = surface.all_names().len();
        self.share_editor = Some(SnapshotEditor::open(snap, surface, held));
        self.share_outcome = Some(format!(
            "captured the focused view ({}) — {n_aff} sub-object(s), every lens, the full slice. Now cull + pare.",
            reflect::short_hex(focus.as_bytes())
        ));
        cx.notify();
    }

    /// Cull a presentation LENS in/out of the shared slice (visibility).
    pub(crate) fn share_cull_lens(&mut self, slug: &str, cx: &mut Context<Self>) {
        if let Some(ed) = &mut self.share_editor {
            if let Some(lens) = starbridge_v2::snapshot_editor::ALL_LENSES
                .into_iter()
                .find(|l| l.slug() == slug)
            {
                let inside = ed.cull_lens(lens);
                self.share_outcome = Some(format!(
                    "lens `{slug}` {} the shared slice",
                    if inside {
                        "→ added back to"
                    } else {
                        "← culled OUT of"
                    }
                ));
            }
        }
        cx.notify();
    }

    /// Cull an affordance SUB-OBJECT in/out of the shared slice (visibility).
    pub(crate) fn share_cull_affordance(&mut self, name: &str, cx: &mut Context<Self>) {
        if let Some(ed) = &mut self.share_editor {
            let inside = ed.cull_affordance(name);
            self.share_outcome = Some(format!(
                "sub-object `{name}` {} the shared slice",
                if inside {
                    "→ added back to"
                } else {
                    "← culled OUT of"
                }
            ));
        }
        cx.notify();
    }

    /// PARE the authority to a rights tier — the REAL [`AttenuationDial`]. An
    /// amplifying choice is REFUSED in-band (fail-closed), surfaced in the banner.
    pub(crate) fn share_pare(&mut self, slug: &str, cx: &mut Context<Self>) {
        if let Some(ed) = &mut self.share_editor {
            self.share_outcome = Some(match ed.pare_to(slug) {
                PareOutcome::Pared { rights } => {
                    format!("pared the recipient role to {rights:?} (a sound attenuation ⊆ held)")
                }
                PareOutcome::Refused { reason } => format!("REFUSED · {reason}"),
            });
        }
        cx.notify();
    }

    /// Toggle the recipient preview tier (WIDE Either ↔ NARROW Signature).
    pub(crate) fn share_toggle_preview(&mut self, cx: &mut Context<Self>) {
        self.share_preview_wide = !self.share_preview_wide;
        cx.notify();
    }

    /// ⤳ SHARE — mint the revocable, attenuated, rehydratable artifact. The
    /// no-amplification gate is IN-BAND: an over-wide / incomplete pare is REFUSED
    /// (you cannot mint an over-wide artifact through this editor).
    pub(crate) fn share_mint(&mut self, cx: &mut Context<Self>) {
        if let Some(ed) = &self.share_editor {
            match ed.share() {
                Ok(artifact) => {
                    let role = artifact.attenuated_rights.clone();
                    let n = artifact.affordance_scope.affordance_names.len();
                    self.share_artifacts.push(artifact);
                    self.share_outcome = Some(format!(
                        "⤳ shared · minted a revocable artifact (role {role:?}, {n} sub-object(s)). \
                         The recipient gets a re-runnable camera + an attenuated cap — not your session."
                    ));
                }
                Err(ShareError::PareIncomplete) => {
                    self.share_outcome = Some(
                        "REFUSED · pick a recipient role first (the pare is incomplete — fail-closed)".to_string(),
                    );
                }
                Err(ShareError::WouldAmplify { held, pared }) => {
                    self.share_outcome = Some(format!(
                        "REFUSED · role {pared:?} would AMPLIFY the held {held:?} — \
                         you cannot share more than you hold (is_attenuation refused it)"
                    ));
                }
            }
        }
        cx.notify();
    }

    /// ⊘ REVOKE a shared artifact — withdraw the right to re-view (org "remove
    /// member"). The membrane re-checks authority at each reacquisition, so a revoked
    /// artifact rehydrates NOTHING thereafter, regardless of caps held.
    pub(crate) fn share_revoke(&mut self, idx: usize, cx: &mut Context<Self>) {
        if let Some(art) = self.share_artifacts.get_mut(idx) {
            art.revoke();
            self.share_outcome = Some(format!(
                "⊘ revoked artifact #{idx} — the right to re-view is withdrawn (rehydrates nothing now)"
            ));
        }
        cx.notify();
    }

    pub(crate) fn moldable_clear_query(&mut self, cx: &mut Context<Self>) {
        self.moldable_query.clear();
        cx.notify();
    }

    /// Cycle the moldable inspector's LENS FAMILY (the L4–L10 reach). Resets the
    /// present-idx to the new lens's first presentation so the tab-strip lands on
    /// a valid sub-tab; the witnessed camera-aim catches up on the next re-aim.
    pub(crate) fn moldable_cycle_lens(&mut self, cx: &mut Context<Self>) {
        self.moldable_lens = self.moldable_lens.next();
        self.inspector_view.doc_mut().set_present_idx(0);
        let _ = self.inspector_view.commit(&mut self.world.borrow_mut());
        cx.notify();
    }

    pub(crate) fn moldable_cycle_focus(&mut self, cx: &mut Context<Self>) {
        let cells = &self.cells;
        if cells.is_empty() {
            return;
        }
        let cur = self
            .inspector_view
            .doc()
            .focus()
            .and_then(|f| cells.iter().position(|c| *c == f))
            .unwrap_or(0);
        let next = cells[(cur + 1) % cells.len()];
        self.moldable_refocus(Some(next), cx);
    }

    /// M3 — RE-AIM the inspector's camera (a witnessed UI mutation). Re-focus the
    /// FREE in-memory draft (the §3.5 stream weight class: free edit), then land an
    /// occasional witnessed `SetField` commit so the inspector's camera-aim is a
    /// real, rewindable dregg-graph mutation (the BufferCell commit discipline,
    /// generalized). A commit failure leaves the free draft moved (the panel still
    /// reflects the operator's aim); the witnessed state catches up on the next
    /// successful commit.
    pub(crate) fn moldable_refocus(&mut self, focus: Option<CellId>, cx: &mut Context<Self>) {
        self.inspector_view.doc_mut().set_focus(focus);
        let _ = self.inspector_view.commit(&mut self.world.borrow_mut());
        cx.notify();
    }

    /// M3 — open presentation `idx` (a tab-strip click). Re-aim the free draft's
    /// lens, then witness it with an occasional commit (the same discipline as a
    /// re-focus).
    pub(crate) fn moldable_set_present_idx(&mut self, idx: usize, cx: &mut Context<Self>) {
        self.inspector_view.doc_mut().set_present_idx(idx);
        let _ = self.inspector_view.commit(&mut self.world.borrow_mut());
        cx.notify();
    }

    /// M3 — toggle the inspector ON ITSELF (inspect the inspector). When on, the
    /// panel focuses [`FocusTarget::ViewCell`] on the inspector's own backing cell —
    /// the reflexive loop through the SAME `Registry::present` dispatch.
    pub(crate) fn moldable_toggle_reflexive(&mut self, cx: &mut Context<Self>) {
        self.inspector_reflexive = !self.inspector_reflexive;
        cx.notify();
    }

    /// Reveal/hide the DEEP native moldable presentation set below the live inspector
    /// card. Default-hidden so the card alone IS the Inspect surface (NOTHING DRAWS
    /// TWICE); this toggle opens the native Registry/Spotter/Halo/RawFields as a
    /// distinct companion face below the card — never an underlay in the same bounds.
    pub(crate) fn moldable_toggle_native(&mut self, cx: &mut Context<Self>) {
        self.moldable_show_native = !self.moldable_show_native;
        cx.notify();
    }

    pub(crate) fn inspect_act_cycle_focus(&mut self, cx: &mut Context<Self>) {
        let cells = &self.cells;
        if cells.is_empty() {
            return;
        }
        let cur = self
            .inspect_act_focus
            .and_then(|f| cells.iter().position(|c| *c == f))
            .unwrap_or(0);
        self.inspect_act_focus = Some(cells[(cur + 1) % cells.len()]);
        self.inspect_act_outcome = None;
        cx.notify();
    }

    /// SEND a message through the REAL inspect→act loop (a verified turn), capturing
    /// the executor's verdict / the in-band refusal into the banner + refreshing.
    pub(crate) fn inspect_act_send(&mut self, message: &str, cx: &mut Context<Self>) {
        let Some(focus) = self
            .inspect_act_focus
            .or_else(|| self.cells.first().copied())
        else {
            return;
        };
        let result = {
            let mut w = self.world.borrow_mut();
            let ia = InspectAct::build(
                &w,
                InspectFocus::Cell(focus),
                focus,
                dregg_cell::AuthRequired::Either,
            );
            ia.send(&mut w, message, dregg_cell::AuthRequired::Either)
        };
        self.inspect_act_outcome = Some(match result {
            SendResult::Committed { receipt, .. } => format!(
                "committed `{message}` · receipt {} · {} action(s)",
                reflect::short_hex(&receipt.receipt_hash()),
                receipt.action_count
            ),
            SendResult::Refused {
                reason,
                by_executor,
            } => format!(
                "REFUSED `{message}` ({}): {reason}",
                if by_executor { "executor" } else { "cap-gate" }
            ),
        });
        self.refresh_cells();
        cx.notify();
    }

    // =======================================================================
    // THE SERVICE EXPLORER — the Postman-like invoke() surface.
    // =======================================================================

    /// THE SERVICE EXPLORER panel: discover a focused cell's PUBLISHED INTERFACE
    /// (the methods its program dispatches on), pick a method, fill its args, and
    /// INVOKE it as a REAL verified turn (the deos-interior `invoke()` front door).
    pub(crate) fn service_explorer_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let w = self.world.borrow();
        let cells = &self.cells;
        let focus = self
            .service_explorer_focus
            .or_else(|| cells.first().copied());
        let mut col = div()
            .id("cockpit-scroll-body-service")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title(
            "🛰 SERVICES · discover a cell's published methods → invoke",
        ));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The Postman-like face of CELLS-AS-SERVICE-OBJECTS: a focused cell's published \
             interface (the methods its program dispatches on, derived live), each with its \
             arity / authority / replay-vs-serviced semantics + a cap badge. Pick a replayable \
             method, fill its args, and INVOKE it — a REAL verified turn that DESUGARS to an \
             ordinary method-targeting turn (no kernel Effect::Invoke). An unknown / serviced / \
             unauthorized method is refused in-band.",
        ));
        let Some(focus) = focus else {
            return col
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child("(no cells yet)"),
                )
                .into_any_element();
        };

        // The focus chip (cycle through cells).
        col = col.child(
            div()
                .flex()
                .items_center()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).child("focus:"))
                .child(cycle_chip(
                    cx,
                    "service-focus",
                    format!("⬡ {} (cycle)", reflect::short_hex(focus.as_bytes())),
                    theme::good(),
                    Cockpit::service_explorer_cycle_focus,
                )),
        );

        // Build the genuine service-explorer view (the cockpit acts as the cell
        // itself — the highest authority over its own window).
        let se = ServiceExplorer::build(&w, focus, focus, dregg_cell::AuthRequired::Either);

        if let Some(insp) = &se.inspectable {
            col = col.child(section_title("inspected state"));
            col = col.child(inspectable_row(insp));
        }

        col = col.child(section_title(format!(
            "published methods · interface {}",
            reflect::short_hex(&se.interface_id)
        )));
        if se.methods.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "(this cell publishes no methods — its program does not dispatch on a method \
                 symbol. Set a Cases program with MethodIs guards to publish an interface.)",
            ));
        }
        for m in &se.methods {
            let selected = self.service_explorer_selected == Some(m.symbol);
            let (badge, badge_color) = if !m.is_invokable() {
                ("serviced — named seam", theme::muted())
            } else if m.authorized {
                ("you may invoke", theme::good())
            } else {
                ("refused: insufficient authority", theme::bad())
            };
            let sym = m.symbol;
            let pick_id = SharedString::from(format!("svc-pick-{}", reflect::short_hex(&m.symbol)));
            let row = div()
                .flex()
                .justify_between()
                .items_center()
                .px_2()
                .py_0p5()
                .rounded_md()
                .bg(if selected {
                    theme::panel_hi()
                } else {
                    theme::panel()
                })
                .child(
                    div()
                        .flex()
                        .flex_col()
                        .child(
                            div()
                                .text_xs()
                                .text_color(theme::text())
                                .child(format!("ƒ {}", m.name)),
                        )
                        .child(div().text_xs().text_color(theme::muted()).child(format!(
                            "requires {:?} · {} args · {:?}",
                            m.required,
                            m.arity
                                .map(|n| n.to_string())
                                .unwrap_or_else(|| "variadic".to_string()),
                            m.semantics,
                        ))),
                )
                .child(
                    div()
                        .flex()
                        .items_center()
                        .gap_1()
                        .child(pill(badge, badge_color))
                        .when(m.is_invokable(), |d| {
                            d.child(
                                Button::new(pick_id)
                                    .label(if selected { "selected" } else { "select" })
                                    .xsmall()
                                    .outline()
                                    .on_click(cx.listener(
                                        move |this, _ev: &ClickEvent, _w, cx| {
                                            this.service_explorer_select(sym, cx);
                                        },
                                    )),
                            )
                        }),
                );
            col = col.child(row);
        }

        // The args composer (preset buttons — the cockpit's text-entry idiom).
        col = col.child(section_title("arguments"));
        col = col.child(
            div()
                .flex()
                .items_center()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).child("args:"))
                .child(div().text_xs().text_color(theme::text()).child(
                    if self.service_explorer_args.is_empty() {
                        "(none)".to_string()
                    } else {
                        self.service_explorer_args.clone()
                    },
                ))
                .child(arg_preset_btn(cx, "svc-args-none", "clear", ""))
                .child(arg_preset_btn(cx, "svc-args-1", "= 1", "1"))
                .child(arg_preset_btn(cx, "svc-args-7", "= 7", "7"))
                .child(arg_preset_btn(cx, "svc-args-42", "= 1,42", "1,42")),
        );

        // The underlying-effect picker + the INVOKE button. A replayable method
        // desugars to its underlying effects; here the operator picks the body
        // from the same palette the inspect→act surface uses (a real, conserving,
        // observable effect), proving the method-targeting path end-to-end.
        col = col.child(section_title("invoke"));
        let can_invoke = self.service_explorer_selected.is_some();
        col = col.child(
            div()
                .flex()
                .items_center()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).child(
                    match self.service_explorer_selected {
                        Some(s) => format!("selected method {}", reflect::short_hex(&s)),
                        None => "(pick a method above)".to_string(),
                    },
                ))
                .when(can_invoke, |d| {
                    d.child(
                        Button::new(SharedString::from("svc-invoke-nonce"))
                            .label("invoke → touch (IncrementNonce)")
                            .primary()
                            .xsmall()
                            .on_click(cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
                                this.service_explorer_invoke(SvcEffectKind::Nonce, cx);
                            })),
                    )
                    .child(
                        Button::new(SharedString::from("svc-invoke-setfield"))
                            .label("invoke → write slot 1 (SetField)")
                            .xsmall()
                            .outline()
                            .on_click(cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
                                this.service_explorer_invoke(SvcEffectKind::SetField, cx);
                            })),
                    )
                }),
        );

        if let Some(b) = &self.service_explorer_outcome {
            let color = if b.contains("REFUSED") {
                theme::bad()
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
        col.into_any_element()
    }

    /// Cycle the service explorer's focused cell.
    pub(crate) fn service_explorer_cycle_focus(&mut self, cx: &mut Context<Self>) {
        let cells = &self.cells;
        if cells.is_empty() {
            return;
        }
        let cur = self
            .service_explorer_focus
            .and_then(|f| cells.iter().position(|c| *c == f))
            .unwrap_or(0);
        self.service_explorer_focus = Some(cells[(cur + 1) % cells.len()]);
        self.service_explorer_selected = None;
        self.service_explorer_outcome = None;
        cx.notify();
    }

    /// Select a method to invoke (by its symbol).
    pub(crate) fn service_explorer_select(&mut self, symbol: [u8; 32], cx: &mut Context<Self>) {
        self.service_explorer_selected = Some(symbol);
        self.service_explorer_outcome = None;
        cx.notify();
    }

    /// Set the args string (the preset-button entry).
    pub(crate) fn service_explorer_set_args(&mut self, args: &str, cx: &mut Context<Self>) {
        self.service_explorer_args = args.to_string();
        cx.notify();
    }

    /// INVOKE the selected method through the REAL service-explorer loop: parse
    /// the args, build the chosen underlying effect, route+gate+desugar+commit a
    /// real verified turn, and capture the verdict / in-band refusal into the
    /// banner. Closes the loop (the post-state is re-read on the next render).
    pub(crate) fn service_explorer_invoke(
        &mut self,
        effect_kind: SvcEffectKind,
        cx: &mut Context<Self>,
    ) {
        let Some(focus) = self
            .service_explorer_focus
            .or_else(|| self.cells.first().copied())
        else {
            return;
        };
        let Some(symbol) = self.service_explorer_selected else {
            self.service_explorer_outcome =
                Some("REFUSED: pick a method to invoke first".to_string());
            cx.notify();
            return;
        };
        let args = parse_felt_args(&self.service_explorer_args);
        let effects = vec![match effect_kind {
            SvcEffectKind::Nonce => dregg_turn::action::Effect::IncrementNonce { cell: focus },
            SvcEffectKind::SetField => dregg_turn::action::Effect::SetField {
                cell: focus,
                index: 1,
                value: [7u8; 32],
            },
        }];
        let result = {
            let mut w = self.world.borrow_mut();
            let se = ServiceExplorer::build(&w, focus, focus, dregg_cell::AuthRequired::Either);
            se.invoke(
                &mut w,
                symbol,
                args,
                effects,
                dregg_cell::AuthRequired::Either,
            )
        };
        self.service_explorer_outcome = Some(match result {
            InvokeOutcome::Committed { receipt, .. } => format!(
                "invoked {} · receipt {} · {} action(s)",
                reflect::short_hex(&symbol),
                reflect::short_hex(&receipt.receipt_hash()),
                receipt.action_count
            ),
            InvokeOutcome::Refused {
                reason,
                by_executor,
            } => format!(
                "REFUSED invoke {} ({}): {reason}",
                reflect::short_hex(&symbol),
                if by_executor {
                    "executor"
                } else {
                    "front-door"
                }
            ),
        });
        self.refresh_cells();
        cx.notify();
    }

    pub(crate) fn workspace_cycle_target(&mut self, cx: &mut Context<Self>) {
        let n = self.cells.len().max(1);
        self.workspace_target_idx = (self.workspace_target_idx + 1) % n;
        cx.notify();
    }

    pub(crate) fn workspace_add_transfer(&mut self, cx: &mut Context<Self>) {
        let cells = &self.cells;
        let Some(target) = cells.get(self.workspace_target_idx).copied() else {
            return;
        };
        let agent = self.workspace.draft().agent;
        let ai = self.workspace.draft_mut().add_action(agent);
        self.workspace.draft_mut().add_effect(
            ai,
            starbridge_v2::simulate::EffectKind::Transfer {
                to: target,
                amount: 100,
            },
        );
        cx.notify();
    }

    pub(crate) fn workspace_clear(&mut self, cx: &mut Context<Self>) {
        let agent = self.workspace.draft().agent;
        self.workspace = Workspace::new(agent);
        cx.notify();
    }

    pub(crate) fn workspace_do_it(&mut self, cx: &mut Context<Self>) {
        let w = self.world.borrow();
        self.workspace.evaluate(&w);
        cx.notify();
    }

    pub(crate) fn workspace_commit(&mut self, cx: &mut Context<Self>) {
        if !self.workspace.can_commit() {
            return;
        }
        {
            let mut w = self.world.borrow_mut();
            self.workspace.commit(&mut w);
        }
        self.refresh_cells();
        cx.notify();
    }

    pub(crate) fn workspace_discard(&mut self, cx: &mut Context<Self>) {
        self.workspace.discard();
        cx.notify();
    }

    pub(crate) fn lane_turn_add(&mut self, cx: &mut Context<Self>) {
        let agent = self.lane_turn.agent_cell();
        self.lane_turn.action_with(
            agent,
            starbridge_v2::simulate::EffectKind::Transfer {
                to: agent,
                amount: 50,
            },
        );
        cx.notify();
    }

    pub(crate) fn lane_turn_clear(&mut self, cx: &mut Context<Self>) {
        self.lane_turn = CommittingTurnGadget::new(self.lane_turn.agent_cell());
        cx.notify();
    }

    /// Set the attenuation dial's designated tier through the REAL `Gadget::set`
    /// (the same path the form's keystroke drives), then capture build()'s verdict.
    pub(crate) fn lane_dial_set(&mut self, slug: &str, cx: &mut Context<Self>) {
        if let Some(dial) = &mut self.lane_dial {
            dial.set("rights", GadgetInput::Variant(slug.to_string()));
            self.lane_outcome = Some(match dial.build() {
                Ok(c) => format!(
                    "designated {slug} → buildable attenuated cap (rights {:?})",
                    c.rights
                ),
                Err(e) => format!("REFUSED designation {slug}: {e:?}"),
            });
        }
        cx.notify();
    }

    /// RUN the macaroon loop's REAL crypto via the gadget's `build()` (mint →
    /// attenuate → delegate → discharge), capturing the live verdict into the banner.
    pub(crate) fn lane_token_run(&mut self, cx: &mut Context<Self>) {
        self.lane_outcome = Some(match self.lane_token.build() {
            Ok(r) => format!(
                "loop ran · service `{}` mask `{}` · authorizes_own={} denies_wider={} · {} caveat(s) added",
                r.service, r.mask, r.authorizes_own, r.denies_wider, r.caveats_added
            ),
            Err(e) => format!("REFUSED · the loop could not build: {e:?}"),
        });
        cx.notify();
    }
}

/// The within-window "this card is hosted in another pane" placeholder — the one-host
/// invariant's calm second-host surface. A live `CardPane` entity may be hosted at most
/// once per frame; when two split panes both show the same card-tab, the first host wins
/// the live entity and the duplicate shows this (so the SAME entity is never re-entered in
/// one frame — the within-window analogue of [`Cockpit::torn_off_placeholder`]).
#[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
fn mirror_in_another_pane_placeholder(title: &str) -> gpui::AnyElement {
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
                .child(SharedString::from(format!("⧉ {title}"))),
        )
        .child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .child(SharedString::from(
                    "This live card is shown in another pane. A card is one live object; \
                     it paints in exactly one pane per frame. Switch this pane to a \
                     different surface to view both.",
                )),
        )
        .into_any_element()
}

/// Which underlying existing effect a service-explorer invocation desugars to —
/// the body the (replayable) method carries. The operator picks from this small
/// palette (the same real, conserving, observable effects the inspect→act surface
/// fires), so the invocation proves the method-targeting path end-to-end.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SvcEffectKind {
    /// `IncrementNonce` — the minimal observable self-mutation (a "touch").
    Nonce,
    /// `SetField` on slot 1 — a visible state write the re-inspection reflects.
    SetField,
}

/// A small preset button that sets the service explorer's args string (the
/// cockpit's text-entry idiom — canned presets rather than a live text field).
fn arg_preset_btn(
    cx: &mut Context<Cockpit>,
    id: &'static str,
    label: &'static str,
    value: &'static str,
) -> impl IntoElement {
    Button::new(SharedString::from(id))
        .label(label)
        .xsmall()
        .outline()
        .on_click(cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
            this.service_explorer_set_args(value, cx);
        }))
}

/// Parse a comma-separated list of decimal integers into the `args` felt vector
/// an invocation carries. Each integer becomes a little-endian 32-byte field
/// element (the cockpit's small-felt encoding); empty/blank entries are skipped.
/// A non-numeric token is skipped (the surface stays robust to stray input).
fn parse_felt_args(s: &str) -> Vec<[u8; 32]> {
    s.split(',')
        .map(str::trim)
        .filter(|t| !t.is_empty())
        .filter_map(|t| t.parse::<u64>().ok())
        .map(|n| {
            let mut felt = [0u8; 32];
            felt[..8].copy_from_slice(&n.to_le_bytes());
            felt
        })
        .collect()
}
